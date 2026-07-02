(*
Author:  Dohan Kim and René Thiemann
*)

section \<open>Formalization of Parallel Criticial Pairs and their Applications\<close>

text \<open>We define parallel critical pairs and prove Toyama's and Gramlich's parallel critical pair condition,
  generalized for commutation. Moreover, we formalize rule labeling for parallel critical pairs,
  again generalized for commutation. We further support the compositional versions of Shintani and
  Hirokawa.\<close>

theory Parallel_Critical_Pairs
  imports
    First_Order_Rewriting.Trs_Impl (* for rules type *)
    TRS.Mgu_generic
    First_Order_Rewriting.Multihole_Context
    First_Order_Rewriting.Critical_Pairs
    "Decreasing-Diagrams-II.Decreasing_Diagrams_II"
    First_Order_Rewriting.Parallel_Rewriting
    TRS.More_Abstract_Rewriting
    Auxx.Util
    TRS.Renaming_Interpretations
begin  

lift_definition renaming2 :: "'v :: infinite renamingN \<Rightarrow> 'v renaming2" is
  "\<lambda> (r1, r2). (\<lambda> x. r1 (0,x), r2)" 
  apply clarsimp
  apply (intro conjI; (force?))
  using injD inj_on_def by fastforce

subsection \<open>Definition of Parallel Critical Pairs and Peaks\<close>

text \<open>We define parallel critical peaks and pairs by contexts so that no reasoning on positions 
  is required.\<close>

context
  fixes ren :: "'v :: infinite renamingN" 
begin

definition parallel_critical_peaks_of_rule :: "('f,'v)trs \<Rightarrow> ('f,'v) rule \<Rightarrow> (('f,'v)mctxt \<times>
  ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)rules) set" where
  "parallel_critical_peaks_of_rule R lr = (case lr of (l,r) \<Rightarrow>
      {  (C \<cdot>mc \<tau>, fill_holes (C \<cdot>mc \<tau>) (map2 (\<lambda> rl \<sigma>i. snd rl \<cdot> \<sigma>i) rls \<sigma>), l \<cdot> \<tau>, r \<cdot> \<tau>, rls) | C lps rls \<sigma> \<tau>. 
         l =\<^sub>f (C, lps) \<and> 
         hole_poss C \<subseteq> fun_poss l \<and>
         num_holes C \<noteq> 0 \<and> 
         set rls \<subseteq> R \<and> 
         mgu_vd_list ren (map2 (\<lambda> rl lp. (fst rl, lp)) rls lps) = Some (\<sigma>, \<tau>) \<and>
         length rls = num_holes C})"

text \<open>PCPs of two TRSs where we directly omit trivial parallel critical pairs\<close>

definition "parallel_critical_pairs R S =
  {(t,u) | t u s C rls lr. (C,t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr \<and> lr \<in> S \<and> t \<noteq> u}" 

text \<open>We directly omit trivial parallel critical pairs and peaks; moreover for the parallel critical
  peaks we only consider those that arise from non-root overlaps.\<close>
definition nonroot_parallel_cps :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs" where
  "nonroot_parallel_cps R S = { (t,u) | lr C rls s u t. lr \<in> S \<and> (C,t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr \<and> 
      C \<noteq> MHole \<and> t \<noteq> u}" 

definition nonroot_parallel_peaks :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> (('f,'v)mctxt \<times> ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)term)set" where
  "nonroot_parallel_peaks R S = { (C,t,s,u) | lr C t s u rls. lr \<in> S \<and> (C,t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr
   \<and> C \<noteq> MHole \<and> t \<noteq> u}" 


subsection \<open>The Key Lemma: Capturing an Overlap of Parallel- and Root-Step via PCPs\<close>

text \<open>Auxiliary lemma\<close>
lemma rewrite_in_subst: assumes "linear_term l" 
  and "l \<cdot> \<sigma> = C \<langle> s \<rangle>" 
  and "hole_pos C \<notin> fun_poss l" 
  and "ctxt.closed rel" 
  and st: "(s,t) \<in> rel" 
shows "\<exists> \<tau> x. l \<cdot> \<tau> = C \<langle> t \<rangle> \<and> x \<in> vars_term l \<and> (\<sigma> x, \<tau> x) \<in> rel \<and> (\<forall> y. y \<noteq> x \<longrightarrow> \<sigma> y = \<tau> y)" 
  using assms(1-3)
proof (induct l arbitrary: C)
  case (Var x)
  from assms(4-5) have "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rel" by blast
  thus ?case using st Var
    by (intro exI[of _ x] exI[of _ "\<sigma>(x := C\<langle>t\<rangle>)"], auto)
next
  case (Fun f ls)
  then obtain D bef aft where C: "C = More f bef D aft" by (cases C, auto)
  let ?n = "length bef" 
  from Fun(3)[unfolded C] have id_list: "map (\<lambda>t. t \<cdot> \<sigma>) ls = bef @ D\<langle>s\<rangle> # aft" by auto
  from arg_cong[OF id_list, of length] have n: "?n < length ls" by auto
  from arg_cong[OF id_list, of "\<lambda> xs. xs ! ?n"] n
  have id: "ls ! ?n \<cdot> \<sigma> = D\<langle>s\<rangle>" by auto
  from Fun(2) n have lin: "linear_term (ls ! ?n)" and mem: "ls ! ?n \<in> set ls" by auto
  from Fun(4) n C have "hole_pos D \<notin> fun_poss (ls ! ?n)" by auto
  from Fun(1)[OF mem lin id this] obtain \<tau> x
    where IH: "ls ! ?n \<cdot> \<tau> = D\<langle>t\<rangle>" "x \<in> vars_term (ls ! ?n)" "(\<sigma> x, \<tau> x) \<in> rel" "\<forall>y. y \<noteq> x \<longrightarrow> \<sigma> y = \<tau> y" 
    by auto
  show ?case
  proof (intro exI[of _ \<tau>] exI[of _ x] conjI IH)
    show "x \<in> vars_term (Fun f ls)" using IH(2) n by auto
    have "C \<langle>t\<rangle> = Fun f ((map (\<lambda>t. t \<cdot> \<sigma>) ls)[?n := D\<langle>t\<rangle>])" unfolding C id_list by auto
    also have "(map (\<lambda>t. t \<cdot> \<sigma>) ls)[?n := D\<langle>t\<rangle>] = map (\<lambda>t. t \<cdot> \<tau>) ls" 
    proof (intro nth_equalityI, force, simp)
      fix i
      assume i: "i < length ls" 
      show "(map (\<lambda>t. t \<cdot> \<sigma>) ls)[?n := D\<langle>t\<rangle>] ! i = ls ! i \<cdot> \<tau>" 
      proof (cases "i = ?n")
        case True
        thus ?thesis using IH(1) n by auto
      next
        case False
        hence "(map (\<lambda>t. t \<cdot> \<sigma>) ls)[?n := D\<langle>t\<rangle>] ! i = ls ! i \<cdot> \<sigma>" using i by auto
        also have "\<dots> = ls ! i \<cdot> \<tau>" 
        proof (rule term_subst_eq)
          fix y
          assume y: "y \<in> vars_term (ls ! i)" 
          from Fun(2) have "is_partition (map vars_term ls)" by auto
          from this[unfolded is_partition_alt is_partition_alt_def, rule_format, of i ?n]
            IH(2) False n i y 
          have "x \<noteq> y" by auto
          with IH(4) show "\<sigma> y = \<tau> y" by auto
        qed
        finally show ?thesis .
      qed
    qed
    finally show "Fun f ls \<cdot> \<tau> = C\<langle>t\<rangle>" unfolding C by simp
  qed
qed

text \<open>We can always split a parallel step of an instance of a linear term 
  into those parts that occur within
  the substitution and the remaining part\<close>
lemma split_parallel_mctxt_step: fixes l t :: "('f,'v)term" 
  assumes "(l \<cdot> \<sigma>, t) \<in> par_rstep_mctxt R D infos"
    and "linear_term l" 
  shows "\<exists> \<tau> C infos'. hole_poss C \<subseteq> hole_poss D \<and> (l \<cdot> \<tau>, t) \<in> par_rstep_mctxt R C infos' \<and> hole_poss C \<subseteq> fun_poss l 
     \<and> (\<forall> x. (\<sigma> x, \<tau> x) \<in> par_rstep R) \<and> (\<forall> x \<in> vars_below_hole l C \<union> (UNIV - vars_term l). \<tau> x = \<sigma> x)"
proof -
  define s where "s = l \<cdot> \<sigma>" 
  let ?Prop = "\<lambda> l D t \<tau> C infos'. hole_poss C \<subseteq> hole_poss D \<and> (l \<cdot> \<tau>, t) \<in> par_rstep_mctxt R C infos' \<and> hole_poss C \<subseteq> fun_poss l 
     \<and> (\<forall> x \<in> vars_term l. (\<sigma> x, \<tau> x) \<in> par_rstep R) \<and> (\<forall> x \<in> vars_below_hole l C. \<tau> x = \<sigma> x)" 
  have "\<exists> \<tau> C infos'. ?Prop l D t \<tau> C infos'" using assms[folded s_def] using s_def
  proof (induct D arbitrary: l s t infos)
    case (MVar x l s t infos)
    from par_rstep_mctxt_MVarE[OF MVar(1)] MVar(2-)
    show ?case by (intro exI[of _ \<sigma>] exI[of _ "MVar x"] exI[of _ Nil], auto intro: par_rstep_mctxt_varI)
  next
    case (MHole l s t infos)
    from par_rstep_mctxt_MHoleE[OF MHole(1)] MHole(2-)
    obtain info where pc: "par_cond R info" and step: "(l \<cdot> \<sigma>,t) \<in> rrstep R"
      and id: "infos = [info]" "par_left info = l \<cdot> \<sigma>" "par_right info = t" by blast
    show ?case
    proof (cases l)
      case Fun
      hence poss: "[] \<in> fun_poss l" by auto
      thus ?thesis
        by (intro exI[of _ \<sigma>] exI[of _ MHole] exI[of _ infos] conjI par_rstep_mctxtI)
          (insert id pc step, auto)
    next
      case (Var x)
      show ?thesis using step unfolding Var
        by (intro exI[of _ "\<sigma>(x := t)"] exI[of _ "mctxt_of_term t"] exI[of _ Nil])
          (auto intro: par_rstep_mctxt_reflI elim!: rrstepE)
    qed
  next
    case (MFun f Cs l s t infos)
    show ?case
    proof (cases l)
      case (Var x)
      from MFun(2) have step: "(s, t) \<in> par_rstep R"
        using par_rstep_par_rstep_mctxt_conv by blast
      show ?thesis using MFun(4) step unfolding Var
        by (intro exI[of _ "\<sigma>(x := t)"] exI[of _ "mctxt_of_term t"] exI[of _ Nil])
          (auto simp: par_rstep_mctxt_def)
    next
      case (Fun g ls)
      let ?n = "length Cs" 
      from par_rstep_mctxt_MFunD[OF MFun(2)]
      obtain ss ts Infos
        where s: "s = Fun f ss" 
          and t: "t = Fun f ts" 
          and len: "length ss = ?n" 
          "length ts = ?n"
          "length Infos = ?n" 
          and infos: "infos = concat Infos" 
          and steps: "\<And> i. i < ?n \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep_mctxt R (Cs ! i) (Infos ! i)" 
        by blast
      from s[unfolded MFun(4)] Fun len have l: "l = Fun f ls" and ss_ls: "ss = map (\<lambda> s. s \<cdot> \<sigma>) ls" 
        and len_ls: "length ls = ?n" by auto 
      {
        fix i
        assume i: "i < ?n" 
        hence mem: "Cs ! i \<in> set Cs" by auto
        from l len_ls i MFun(3) have lin: "linear_term (ls ! i)" by auto
        from ss_ls i len have "ss ! i = ls ! i \<cdot> \<sigma>" by auto
        note IH = MFun(1)[OF mem steps[OF i] lin this]
      }

      hence "\<forall> i. \<exists>\<tau> C infos. i < ?n \<longrightarrow> ?Prop (ls ! i) (Cs ! i) (ts ! i) \<tau> C infos" by auto
      from choice[OF this] obtain \<tau> where "\<forall> i. \<exists>C infos. i < ?n \<longrightarrow> ?Prop (ls ! i) (Cs ! i) (ts ! i) (\<tau> i) C infos" by auto
      from choice[OF this] obtain C where "\<forall> i. \<exists>infos. i < ?n \<longrightarrow> ?Prop (ls ! i) (Cs ! i) (ts ! i) (\<tau> i) (C i) infos" by auto
      from choice[OF this] obtain infos where IH: "i < ?n \<Longrightarrow> ?Prop (ls ! i) (Cs ! i) (ts ! i) (\<tau> i) (C i) (infos i)" for i by auto
      let ?is = "[0..<?n]" 

      let ?C = "MFun f (map C ?is)"
      let ?infos = "concat (map infos ?is)" 
      define \<tau>' where "\<tau>' = fun_merge (map \<tau> ?is) (map (\<lambda> i. vars_term (ls ! i)) ?is)" 

      {
        fix i
        assume i: "i < ?n" 
        {
          fix x
          assume x: "x \<in> vars_term (ls ! i)" 
          have [simp]: "map (\<lambda>i. vars_term (ls ! i)) ?is = map vars_term ls" using len_ls
            by (intro nth_equalityI, auto)
          have "\<tau>' x = \<tau> i x" unfolding \<tau>'_def using \<open>linear_term l\<close> Fun
            by (subst fun_merge_part[of _ i], insert i len_ls x, auto)
        } note tau = this
        have "ls ! i \<cdot> \<tau>' = ls ! i \<cdot> \<tau> i" 
          by (rule term_subst_eq, insert tau, auto)
        note tau this
      } note tau = this

      show ?thesis unfolding t
      proof (intro exI conjI ballI)
        show "hole_poss ?C \<subseteq> fun_poss l" unfolding Fun using len_ls by (auto, insert IH, auto)
        {
          fix x
          assume "x \<in> vars_term l" 
          then obtain i where i: "i < ?n" and x: "x \<in> vars_term (ls ! i)" unfolding Fun using len_ls
            by (auto simp: set_conv_nth)
          from IH[OF i] show "(\<sigma> x, \<tau>' x) \<in> par_rstep R" using tau(1)[OF i x] x by auto
        }
        have ltau: "l \<cdot> \<tau>' = Fun f (map (\<lambda> i. ls ! i \<cdot> \<tau> i) ?is)" unfolding l using tau(2) len_ls
          by (auto intro: nth_equalityI)
        have lenis: "length ?is = ?n" by auto
        show "(l \<cdot> \<tau>', Fun f ts) \<in> par_rstep_mctxt R ?C ?infos" 
          unfolding ltau using len IH
          by (intro par_rstep_mctxt_funI, auto)
        show "hole_poss ?C \<subseteq> hole_poss (MFun f Cs)" using IH[THEN conjunct1] by fastforce
        {
          fix x
          assume "x \<in> vars_below_hole l ?C" 
          also have "l = Fun f (map (\<lambda> i. ls ! i) ?is)" unfolding l using len_ls by (auto intro: nth_equalityI)
          also have "vars_below_hole \<dots> ?C = \<Union> ((\<lambda> i. vars_below_hole (ls ! i) (C i)) ` set ?is)" 
            unfolding vars_below_hole.simps using len_ls[symmetric] by (force simp: set_zip)
          finally obtain i where i: "i < ?n" and x: "x \<in> vars_below_hole (ls ! i) (C i)" by auto
          with vars_below_hole_vars_term have "x \<in> vars_term (ls ! i)" by force
          from tau(1)[OF i this]
          have "\<tau>' x = \<tau> i x" .
          also have "\<dots> = \<sigma> x" using IH[OF i] x by auto
          finally show "\<tau>' x = \<sigma> x" .
        }        
      qed
    qed
  qed  
  then obtain \<tau>' C infos where main: 
    "hole_poss C \<subseteq> hole_poss D" 
    "(l \<cdot> \<tau>', t) \<in> par_rstep_mctxt R C infos" 
    "hole_poss C \<subseteq> fun_poss l"
    "(\<forall> x \<in> vars_term l. (\<sigma> x, \<tau>' x) \<in> par_rstep R)" 
    "(\<forall> x \<in> vars_below_hole l C. \<tau>' x = \<sigma> x)" 
    by blast
  define \<tau> where "\<tau> = (\<lambda> x. if x \<in> vars_term l then \<tau>' x else \<sigma> x)" 
  show ?thesis
  proof (intro exI conjI allI ballI)
    show "(l \<cdot> \<tau>, t) \<in> par_rstep_mctxt R C infos" 
      by (subst term_subst_eq[of _ _ \<tau>'], insert main, auto simp: \<tau>_def)
    show "hole_poss C \<subseteq> fun_poss l" by fact
    show "(\<sigma> x, \<tau> x) \<in> par_rstep R" for x unfolding \<tau>_def using main(4) by auto
    show "x \<in> vars_below_hole l C \<union> (UNIV - vars_term l) \<Longrightarrow> \<tau> x = \<sigma> x" for x using main unfolding \<tau>_def by auto
  qed (insert main, auto)
qed 

text \<open>The key lemma for PCPs\<close>
lemma parallel_critical_peaks_of_rule: fixes \<sigma> :: "('f,'v)subst" 
  assumes
    par_step: "(s,t) \<in> par_rstep_mctxt R' C infos" 
    and s: "s = l \<cdot> \<sigma>"
    and l: "linear_term l" 
    and u: "u = r \<cdot> \<sigma>" 
    and R': "R' \<subseteq> R" 
  shows "(\<exists> v. (t,v) \<in> rrstep {(l,r)} \<and> (u,v) \<in> par_rstep R') \<or> 
    \<comment> \<open>above: parallel step is completely inside \<sigma>, so that there is a trivial join.

        below: we get a parallel critical pair because of some overlap where the
         additional steps inside the substition are done from \<delta> to \<gamma>, and these steps
         are not occurring outside the variables the of multihole-context C that describes the overlap.
         This in particular shows that no steps are done for variables that
         occur below hole positions of cs = C[..].\<close>
    (\<exists> C' s' t' u' rls \<gamma> \<delta> infos. 
      (C', t', s', u', rls) \<in> parallel_critical_peaks_of_rule R (l,r) \<and>
      s = s' \<cdot> \<delta> \<and> 
      u = u' \<cdot> \<delta> \<and> 
      t = t' \<cdot> \<gamma> \<and> 
      \<comment> \<open> in total: t' <-||,C'- s' --root--> u'\<close>
      (s', t') \<in> par_rstep_mctxt (set rls) C' infos \<and>
      (s', u') \<in> rrstep {(l,r)} \<and>
      set rls \<subseteq> R' \<and>
      (\<forall> x. (\<delta> x, \<gamma> x) \<in> par_rstep R') \<and> 
      (\<forall> x. x \<notin> vars_mctxt C' \<longrightarrow> \<delta> x = \<gamma> x) \<and>
      (vars_below_hole s' C' \<inter> vars_mctxt C' = {}) \<and>
      (vars_term s' = vars_below_hole s' C' \<union> vars_mctxt C') \<and>
      (C \<noteq> MHole \<longrightarrow> C' \<noteq> MHole))"   
proof -
  let ?D = C
  from split_parallel_mctxt_step[OF par_step[unfolded s] l]
  obtain \<tau> C infos where par_step: "(l \<cdot> \<tau>, t) \<in> par_rstep_mctxt R' C infos" and
    Cl: "hole_poss C \<subseteq> fun_poss l" and
    hCCC: "hole_poss C \<subseteq> hole_poss ?D" and
    var_steps: "\<And> x. (\<sigma> x, \<tau> x) \<in> par_rstep R'" and
    tau_sigma: "\<And> x. x \<in> vars_below_hole l C \<union> (vars_term r - vars_term l) \<Longrightarrow> \<tau> x = \<sigma> x" 
    by blast
  let ?s = "l \<cdot> \<tau>" 
  let ?n = "num_holes C"
  let ?ss = "par_lefts infos" 
  let ?ts = "par_rights infos" 
  show ?thesis
  proof (cases "?n = 0")
    case True
    from par_step have eqs: "l \<cdot> \<tau> =\<^sub>f (C, ?ss)" "t =\<^sub>f (C, ?ts)" 
      by (auto simp: par_rstep_mctxt_def)
    from eqfE[OF eqs(1)] eqfE[OF eqs(2)] True have tltau: "t = l \<cdot> \<tau>" by auto
    have "\<exists> v. (t,v) \<in> rrstep {(l,r)} \<and> (u,v) \<in> par_rstep R'" 
    proof (intro exI conjI)
      show "(t, r \<cdot> \<tau>) \<in> rrstep {(l,r)}" unfolding tltau by auto
      show "(u, r \<cdot> \<tau>) \<in> par_rstep R'" unfolding u
        using var_steps
        by (simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
    qed
    thus ?thesis by blast
  next
    case False
    from par_step(1)[unfolded par_rstep_mctxt_def]
    have s: "?s =\<^sub>f (C, ?ss)" and t: "t =\<^sub>f (C, ?ts)" and steps: "par_conds R' infos" by auto
    have len: "length infos = ?n"  
      and fill: "?s = fill_holes C ?ss" "t = fill_holes C ?ts" 
      using eqfE[OF s] eqfE[OF t] by auto
    from par_conds_imp_rrstep[OF steps] len
    have steps: "\<And> i. i < ?n \<Longrightarrow> (?ss ! i, ?ts ! i) \<in> rrstep R'" by auto
    have "\<forall> i. \<exists> li ri \<sigma>i. i < ?n \<longrightarrow> (li,ri) \<in> R' \<and> ?ss ! i = li \<cdot> \<sigma>i \<and> ?ts ! i = ri \<cdot> \<sigma>i" 
      using steps len unfolding rrstep_def' by auto 
    from choice[OF this] obtain li where "\<forall> i. \<exists> ri \<sigma>i. i < ?n \<longrightarrow> (li i,ri) \<in> R' \<and> ?ss ! i = li i \<cdot> \<sigma>i \<and> ?ts ! i = ri \<cdot> \<sigma>i" by auto
    from choice[OF this] obtain ri where "\<forall> i. \<exists> \<sigma>i. i < ?n \<longrightarrow> (li i,ri i) \<in> R' \<and> ?ss ! i = li i \<cdot> \<sigma>i \<and> ?ts ! i = ri i \<cdot> \<sigma>i" by auto
    from choice[OF this] obtain \<sigma>i where rules: "\<And> i. i < ?n \<Longrightarrow> (li i,ri i) \<in> R' \<and> ?ss ! i = li i \<cdot> \<sigma>i i \<and> ?ts ! i = ri i \<cdot> \<sigma>i i" by auto
    from \<open>hole_poss C \<subseteq> fun_poss l\<close> have "hole_poss C \<subseteq> poss l" 
      using fun_poss_imp_poss by blast
    from eqF_substD[OF s this]
    obtain D lps where l_ctxt: "l =\<^sub>f (D,lps)" "C = D \<cdot>mc \<tau>" and ss_tau: "?ss = map (\<lambda> lp. lp \<cdot> \<tau>) lps" 
      by blast
    from eqfE[OF l_ctxt(1)] have vars_lps: "\<Union> (vars_term ` set lps) \<subseteq> vars_term l"
      by (simp add: vars_term_fill_holes')
    from len arg_cong[OF ss_tau, of length] have "length lps = ?n" by auto
    note len = len this
    {
      fix i
      assume i: "i < ?n" 
      from rules[OF i] arg_cong[OF ss_tau, of "\<lambda> xs. xs ! i"] i len R'
      have rule: "(li i, ri i) \<in> R" and unif: "li i \<cdot> \<sigma>i i = lps ! i \<cdot> \<tau>" by auto
    } note rule_unif = this
    define list where "list = map (\<lambda> i. (lps ! i, li i, ri i)) [0..<?n]" 
    have lps_list: "lps = map fst list" unfolding list_def using len by (intro nth_equalityI, auto)
    hence fst_list: "fst ` set list = set lps" by auto
    have len_list[simp]: "length list = ?n" by (auto simp: list_def)

    have vars_bh_list: "vars_below_hole l D = \<Union> (vars_term ` fst ` set list)" 
      using l_ctxt(1) unfolding fst_list by (rule vars_below_hole_eqf)

    let ?unif = "map (\<lambda>(lp, li, ri). (li, lp)) list" 
    define V where "V = \<Union> (vars_term ` rhss (set ?unif))" 
    have V: "V = vars_below_hole l D" unfolding vars_bh_list V_def by auto
    define Vo where "Vo = UNIV - V" 
    have "\<exists>\<sigma> \<tau>' \<delta>.
     mgu_vd_list ren ?unif = Some (\<sigma>, \<tau>') \<and>
     \<tau> = \<tau>' \<circ>\<^sub>s \<delta> \<and> (\<forall>i<length ?unif. \<sigma>i i = \<sigma> ! i \<circ>\<^sub>s \<delta> \<and> fst (?unif ! i) \<cdot> \<sigma> ! i = snd (?unif ! i) \<cdot> \<tau>')
     \<and> \<tau>' ` Vo \<subseteq> Var ` (UNIV - \<Union> (vars_term ` \<tau>' ` V) - (\<Union> {\<Union> (vars_term ` range (\<sigma> ! i)) | i. i < length ?unif})) \<and> inj_on \<tau>' Vo" 
      by (rule mgu_vd_list_complete[of ?unif, folded V_def, folded Vo_def],
          insert rule_unif, auto simp: list_def)
    then obtain \<sigma>' \<tau>' \<delta>' where 
      mgu: "mgu_vd_list ren ?unif = Some (\<sigma>', \<tau>')" and
      mgu_id: "\<tau> = \<tau>' \<circ>\<^sub>s \<delta>'" "\<And> i. i< ?n \<Longrightarrow> \<sigma>i i = \<sigma>' ! i \<circ>\<^sub>s \<delta>' \<and> fst (?unif ! i) \<cdot> \<sigma>' ! i = snd (?unif ! i) \<cdot> \<tau>'" and
      outside: "\<tau>' ` Vo \<subseteq> Var ` (UNIV - \<Union> (vars_term ` \<tau>' ` V) - (\<Union> {\<Union> (vars_term ` range (\<sigma>' ! i)) | i. i < ?n}))" and 
      inj_\<tau>': "inj_on \<tau>' Vo" 
      by auto  
    define W where "W = vars_term l \<union> vars_term r" 
    define Vo' where "Vo' = W - V" 
    have Vo': "Vo' \<subseteq> Vo" unfolding Vo_def Vo'_def by auto
    from mgu_vd_list_sound[OF mgu, simplified] 
    have len_\<sigma>: "length \<sigma>' = length list"
      and mgu_eq: "i < ?n \<Longrightarrow> fst (?unif ! i) \<cdot> \<sigma>' ! i = snd (?unif ! i) \<cdot> \<tau>'" for i 
      by (auto simp: list_def)
    let ?args = "map2 (\<lambda>(_, li, y). (\<cdot>) y) list \<sigma>'" 
    let ?R = "map snd list" 
    let ?C = "D \<cdot>mc \<tau>'"
    let ?r = "fill_holes (D \<cdot>mc \<tau>') ?args" 
    let ?l = "l \<cdot> \<tau>'" 
    let ?r2 = "r \<cdot> \<tau>'" 
    have crit_pair: "(?C, ?r, ?l, ?r2, ?R) \<in> (parallel_critical_peaks_of_rule R (l,r))" 
      unfolding parallel_critical_peaks_of_rule_def split 
      by (rule CollectI, rule exI[of _ D], rule exI[of _ lps], 
          rule exI[of _ "map (\<lambda> i. (li i, ri i)) [0..<?n]"], 
          rule exI[of _ \<sigma>'], rule exI[of _ \<tau>'])
        (insert False rule_unif len \<open>hole_poss C \<subseteq> fun_poss l\<close> , 
          auto simp: mgu[symmetric] o_def hole_poss_subst list_def subst_apply_mctxt_numholes l_ctxt 
          intro!: arg_cong[of _ _ "fill_holes _"] arg_cong[of _ _ "mgu_vd_list ren"] 
          nth_equalityI)
    have tau: "\<tau> = \<tau>' \<circ>\<^sub>s \<delta>'" using mgu_id by simp
    have eq: "num_holes (D \<cdot>mc \<tau>') = length ?args" using len_\<sigma> by (simp add: list_def l_ctxt subst_apply_mctxt_numholes)
    have CD:  "C = D \<cdot>mc \<tau>' \<cdot>mc \<delta>'" unfolding l_ctxt mgu_id
      by (simp add: subst_apply_mctxt_compose)
    have VC: "V = vars_below_hole l C" unfolding V CD
      by (simp add: hole_poss_subst)

    note var_steps[unfolded tau subst_compose_def]
    {
      fix x
      assume "x \<in> Vo" 
      with outside have "\<exists> y. \<tau>' x = Var y" by (cases "\<tau>' x", auto)
    } hence "\<forall> x. \<exists> y. x \<in> Vo \<longrightarrow> \<tau>' x = Var y" by auto
    from choice[OF this] obtain ren where ren: "\<And> x. x \<in> Vo \<Longrightarrow> \<tau>' x = Var (ren x)" by auto

    with inj_\<tau>' have inj_ren: "inj_on ren Vo" unfolding inj_on_def by auto
    define \<delta> where "\<delta> = (\<lambda> x. if x \<in> ren ` Vo' then \<sigma> (the_inv_into Vo ren x) else \<delta>' x)" 
    define \<tau>'' where "\<tau>'' = (\<lambda> x. if x \<in> ren ` Vo' then \<tau> (the_inv_into Vo ren x) else \<delta>' x)" 

    {
      fix x
      assume x: "x \<in> Vo'"
      hence "x \<in> Vo" using Vo' by auto
      with x ren[OF this] have "\<tau>' x \<cdot> \<delta> = \<sigma> x" "\<tau>' x \<cdot> \<tau>'' = \<tau> x" 
        unfolding \<delta>_def \<tau>''_def using the_inv_into_f_f[OF inj_ren] by auto 
    } note xVo = this 

    {
      fix x
      have "\<tau>'' x = \<delta>' x" 
      proof (rule ccontr)
        assume diff: "\<tau>'' x \<noteq> \<delta>' x" 
        from this[unfolded \<tau>''_def] have "x \<in> ren ` Vo'" by (auto split: if_splits)
        then obtain y where "x = ren y" and y: "y \<in> Vo'" by auto  
        from ren[of y] Vo' this have "\<tau>' y = Var x" by auto
        from y[unfolded Vo'_def] have y: "y \<in> W - V" by auto
        show False using y \<open>\<tau>' y = Var x\<close> 
          by (metis Vo'_def diff eval_term.simps(1) subst_compose tau xVo(2))
      qed
    } 
    hence tau_delta: "\<tau>'' = \<delta>'" by auto

    have VW: "V \<subseteq> W" unfolding V using vars_below_hole_vars_term[of l D] unfolding W_def by auto
    {
      fix x
      assume "x \<notin> Vo'" "x \<in> W"  
      from this[unfolded Vo'_def] have "x \<in> V" by auto
      from this[unfolded VC]
      have "x \<in> vars_below_hole l C" by auto    
      with tau_sigma
      have "\<sigma> x = \<tau> x" by simp
      moreover {
        fix \<gamma>'
        assume gamma': "\<gamma>' \<in> {\<delta>, \<tau>''}" 
        have "\<tau>' x \<cdot> \<gamma>' = \<tau> x" unfolding tau subst_compose_def
        proof (rule term_subst_eq)
          fix y
          assume y: "y \<in> vars_term (\<tau>' x)" 
          show "\<gamma>' y = \<delta>' y" 
          proof (cases "y \<in> ren ` Vo'")
            case False
            thus ?thesis using gamma' unfolding \<tau>''_def \<delta>_def by auto
          next
            case True
            then obtain z where z: "z \<in> Vo'" and yz: "y = ren z" by auto
            from ren[of z] z Vo' yz have "\<tau>' z = Var y" by auto
            with z have "Var y \<in> \<tau>' ` Vo'" by auto
            with outside Vo' have "y \<notin> \<Union> (vars_term ` \<tau>' ` V)" by auto
            with y \<open>x \<in> V\<close>
            have False by auto
            thus ?thesis by simp
          qed
        qed
      }
      ultimately have "\<tau>' x \<cdot> \<delta> = \<tau> x" "\<tau>' x \<cdot> \<tau>'' = \<tau> x" "\<sigma> x = \<tau> x" 
        by auto
    } note xNoVo = this

    from Cl have "hole_poss D \<subseteq> fun_poss l" unfolding CD
      by (simp add: hole_poss_subst)
    hence hDl: "hole_poss D \<subseteq> poss l"
      using hole_poss_subset_poss l_ctxt(1) by blast
    have "vars_below_hole ?l ?C = vars_below_hole ?l D" by simp
    also have "\<dots> = \<Union> (vars_term ` \<tau>' ` V)" unfolding V using hDl
      by (subst vars_below_hole_term_subst, auto)
    finally have vars_bh_lC: "vars_below_hole ?l ?C = \<Union> (vars_term ` \<tau>' ` V)" .

    have sigma: "x \<in> W \<Longrightarrow> \<sigma> x = \<tau>' x \<cdot> \<delta>" for x
    proof -
      assume x: "x \<in> W"  
      show "\<sigma> x = \<tau>' x \<cdot> \<delta>" 
      proof (cases "x \<in> Vo'")
        case True
        thus ?thesis using xVo by auto
      next
        case False
        from xNoVo[OF False x] show ?thesis by auto
      qed
    qed

    have tau2: "x \<in> W \<Longrightarrow> \<tau> x = \<tau>' x \<cdot> \<tau>''" for x
    proof -
      assume x: "x \<in> W"  
      show "\<tau> x = \<tau>' x \<cdot> \<tau>''" 
      proof (cases "x \<in> Vo'")
        case True
        thus ?thesis using xVo by auto
      next
        case False
        from xNoVo[OF False x] show ?thesis by auto
      qed
    qed

    have "map (\<lambda> ti. ti \<cdot> \<tau>'') ?args = map (\<lambda>ti. ti \<cdot> \<delta>') ?args" unfolding tau_delta ..
    also have "\<dots> = map2 (\<lambda>(_, li, y). (\<cdot>) y) list (map \<sigma>i [0..<?n])" 
      using mgu_id(2) len_\<sigma> unfolding list_def by (auto intro!: nth_equalityI)
    also have "\<dots> = ?ts" unfolding list_def using rules len by (auto intro!: nth_equalityI)
    finally have subst: "map (\<lambda>ti. ti \<cdot> \<tau>'') ?args = ?ts" .
    from eqfE[OF l_ctxt(1)] have "vars_mctxt D \<subseteq> vars_term l"
      by (simp add: vars_term_fill_holes')
    hence varsD: "vars_mctxt D \<subseteq> W" unfolding W_def by auto
    have tr: "t = ?r \<cdot> \<tau>''" 
      unfolding fill l_ctxt
      unfolding subst_apply_mctxt_fill_holes[OF eq]
      unfolding subst subst_apply_mctxt_compose
      by (subst subst_apply_mctxt_cong[of _ _ "\<tau>' \<circ>\<^sub>s \<tau>''"], insert tau2 varsD, auto simp: subst_compose_def)

    {
      fix x
      assume "x \<in> vars_below_hole ?l ?C" 
      then obtain y where y: "y \<in> V" and x: "x \<in> vars_term (\<tau>' y)" 
        unfolding vars_bh_lC by auto
      from y VW have yW: "y \<in> W" by auto
      from y have "y \<notin> Vo" unfolding Vo_def by auto
      hence "y \<notin> Vo'" using Vo' by auto
      from xNoVo[OF this yW] have tau_eq: "\<tau>' y \<cdot> \<delta> = \<tau>' y \<cdot> \<tau>''" by auto
      hence "\<delta> x = \<tau>'' x" using x
        by (simp add: term_subst_eq_conv)        
    } note vars_below_hole = this

    {
      fix x
      assume "x \<in> vars_term ?r2 - vars_term ?l" 
      from this[unfolded vars_term_subst] obtain y where 
        y: "y \<in> vars_term r - vars_term l" and x: "x \<in> vars_term (\<tau>' y)" by auto
      from y have yV: "y \<notin> V" unfolding V using vars_below_hole_vars_term by fastforce
      have yW: "y \<in> W" unfolding W_def using y by auto
      have yVo': "y \<in> Vo'" unfolding Vo'_def using yV yW by auto
      have yVo: "y \<in> Vo" unfolding Vo_def using yV by auto
      from ren[OF this] x have "\<tau>' y = Var x" by auto
      from xVo[OF yVo', unfolded this]
      have "\<delta> x = \<sigma> y" "\<tau>'' x = \<tau> y" by auto
      with tau_sigma[of y] y
      have "\<delta> x = \<tau>'' x" by auto
    } note fresh_vars_r2 = this 

    {
      fix x  
      assume "x \<in> vars_term ?r - vars_mctxt ?C" 
      from this[unfolded vars_term_fill_holes'[OF eq]]
      have "x \<in> \<Union> (vars_term ` set ?args)" and xC: "x \<notin> vars_mctxt ?C" by auto
      from this[unfolded list_def]
      obtain i where i: "i < ?n" and x: "x \<in> vars_term (ri i \<cdot> \<sigma>' ! i)" 
        by (auto simp: set_zip)      
      have "ri i \<cdot> \<sigma>' ! i \<cdot> \<delta>' = ri i \<cdot> \<sigma>i i" using mgu_id(2)[of i] i
        using list_def by auto
      {
        assume "\<delta> x \<noteq> \<tau>'' x" 
        from this[unfolded \<delta>_def tau_delta]
        have "x \<in> ren ` Vo'" by (auto split: if_splits)
        from this(1) obtain y where
          *: "y \<in> Vo'" "x = ren y" by auto
        from ren[of y] this have **: "\<tau>' y = Var (ren y)" "y \<in> Vo" unfolding Vo_def Vo'_def by auto
        from * ** have "Var x \<in> \<tau>' ` Vo" by auto
        with outside i  have "Var x \<notin> Var ` (\<Union> (vars_term ` range (\<sigma>' ! i)))" by auto
        hence "x \<notin> \<Union> (vars_term ` range (\<sigma>' ! i))" by auto
        with x have False by (simp add: vars_term_subst)
      }
      hence "\<delta> x = \<tau>'' x" by auto
    } note fresh_vars_r = this  

    from eqfE[OF l_ctxt(1)] 
    have l: "l = fill_holes D lps" "num_holes D = length lps" by auto
    have V_lps: "V = \<Union> (vars_term ` set lps)" 
      unfolding V_def list_def using l(2) len by auto

    {
      fix x
      assume xbh: "x \<in> vars_below_hole ?l ?C"
      have "x \<notin> vars_mctxt ?C" 
      proof
        assume "x \<in> vars_mctxt ?C" 
        from this[unfolded vars_mctxt_subst]
        obtain y where y: "y \<in> vars_mctxt D" and xy: "x \<in> vars_term (\<tau>' y)" by auto
        from xbh[unfolded vars_bh_lC] obtain z where z: "z \<in> V" and xz: "x \<in> vars_term (\<tau>' z)" by auto
        from vars_mctxt_linear[OF l_ctxt(1) \<open>linear_term l\<close>, folded V_lps]
        have "vars_mctxt D \<inter> V = {}" by auto
        with y have yVo: "y \<in> Vo" unfolding Vo_def by auto
        from ren[OF yVo] have "\<tau>' y = Var (ren y)" by auto
        with xy have tau_yx: "\<tau>' y = Var x" and "ren y = x" by auto 
        from yVo have "\<tau>' y \<in> \<tau>' ` Vo" by auto
        from set_mp[OF outside this, unfolded tau_yx]
        have "x \<notin> \<Union> (vars_term ` \<tau>' ` V)" by auto
        with z xz show False by auto
      qed
    }
    hence vbh: "vars_below_hole ?l ?C \<inter> vars_mctxt ?C = {}" by auto

    {
      fix x
      have "(\<delta> x, \<tau>'' x) \<in> par_rstep R'" 
      proof (cases "x \<in> ren ` Vo'")
        case False
        hence "\<delta> x = \<tau>'' x" 
          unfolding \<delta>_def \<tau>''_def by auto
        thus ?thesis by auto
      next
        case True
        then obtain y where "x = ren y" and "y \<in> Vo'" by auto
        from ren[of y] Vo' this have "\<tau>' y = Var x" by auto
        with xVo[OF \<open>y \<in> Vo'\<close>] have "\<delta> x = \<sigma> y" "\<tau>'' x = \<tau> y" by auto
        with var_steps[of y] show ?thesis by auto
      qed
    } note vars_steps = this

    define \<gamma> where "\<gamma> = (\<lambda> x. if x \<in> vars_term ?r \<inter> vars_mctxt ?C then \<delta>' x else \<delta> x)" 
    note \<gamma>def = \<gamma>_def[folded tau_delta]
    show ?thesis
    proof (rule disjI2, intro bexI exI conjI)
      show "s = ?l \<cdot> \<delta>" unfolding assms(2) subst_subst using sigma[unfolded W_def] 
        by (intro term_subst_eq, auto simp: subst_compose_def)
      show "u = ?r2 \<cdot> \<delta>" unfolding u subst_subst using sigma[unfolded W_def] 
        by (intro term_subst_eq, auto simp: subst_compose_def)
      have "t = ?r \<cdot> \<tau>''" unfolding tr ..
      also have "\<dots> = ?r \<cdot> \<gamma>" 
      proof (rule term_subst_eq)
        fix x
        assume "x \<in> vars_term ?r" 
        thus "\<tau>'' x = \<gamma> x" using fresh_vars_r[of x] unfolding \<gamma>def by auto
      qed
      finally show "t = ?r \<cdot> \<gamma>" .
      show "(?l,?r2) \<in> rrstep {(l,r)}" by auto
      show "(?C, ?r, ?l, ?r2, ?R) \<in> parallel_critical_peaks_of_rule R (l, r)" by fact
      show "\<forall>x. (\<delta> x, \<gamma> x) \<in> par_rstep R'" using vars_steps unfolding \<gamma>def by auto
      show "\<forall> x. x \<notin> vars_mctxt ?C \<longrightarrow> \<delta> x = \<gamma> x" 
        unfolding \<gamma>_def by auto
      show "?D \<noteq> MHole \<longrightarrow> ?C \<noteq> MHole" using hCCC unfolding CD by (cases ?D, auto)
      show "vars_below_hole ?l ?C \<inter> vars_mctxt ?C = {}" by fact
      define Infos where "Infos = map (\<lambda> i. Par_Info (li i \<cdot> \<sigma>' ! i) (ri i \<cdot> \<sigma>' ! i) (li i, ri i)) [0..<?n]" 
      have rInfos: "par_rights Infos = ?args"
        using len_\<sigma> unfolding Infos_def list_def by (auto intro!: nth_equalityI)
      {
        fix i
        assume i: "i < ?n" 
        have "lps ! i \<cdot> \<tau>' = li i \<cdot> \<sigma>' ! i" using mgu_eq[OF i] i unfolding list_def by auto
      }
      hence lInfos: "par_lefts Infos = map (\<lambda> lp. lp \<cdot> \<tau>') lps" 
        unfolding lps_list unfolding list_def Infos_def by auto 
      have Infos: "par_conds R' Infos" unfolding Infos_def
        using rules R' by (auto simp: par_cond_def)

      have "(?l,?r) \<in> par_rstep_mctxt R' ?C Infos" 
        unfolding l(1) subst_apply_mctxt_fill_holes[OF l(2)]
        apply (intro par_rstep_mctxtI[OF _ _ Infos]; unfold lInfos rInfos; intro eqfI refl)
        subgoal using len by (auto simp: CD subst_apply_mctxt_numholes)
        subgoal using len by (auto simp: CD subst_apply_mctxt_numholes list_def len_\<sigma>)
        done
      hence "(?l,?r) \<in> par_rstep_mctxt (R' \<inter> par_rules Infos) ?C Infos" 
        unfolding par_rstep_mctxt_def by (auto simp: par_cond_def)
      also have "R' \<inter> par_rules Infos = set ?R" unfolding Infos_def list_def using rules by force 
      finally show step: "(?l,?r) \<in> par_rstep_mctxt (set ?R) ?C Infos" by auto
      show "set ?R \<subseteq> R'" unfolding list_def using rules by force
      from step[unfolded par_rstep_mctxt_def]
      have "?l =\<^sub>f (?C, par_lefts Infos)" by auto
      note * = eqfE[OF this]
      have [simp]: "{0..<?n} = {i . i < ?n}" by auto
      show "vars_term ?l = vars_below_hole ?l ?C \<union> vars_mctxt ?C" 
        unfolding *(1) vars_term_fill_holes'[OF *(2)] 
        unfolding *(1)[symmetric] vars_bh_lC V_lps 
        unfolding lInfos 
        by (fastforce simp: vars_term_subst)
    qed
  qed
qed

subsection \<open>Gramlich's and Toyama's Criteria using PCPs\<close>

abbreviation ren2 where "ren2 \<equiv> renaming2 ren" 

definition nontriv_ordinary_cps :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs" where
  "nontriv_ordinary_cps R S = { cp | b cp. (b,cp) \<in> critical_pairs ren2 R S \<and> fst cp \<noteq> snd cp}" 

definition gramlich_pcp_condition :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "gramlich_pcp_condition R S = (\<forall> cp \<in> nonroot_parallel_cps R S. cp \<in> (rstep S)^*)" 

definition toyama_pcp_condition :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "toyama_pcp_condition R S = (\<forall> (C,t,s,u) \<in> nonroot_parallel_peaks R S. 
    \<exists> v. (t,v) \<in> (rstep S)^* \<and> (u, v) \<in> par_rstep_var_restr R (vars_mctxt C))" 

lemma gramlich_implies_toyama: assumes "gramlich_pcp_condition R S" 
  shows "toyama_pcp_condition R S" 
  unfolding toyama_pcp_condition_def 
proof (intro ballI, clarify, goal_cases)
  case (1 C t s u)
  hence "(t, u) \<in> nonroot_parallel_cps R S" 
    unfolding nonroot_parallel_peaks_def nonroot_parallel_cps_def    
    by (force split: if_splits)
  from assms[unfolded gramlich_pcp_condition_def, rule_format, OF this]
  have "(t, u) \<in> (rstep S)\<^sup>*" by auto 
  then show ?case 
    by (intro exI[of _ u], auto intro!: exI[of _ "mctxt_of_term u"] exI[of _ Nil] simp: par_rstep_mctxt_def par_rstep_var_restr_def)
qed

definition cp_parstep_steps_joinable :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "cp_parstep_steps_joinable R S = (\<forall> t u. (t, u) \<in> nontriv_ordinary_cps R S \<longrightarrow> 
     (\<exists> v. (t, v) \<in> par_rstep R \<and> (u, v) \<in> (rstep S)^*))" 

definition "gramlich_parallel_critical_pair_condition R S = (gramlich_pcp_condition R S \<and> cp_parstep_steps_joinable R S)" 
definition "toyama_parallel_critical_pair_condition R S = (toyama_pcp_condition R S \<and> cp_parstep_steps_joinable R S)" 

context
  fixes R S :: "('f,'v)trs" 
  assumes ll: "left_linear_trs R" "left_linear_trs S"  
    and crit_pairs: "cp_parstep_steps_joinable R S" 
    and parallel_crit_pairs: "toyama_pcp_condition R S" 
begin

lemma par_step_single_root_step_join: assumes 
  par_step: "(s,t) \<in> par_rstep_mctxt R C infos" 
  and step: "(s,u) \<in> rrstep S"
  and C: "C \<noteq> MHole" 
shows "\<exists> v. (t,v) \<in> (rstep S)^* \<and> (u,v) \<in> par_rstep R" 
proof -
  from rrstepE[OF assms(2)] obtain l r \<sigma> where 
    lr: "(l,r) \<in> S" and s: "s = l \<cdot> \<sigma>" and u: "u = r \<cdot> \<sigma>" by auto  
  from lr ll have l: "linear_term l" unfolding left_linear_trs_def by auto
  from parallel_critical_peaks_of_rule[OF par_step s l u subset_refl] C
  have "(\<exists>v. (t, v) \<in> rrstep {(l, r)} \<and> (u, v) \<in> par_rstep R) \<or>
  (\<exists>C cs ct cu rls \<gamma> \<delta>.
      (C, ct, cs, cu, rls) \<in> parallel_critical_peaks_of_rule R (l, r) \<and>
      s = cs \<cdot> \<delta> \<and>
      u = cu \<cdot> \<delta> \<and>
      t = ct \<cdot> \<gamma> \<and>
      (\<forall>x. (\<delta> x, \<gamma> x) \<in> par_rstep R) \<and>
      (\<forall>x. x \<notin> vars_mctxt C \<longrightarrow> \<delta> x = \<gamma> x) \<and> 
      (vars_below_hole cs C \<inter> vars_mctxt C = {}) \<and>
      (vars_term cs = vars_below_hole cs C \<union> vars_mctxt C) \<and>
      C \<noteq> MHole)" (is "?triv \<or> ?crit_pair")
    by blast
  thus ?thesis
  proof 
    assume ?triv
    then obtain v where tv: "(t, v) \<in> rrstep {(l, r)}" and uv: "(u, v) \<in> par_rstep R" 
      by auto
    from tv lr have "(t,v) \<in> rstep S"
      by (metis rrstepE rrstepI rrstep_imp_rstep singletonD)
    with uv show ?thesis by (intro exI[of _ v], auto)
  next
    assume ?crit_pair
    then obtain C cs ct cu rls \<gamma> \<delta> where
      crit: "(C, ct, cs, cu, rls) \<in> parallel_critical_peaks_of_rule R (l, r)" and
      s: "s = cs \<cdot> \<delta>" and
      u: "u = cu \<cdot> \<delta>" and
      t: "t = ct \<cdot> \<gamma>" and
      subst_R: "\<forall>x. (\<delta> x, \<gamma> x) \<in> par_rstep R" and
      subst_eq: "\<And> x. x \<notin> vars_mctxt C \<Longrightarrow> \<delta> x = \<gamma> x" and
      C: "C \<noteq> MHole" 
      by auto
    show ?thesis
    proof (cases "ct = cu")
      case True
      show ?thesis unfolding t u True using subst_R
        by (intro exI[of _ "cu \<cdot> \<gamma>"], 
            auto simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
    next
      case False
      let ?V = "vars_mctxt C" 
      from False C crit lr have "(C, ct, cs, cu) \<in> nonroot_parallel_peaks R S" 
        unfolding nonroot_parallel_peaks_def by auto
      from parallel_crit_pairs[unfolded toyama_pcp_condition_def, rule_format, OF this, unfolded split]
      obtain v
        where ctv: "(ct, v) \<in> (rstep S)\<^sup>*" and
          cuv: "(cu, v) \<in> par_rstep_var_restr R ?V"
        by auto
      from merge_par_rstep_var_restr[OF _ cuv subst_eq] subst_R
      have merge: "(cu \<cdot> \<delta>, v \<cdot> \<gamma>) \<in> par_rstep R" by auto
      show ?thesis unfolding t u
        by (rule exI, rule conjI[OF _ merge], insert ctv, auto simp: rsteps_closed_subst)
    qed
  qed
qed


lemma parallel_critical_pair_condition_main: assumes 
  par_step: "(s,t) \<in> par_rstep R" 
  and step: "(s,u) \<in> rstep S"
shows "\<exists> v. (t,v) \<in> (rstep S)^* \<and> (u,v) \<in> par_rstep R" 
proof -
  from rstepE[OF step] obtain C \<sigma> l r where lr: "(l,r) \<in> S" and su: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" "u = C \<langle> r \<cdot> \<sigma> \<rangle>" 
    by metis
  from par_step show ?thesis unfolding su(2) using su(1)
  proof (induct arbitrary: C rule: par_rstep.induct)
    case (root_step s t \<tau>)
    let ?p = "hole_pos C" 
    show ?case
    proof (cases "?p \<in> fun_poss s")
      case False
        (* rewrite in substitution *)
      from root_step have id: "s \<cdot> \<tau> = C\<langle>l \<cdot> \<sigma>\<rangle>" and st: "(s,t) \<in> R" by auto
      with ll have lin_s: "linear_term s" unfolding left_linear_trs_def by auto
      have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep S" using lr by auto
      from rewrite_in_subst[OF lin_s id False ctxt_closed_rstep this]
      obtain \<tau>' x where main: "s \<cdot> \<tau>' = C\<langle>r \<cdot> \<sigma>\<rangle>" "x \<in> vars_term s" "(\<tau> x, \<tau>' x) \<in> rstep S" "\<And> y. y \<noteq> x \<longrightarrow> \<tau> y = \<tau>' y" 
        by blast
      show ?thesis unfolding main(1)[symmetric] 
      proof (intro exI[of _ "t \<cdot> \<tau>'"] conjI)
        show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> par_rstep R" using st by auto
        have "(\<tau> y, \<tau>' y) \<in> (rstep S)\<^sup>*" for y using main(3) main(4)[of y] by auto
        thus "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep S)\<^sup>*" by (rule substs_rsteps)
      qed
    next
      case True
        (* ordinary critical pair *)
      from root_step have id: "s \<cdot> \<tau> = C\<langle>l \<cdot> \<sigma>\<rangle>" and st: "(s,t) \<in> R" by auto
      from True have p: "?p \<in> poss s" by (simp add: fun_poss_imp_poss)
      from ctxt_supt_id [OF p] obtain D where Ds: "D\<langle>s |_ ?p\<rangle> = s"
        and D: "D = ctxt_of_pos_term ?p s" by blast
      from arg_cong [OF Ds, of "\<lambda> t. t \<cdot> \<tau>"]
      have "(D \<cdot>\<^sub>c \<tau>)\<langle>(s |_ ?p) \<cdot> \<tau>\<rangle> = C\<langle>l \<cdot> \<sigma>\<rangle>" unfolding id by simp
      from id have "s \<cdot> \<tau> |_ ?p = l \<cdot> \<sigma>" by simp
      also have "s \<cdot> \<tau> |_ ?p = s |_ ?p \<cdot> \<tau>" using True
        by (simp add: fun_poss_imp_poss)
      finally have unif: "s |_ ?p \<cdot> \<tau> = l \<cdot> \<sigma>" by auto
      let ren2 = "renaming2 ren" 
      from mgu_vd_complete[OF unif, of ren2]
      obtain \<mu>1 \<mu>2 \<delta> where mgu_res: "mgu_vd ren2 (s |_ ?p) l = Some (\<mu>1, \<mu>2)" 
        and mgu: "\<tau> = \<mu>1 \<circ>\<^sub>s \<delta>" "\<sigma> = \<mu>2 \<circ>\<^sub>s \<delta>" "s |_ ?p \<cdot> \<mu>1 = l \<cdot> \<mu>2" by auto
      have cp: "(D = \<box>, (D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle>, t \<cdot> \<mu>1) \<in> critical_pairs ren2 R S" 
        unfolding critical_pairs_def
      proof (standard, intro exI conjI)
        show "(s,t) \<in> R" by fact
        show "(l,r) \<in> S" by fact
        show "s = D\<langle>s |_ ?p\<rangle>" unfolding Ds ..
        show "is_Fun (s |_ ?p)" using True
          by (metis DiffE is_Var_def p poss_simps(4) var_poss_iff)
        show "mgu_vd ren2 (s |_ ?p) l = Some (\<mu>1, \<mu>2)" by fact
      qed auto
      have "\<exists> w. (t \<cdot> \<mu>1, w) \<in> (rstep S)\<^sup>* \<and> ((D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle>, w) \<in> par_rstep R" 
      proof (cases "t \<cdot> \<mu>1 = (D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle>")
        case False
        have "((D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle>, t \<cdot> \<mu>1) \<in> nontriv_ordinary_cps R S" 
          unfolding nontriv_ordinary_cps_def using cp False by force
        from crit_pairs[unfolded cp_parstep_steps_joinable_def, rule_format, OF this]
        show ?thesis by blast
      qed auto
      then obtain w where steps: "(t \<cdot> \<mu>1, w) \<in> (rstep S)\<^sup>*" and pstep: "((D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle>, w) \<in> par_rstep R" by auto      
      let ?v = "w \<cdot> \<delta>" 
      show ?thesis unfolding mgu 
      proof (intro exI[of _ ?v] conjI)
        show "(t \<cdot> \<mu>1 \<circ>\<^sub>s \<delta>, w \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" using steps 
          unfolding subst_subst_compose by (rule rsteps_closed_subst)
        have "D \<cdot>\<^sub>c \<mu>1 \<cdot>\<^sub>c \<delta> = C" unfolding D using hole_pos_id_ctxt[of C] p mgu
          by (metis ctxt_compose_subst_compose_distrib ctxt_of_pos_term_subst id)
        hence "(D \<cdot>\<^sub>c \<mu>1)\<langle>r \<cdot> \<mu>2\<rangle> \<cdot> \<delta> = C\<langle>r \<cdot> \<mu>2 \<circ>\<^sub>s \<delta>\<rangle>" using mgu p by auto
        thus "(C\<langle>r \<cdot> \<mu>2 \<circ>\<^sub>s \<delta>\<rangle>, w \<cdot> \<delta>) \<in> par_rstep R" 
          using subst_closed_par_rstep[OF pstep, of \<delta>] by simp
      qed
    qed
  next
    case (par_step_fun ts ss f)
    show ?case
    proof (cases C)
      case Hole
        (* parallel critical pair *)
      from par_rstep_mctxt_funI_ex[OF par_step_fun(1)[unfolded par_rstep_par_rstep_mctxt_conv] par_step_fun(3), of f]
      obtain D infos where pstep: "(Fun f ss, Fun f ts) \<in> par_rstep_mctxt (R) D infos" 
        and D: "D \<noteq> MHole" by auto
      from par_step_fun(4) have rstep: "(Fun f ss, C \<langle>r \<cdot> \<sigma>\<rangle>) \<in> rrstep S" using lr Hole by auto      
      show ?thesis 
        by (rule par_step_single_root_step_join[OF pstep rstep D])
    next
      case (More g bef D aft)
        (* apply induction on one argument, no steps for the others *)
      from par_step_fun(4) More
      have C: "C = More f bef D aft" and ss: "ss = bef @ D\<langle>l \<cdot> \<sigma>\<rangle> # aft" by auto
      let ?n = "length bef" 
      from arg_cong[OF ss, of length] have len: "length ss = Suc (?n + length aft)" by auto
          (* induction case *)
      have n: "?n < length ts" using len par_step_fun(3) by auto
      from par_step_fun(1)[OF this] have step: "(ss ! ?n, ts ! ?n) \<in> par_rstep R" .
      from arg_cong[OF ss, of "\<lambda> ss. ss ! ?n"] have "ss ! ?n = D \<langle>l \<cdot> \<sigma>\<rangle>" by simp
      from par_step_fun(2)[OF n this] obtain vn where
        vn: "(ts ! ?n, vn) \<in> (rstep S)\<^sup>*" "(D\<langle>r \<cdot> \<sigma>\<rangle>, vn) \<in> par_rstep R" 
        by auto
          (* assemble witness *)
      let ?v = "Fun f (ts [?n := vn])"       
      have id: "C\<langle>r \<cdot> \<sigma>\<rangle> = Fun f (ss [?n := D\<langle>r \<cdot> \<sigma>\<rangle>])" unfolding C ss by simp
      show ?thesis unfolding id
      proof (intro exI[of _ ?v] conjI)
        show "(Fun f (ss[?n := D\<langle>r \<cdot> \<sigma>\<rangle>]), ?v) \<in> par_rstep R" 
        proof (intro par_rstep.par_step_fun, insert n vn(2) par_step_fun(3), goal_cases)
          case (1 i)
          thus ?case using par_step_fun(1)[of i] by (cases "i = ?n", auto)
        qed auto
        show "(Fun f ts, ?v) \<in> (rstep S)\<^sup>*" using vn(1) n
          by (metis (no_types, lifting) args_rsteps_imp_rsteps length_list_update nth_list_update_eq nth_list_update_neq rtrancl.rtrancl_refl) 
      qed
    qed
  next
    case (par_step_var x)
    show ?case unfolding par_step_var
      by (intro exI[of _ "C\<langle>r \<cdot> \<sigma>\<rangle>"], insert lr, auto)
  qed
qed
end (* left-linear assumption, etc. *)

theorem toyama_parallel_critical_pair_condition_commute: 
  assumes "left_linear_trs R" "left_linear_trs S"  
    and "cp_parstep_steps_joinable R S" 
    and "toyama_pcp_condition R S" 
  shows "commute (rstep R) (rstep S)" 
proof -
  have "strongly_commute (rstep S) (par_rstep R)" 
    unfolding strongly_commute_def
    using parallel_critical_pair_condition_main[OF assms] by blast
  hence "commute (rstep S) (par_rstep R)" 
    by (rule strongly_commute_imp_commute)
  hence "commute (rstep S) (rstep R)" 
    unfolding commute_def par_rsteps_rsteps by simp
  thus ?thesis
    by (simp add: commuteE commuteI)
qed

text \<open>The original result of Toyama is an immediate consequence
  of the commutation result.\<close>

corollary toyama_parallel_critical_pair_condition_CR: assumes
  "left_linear_trs R"
  "cp_parstep_steps_joinable R R" "toyama_pcp_condition R R" 
shows "CR (rstep R)" 
proof -
  from toyama_parallel_critical_pair_condition_commute[OF assms(1,1-3)]
  have "commute (rstep R) (rstep R)" .
  thus ?thesis
    by (simp add: CR_iff_self_commute)
qed

text \<open>The Gramlich result is also trivially included.\<close>

corollary gramlich_parallel_critical_pair_condition_commute:
  assumes "left_linear_trs R" "left_linear_trs S"
  and "cp_parstep_steps_joinable R S"
  and "gramlich_pcp_condition R S"
  shows "commute (rstep R) (rstep S)" 
  by (intro toyama_parallel_critical_pair_condition_commute gramlich_implies_toyama assms)
  
corollary gramlich_parallel_critical_pair_condition_CR: assumes
  "left_linear_trs R"
  "cp_parstep_steps_joinable R R" "gramlich_pcp_condition R R" 
shows "CR (rstep R)" 
  by (rule toyama_parallel_critical_pair_condition_CR[OF assms(1,2) gramlich_implies_toyama[OF assms(3)]])

text \<open>Note that there is no variable condition on the rewrite systems!\<close>




subsection \<open>Rule Labeling with PCPs\<close>

definition critical_parallel_rule_peaks :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> (('f,'v)mctxt \<times> ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)term \<times> nat \<times> nat)set" where
  "critical_parallel_rule_peaks R S \<phi> \<psi> = { (C,t,s,u,max_list (map \<phi> rls), \<psi> lr) | lr C t s u rls.
     lr \<in> S \<and> (C,t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr \<and> t \<noteq> u}" 

definition RS_conv :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f,'v)trs" where
  "RS_conv R S \<phi> \<psi> k = {lr . lr \<in> R \<and> \<phi> lr < k}^-1 \<union> {lr . lr \<in> S \<and> \<psi> lr < k}" 

definition R_le :: "('f,'v)trs \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f,'v)trs" where
  "R_le R \<phi> k = {lr . lr \<in> R \<and> \<phi> lr \<le> k}"

datatype Lab_filter = No_Lab_Filter | Zero_Zero_Filter

fun lab_filter :: "Lab_filter \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lab_filter No_Lab_Filter k m = True" 
| "lab_filter Zero_Zero_Filter k m = (k \<noteq> 0 \<or> m \<noteq> 0)" 

definition is_decreasing where
  "is_decreasing R S \<phi> \<psi> lf = (\<forall> C t s u k m. (C, t, s, u, k, m) \<in> critical_parallel_rule_peaks R S \<phi> \<psi> \<longrightarrow>
      lab_filter lf k m \<longrightarrow>
      (t,u) \<in> 
         (rstep (RS_conv R S \<phi> \<psi> k))^* O 
         par_rstep (R_le S \<psi> m) O 
         (rstep (RS_conv R S \<phi> \<psi> (max k m)))^* O
         (par_rstep_var_restr (R_le R \<phi> k) (vars_mctxt C))^-1 O
         (rstep (RS_conv R S \<phi> \<psi> m))^*)" 

text \<open>Proof for handling root-steps in Theorem 24 and 31, FSCD 2022\<close>
lemma is_decreasing_root_overlap_joinable:
  assumes ll: "left_linear_trs S" 
    and decr: "is_decreasing R S \<phi> \<psi> lf" 
    and par_step: "(s,t) \<in> par_rstep (R_le R \<phi> k)" 
    and step: "(s,u) \<in> rrstep (R_le S \<psi> m)"
    and lf: "lab_filter lf k m" 
  shows "(t,u) \<in> 
   (rstep (RS_conv R S \<phi> \<psi> k))^* O 
   par_rstep (R_le S \<psi> m) O 
   (rstep (RS_conv R S \<phi> \<psi> (max k m)))^* O 
   (par_rstep (R_le R \<phi> k))^-1 O 
   (rstep (RS_conv R S \<phi> \<psi> m))^*" 
proof -
  let ?S = "R_le S \<psi> m" 
  let ?R = "R_le R \<phi> k" 
  let ?RS = "RS_conv R S \<phi> \<psi>" 
  have R_le: "?R \<subseteq> R" unfolding R_le_def by auto
  from rrstepE[OF step] obtain l r \<sigma> where 
    lr: "(l,r) \<in> ?S" and s: "s = l \<cdot> \<sigma>" and u: "u = r \<cdot> \<sigma>" by auto  
  from lr ll have l: "linear_term l" unfolding left_linear_trs_def R_le_def by auto
  from par_step[unfolded par_rstep_par_rstep_mctxt_conv] obtain C infos
    where "(s, t) \<in> par_rstep_mctxt ?R C infos" by auto
  from parallel_critical_peaks_of_rule[OF this s l u R_le]
  have "(\<exists>v. (t, v) \<in> rrstep {(l, r)} \<and> (u, v) \<in> par_rstep ?R) \<or>
    (\<exists>C cs ct cu rls \<gamma> \<delta> infos.
      (C, ct, cs, cu, rls) \<in> parallel_critical_peaks_of_rule R (l, r) \<and>
      s = cs \<cdot> \<delta> \<and>
      u = cu \<cdot> \<delta> \<and>
      t = ct \<cdot> \<gamma> \<and>
      (cs, ct) \<in> par_rstep_mctxt (set rls) C infos \<and>
      (cs, cu) \<in> rrstep {(l, r)} \<and>
      set rls \<subseteq> ?R \<and>
      (\<forall>x. (\<delta> x, \<gamma> x) \<in> par_rstep ?R) \<and>
      (\<forall>x. x \<notin> vars_mctxt C \<longrightarrow> \<delta> x = \<gamma> x))" (is "?triv \<or> ?crit_pair")
    by blast
  thus ?thesis
  proof 
    assume ?triv
    then obtain v where "(t, v) \<in> rrstep {(l, r)}" and uv: "(u, v) \<in> par_rstep ?R" 
      by auto
    from this lr have "(t,v) \<in> rstep ?S"
      by (metis rrstepE rrstepI rrstep_imp_rstep singletonD)
    hence tv: "(t,v) \<in> par_rstep ?S"
      using rstep_par_rstep by blast
    show ?thesis using tv uv by blast
  next
    assume ?crit_pair
    then obtain C cs ct cu rls \<gamma> \<delta> infos where
      crit: "(C, ct, cs, cu, rls) \<in> parallel_critical_peaks_of_rule R (l, r)" and
      s: "s = cs \<cdot> \<delta>" and
      u: "u = cu \<cdot> \<delta>" and
      t: "t = ct \<cdot> \<gamma>" and
      cst: "(cs, ct) \<in> par_rstep_mctxt (set rls) C infos" and 
      csu: "(cs, cu) \<in> rrstep {(l, r)}" and
      rls: "set rls \<subseteq> ?R" and
      subst_R: "\<forall>x. (\<delta> x, \<gamma> x) \<in> par_rstep ?R" and
      subst_eq: "\<And> x. x \<notin> vars_mctxt C \<Longrightarrow> \<delta> x = \<gamma> x"      
      by auto
    let ?V = "vars_mctxt C" 
    show ?thesis
    proof (cases "ct = cu")
      case True
      have step: "(cu \<cdot> \<delta>, cu \<cdot> \<gamma>) \<in> par_rstep ?R" using subst_R
        by (auto simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
      show ?thesis unfolding t u True using step by auto
    next
      case False
      define k' where "k' = max_list (map \<phi> rls)" 
      define m' where "m' = \<psi> (l,r)" 
      have m': "m' \<le> m" using lr unfolding m'_def R_le_def by auto
      have k': "k' \<le> k" using rls unfolding k'_def R_le_def 
        by (intro max_list_leI, auto)
      from m' k' have subTrs: 
        "R_le R \<phi> k' \<subseteq> ?R"
        "R_le S \<psi> m' \<subseteq> ?S"
        "?RS k' \<subseteq> ?RS k"  
        "?RS m' \<subseteq> ?RS m" 
        "?RS (max k' m') \<subseteq> ?RS (max k m)" 
        unfolding RS_conv_def R_le_def R_le by auto
      from False crit lr[unfolded R_le_def] have crit: "(C, ct, cs, cu, k', m') \<in> critical_parallel_rule_peaks R S \<phi> \<psi>" 
        unfolding critical_parallel_rule_peaks_def k'_def m'_def by auto
      show ?thesis
      proof (cases "lab_filter lf k' m'")
        case True
        from decr[unfolded is_decreasing_def, rule_format, OF crit this]
        obtain v where
          ctv: "(ct, v) \<in> (rstep (?RS k'))^* O par_rstep (R_le S \<psi> m') O (rstep (?RS (max k' m')))^*" 
          and vcu: "(v, cu) \<in> (par_rstep_var_restr (R_le R \<phi> k') ?V)^-1 O (rstep (?RS m'))\<^sup>*" 
          by blast 
        have ctv: "(ct, v) \<in> (rstep (?RS k))^* O par_rstep ?S O (rstep (?RS (max k m)))^*" 
          apply (rule set_mp[OF _ ctv])
          using rstep_mono[OF subTrs(3)] par_rstep_mono[OF subTrs(2)] rstep_mono[OF subTrs(5)]
          by (meson relcomp_mono rtrancl_mono)
        have vcu: "(v, cu) \<in> (par_rstep_var_restr ?R ?V)^-1 O (rstep (?RS m))\<^sup>*" 
          apply (rule set_mp[OF _ vcu])
          unfolding rstep_converse
          using rstep_mono[OF subTrs(4)] par_rstep_var_restr_mono[OF subTrs(1)]
          by (auto simp add: relcomp_mono rtrancl_mono)
        let ?A = "(par_rstep ?R)^-1 O (rstep (?RS m))\<^sup>*" 
        {
          from vcu obtain w where wcu: "(w, cu) \<in> (rstep (?RS m))\<^sup>*" 
            and wv: "(w,v) \<in> par_rstep_var_restr ?R ?V" by auto
          from rsteps_closed_subst[OF wcu]
          have cuw: "(w \<cdot> \<delta>, cu \<cdot> \<delta>) \<in> (rstep ((?RS m)))\<^sup>*" .
          from merge_par_rstep_var_restr[OF subst_R[rule_format] wv subst_eq]
          have wv: "(v \<cdot> \<gamma>, w \<cdot> \<delta>) \<in> (par_rstep ?R)^-1" by auto
          from cuw wv have "(v \<cdot> \<gamma>, cu \<cdot> \<delta>) \<in> ?A" 
            by auto
        } note vcu = this
        from ctv have ctv: "(ct \<cdot> \<gamma>, v \<cdot> \<gamma>) \<in> (rstep (?RS k))^* O par_rstep ?S O (rstep (?RS (max k m)))^*"
          (is "_ \<in> ?B")
          using rstep_subst[of _ _ "?RS k" \<gamma> for k] subst_closed_par_rstep[of _ _ ?S \<gamma>]
          by (meson subst.closedD subst.closedI subst.closed_comp subst.closed_rtrancl subst_closed_par_rstep subst_closed_rstep)
        from ctv vcu have "(ct \<cdot> \<gamma>, cu \<cdot> \<delta>) \<in> ?B O ?A" by blast
        thus ?thesis unfolding t u by blast
      next
        (* this case is missing in the FSCD-paper-proof *)
        assume "\<not> lab_filter lf k' m'" 
        with lf have km': "k' < max k m" "m' < max k m"
          by (cases lf, auto)+
        let ?RM = "?RS (max k m)" 
        {
          fix rl
          assume rl: "rl \<in> set rls" 
          hence "\<phi> rl \<le> k'" unfolding k'_def using max_list[of _ "map \<phi> rls"] by simp
          also have "\<dots> < max k m" by fact
          finally have "rl \<in> ?RM^-1" using set_mp[OF rls rl] unfolding R_le_def RS_conv_def
            by (simp add: converse_Un)
        }
        hence rlsRM: "set rls \<subseteq> ?RM^-1" by blast
        from subst_R have "(u, cu \<cdot> \<gamma>) \<in> par_rstep ?R" unfolding u
          by (simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
        hence cuu: "(cu \<cdot> \<gamma>, u) \<in> (par_rstep ?R)^-1" by simp
        from cst have "(cs, ct) \<in> par_rstep (set rls)"
          using par_rstep_par_rstep_mctxt_conv by blast
        hence "(cs \<cdot> \<gamma>, ct \<cdot> \<gamma>) \<in> par_rstep (set rls)" by (rule subst_closed_par_rstep)
        hence "(cs \<cdot> \<gamma>, ct \<cdot> \<gamma>) \<in> par_rstep (?RM^-1)" 
          using rlsRM par_rstep_mono by blast
        hence "(cs \<cdot> \<gamma>, ct \<cdot> \<gamma>) \<in> (rstep (?RM^-1))^*" using par_rsteps_rsteps by blast
        hence tcs: "(t, cs \<cdot> \<gamma>) \<in> (rstep ?RM)^*" unfolding rstep_converse t by (metis rtrancl_converseD)
        from csu have "(cs,cu) \<in> rstep {(l,r)}" by (rule rrstep_imp_rstep)
        also have "\<dots> \<subseteq> rstep ?RM" 
          by (rule rstep_mono, insert km' lr, auto simp: m'_def R_le_def RS_conv_def)
        finally have csu: "(cs \<cdot> \<gamma>, cu \<cdot> \<gamma>) \<in> rstep ?RM" by blast
        from relcompI[OF tcs relcompI[OF csu cuu]] 
        have tu: "(t, u) \<in> par_rstep ?S O (rstep ?RM)\<^sup>* O (rstep ?RM)^* O (par_rstep ?R)\<inverse>" by auto
        show ?thesis 
          by (rule set_mp[OF _ tu], regexp)
      qed
    qed
  qed
qed

lemma par_rstep_as_union: fixes \<phi> :: "_ \<Rightarrow> nat" 
  shows "(\<Union>n. par_rstep {lr \<in> R. \<phi> lr \<le> n}) = par_rstep R" 
proof
  show "(\<Union>n. par_rstep {lr \<in> R. \<phi> lr \<le> n}) \<subseteq> par_rstep R" 
    using par_rstep_mono[of "{lr \<in> R. \<phi> lr \<le> n}" R for n] by auto
  {
    fix s t
    assume "(s,t) \<in> par_rstep R" 
    from this[unfolded par_rstep_par_rstep_mctxt_conv]
    obtain C infos where step: "(s,t) \<in> par_rstep_mctxt R C infos" by auto
    define n where "n = max_list (map \<phi> (map par_rule infos))" 
    have "(s,t) \<in> par_rstep_mctxt {lr \<in> R. \<phi> lr \<le> n} C infos" 
      using step unfolding par_rstep_mctxt_def n_def par_cond_def
      by (auto simp: o_def max_list)
    hence "(s,t) \<in> par_rstep {lr \<in> R. \<phi> lr \<le> n}" 
      unfolding par_rstep_par_rstep_mctxt_conv by blast
    hence "(s,t) \<in> (\<Union>n. par_rstep {lr \<in> R. \<phi> lr \<le> n})"  by blast
  }
  thus "(\<Union>n. par_rstep {lr \<in> R. \<phi> lr \<le> n}) \<supseteq> par_rstep R" by force
qed

lemma union_of_par_rsteps: fixes \<phi> :: "_ \<Rightarrow> nat"
  assumes k: "k > 0" 
  shows "(\<Union>x\<in>{x. x < k}. par_rstep {lr \<in> R. \<phi> lr \<le> x}) = par_rstep {lr \<in> R. \<phi> lr < k}" (is "?L = ?R")
proof 
  show "?L \<subseteq> ?R" 
    by (force simp: par_rstep_mctxt_def par_cond_def par_rstep_par_rstep_mctxt_conv)
  have "par_rstep {lr \<in> R. \<phi> lr < k} = par_rstep {lr \<in> R. \<phi> lr \<le> k - 1}" using k 
    by (intro arg_cong[of _ _ par_rstep], cases k, auto) 
  moreover have "k - 1 \<in> {x. x < k}" using k by auto
  ultimately show "?R \<subseteq> ?L" by blast
qed

definition is_decreasing_trs where
  "is_decreasing_trs R \<phi> = (\<forall>C s peak t k m.
    (C, s, peak, t, k, m) \<in> critical_parallel_rule_peaks R R \<phi> \<phi> \<longrightarrow>
      (s, t)
        \<in> (rstep {lr \<in> R. \<phi> lr < k})\<^sup>\<leftrightarrow>\<^sup>* O
           par_rstep (R_le R \<phi> m) O
           (rstep {lr \<in> R. \<phi> lr < max k m})\<^sup>\<leftrightarrow>\<^sup>* O
           (par_rstep_var_restr (R_le R \<phi> k) (vars_mctxt C))^-1 O
           (rstep {lr \<in> R. \<phi> lr < m})\<^sup>\<leftrightarrow>\<^sup>*)" 

lemma RS_conv_conversion: "(rstep (RS_conv R R \<phi> \<phi> m))^* = (rstep {lr \<in> R. \<phi> lr < m})\<^sup>\<leftrightarrow>\<^sup>*" for m
  unfolding RS_conv_def
  by (simp add: conversion_def rstep_simps(5) sup_commute)

lemma is_decreasing_trs: "is_decreasing_trs R \<phi> = is_decreasing R R \<phi> \<phi> No_Lab_Filter"
proof -
  have [simp]: "(RS_conv R R \<phi> \<phi> m)\<inverse> = RS_conv R R \<phi> \<phi> m" for m
    unfolding RS_conv_def by auto
  show ?thesis
    unfolding is_decreasing_trs_def is_decreasing_def RS_conv_conversion[symmetric] R_le_def by auto
qed


lemma conversion''_mono: "(\<And> i. L i \<subseteq> L' i) \<Longrightarrow> (\<And> i. R i \<subseteq> R' i) \<Longrightarrow> 
  conversion'' L R M \<subseteq> conversion'' L' R' M" 
  by (intro rtrancl_mono Un_mono; (unfold converse_mono)?; blast)

text \<open>Theorem 20 in FSCD 2022 Shintani Hirokawa\<close>
theorem dd_minimum_commute:
  fixes bot
  assumes "wf r" and "trans r"
    and least: "\<And> x. x = bot \<or> (bot,x) \<in> r" 
    and comm: "commute (L bot) (R bot)" 
    and pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow> (a,b) \<noteq> (bot,bot) \<Longrightarrow>
    (t, u) \<in> conversion'' L R (under r a) O (R b)\<^sup>= O conversion'' L R (under r a \<union> under r b) O
      ((L a)\<inverse>)\<^sup>= O conversion'' L R (under r b)"
  shows "commute (\<Union>i. L i) (\<Union>i. R i)"
proof -
  define prime where "prime L a = (if a = bot then (L a)^* else L a)" for L :: "'a \<Rightarrow> 'b rel" and a
  define L' where "L' = prime L" 
  define R' where "R' = prime R"
  note defs = L'_def prime_def R'_def
  have under_bot: "under r bot = {}" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain b where "b \<in> under r bot" by auto
    hence "(b,bot) \<in> r" unfolding under_def by auto
    with least[of b] have "(bot,bot) \<in> r O r" by auto
    hence "\<not> wf (r O r)" by (meson wf_irrefl)
    with \<open>wf r\<close> show False
      using wf_comp_self by blast
  qed
  have "commute (\<Union>i. L' i) (\<Union>i. R' i)" 
  proof (rule dd_commute[OF assms(1-2)])
    {
      fix a b s t u and L R L' R' :: "'a \<Rightarrow> 'b rel" 
      assume "L' = prime L" "R' = prime R" 
      note defs = this prime_def
      assume stu: "(s, t) \<in> L' a" "(s, u) \<in> R' b" 
      assume abot: "a = bot" "b \<noteq> bot" 
      assume pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow> (a,b) \<noteq> (bot,bot) \<Longrightarrow>
    (t, u) \<in> conversion'' L R (under r a) O (R b)\<^sup>= O conversion'' L R (under r a \<union> under r b) O
      ((L a)\<inverse>)\<^sup>= O conversion'' L R (under r b)" 
      have "(t, u)
       \<in> conversion'' L' R' (under r a) O (R' b)\<^sup>= O
          conversion'' L' R' (under r a \<union> under r b) O ((L' a)\<inverse>)\<^sup>= O conversion'' L' R' (under r b)" 
      proof -
        from abot have ab: "(a,b) \<noteq> (bot,bot)" by auto
        have under: "under r a = {}" unfolding abot under_bot by simp
        have id: "conversion'' L R {} = Id" by simp
        have id2: "Id O X = X" for X :: "'b rel" by auto
        have id3: "conversion'' L R (under r b) = conversion'' L R (under r b) O conversion'' L R (under r b) O conversion'' L R (under r b)" 
          by auto
        from least[of b] abot have a_under_b: "a \<in> under r b" unfolding under_def by auto
        {
          fix t u
          assume "(t,u) \<in> (L a)^-1 O R b" 
          then obtain s where *: "(s,t) \<in> L a" "(s,u) \<in> R b" by auto
          have "(t, u) \<in> (R b)\<^sup>= O conversion'' L R (under r b)"
            by (subst id3)
              (rule set_mp[OF _ pk[OF * ab, unfolded under id id2]], intro relcomp_mono subset_refl, force, insert a_under_b, blast)
        }
        hence one: "(L a)^-1 O R b \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b)" by blast
        have "((L a)^-1)^^n O R b \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b)" for n
        proof (induct n)
          case (Suc n)
          have "(L a)\<inverse> ^^ Suc n O R b = (L a)\<inverse> ^^ n O (L a)\<inverse> O R b" by auto
          also have "\<dots> \<subseteq> (L a)\<inverse> ^^ n O (R b)\<^sup>= O conversion'' L R (under r b)" using one by blast
          also have "\<dots> \<subseteq> (L a)\<inverse> ^^ n O R b O conversion'' L R (under r b) \<union> (L a)\<inverse> ^^ n O conversion'' L R (under r b)" 
            by auto
          also have "\<dots> \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b) O conversion'' L R (under r b) \<union> (L a)\<inverse> ^^ n O conversion'' L R (under r b)" 
            using Suc by blast
          also have "\<dots> = (R b)\<^sup>= O conversion'' L R (under r b) \<union> (L a)\<inverse> ^^ n O conversion'' L R (under r b)" 
            by auto
          also have "\<dots> \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b) \<union> ((L a)\<inverse>) ^* O conversion'' L R (under r b)" 
            by (intro Un_mono relcomp_mono subset_refl, auto intro: relpow_imp_rtrancl)
          also have "\<dots> \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b) \<union> conversion'' L R (under r b) O conversion'' L R (under r b)"
            by (intro Un_mono relcomp_mono subset_refl rtrancl_mono, insert a_under_b, auto)
          finally show ?case by auto
        qed auto
        hence main: "((L a)^-1)^* O R b \<subseteq> (R b)\<^sup>= O conversion'' L R (under r b)" 
          by blast
        from stu[unfolded defs] abot have tu: "(t,u) \<in> ((L a)^-1)^* O R b" 
          by (auto simp: rtrancl_converse)
        have Rb: "R b = R' b" using abot unfolding defs by auto
        have conv: "conversion'' L R (under r b) = conversion'' L' R' (under r b)" 
        proof
          show "conversion'' L R (under r b) \<subseteq> conversion'' L' R' (under r b)" 
            unfolding defs
            by (intro rtrancl_mono, auto)
          have "conversion'' L' R' (under r b) \<subseteq> (conversion'' L R (under r b))^*" 
            unfolding defs
            apply (intro rtrancl_mono)
            apply (rule subset_trans[OF _ rtrancl_Un_subset])
            apply (unfold rtrancl_converse, rule Un_mono; (unfold converse_mono)?)
            by (smt (verit) SUP_least SUP_upper rtrancl_mono rtrancl_mono_rightI)+
          thus "conversion'' L' R' (under r b) \<subseteq> (conversion'' L R (under r b))" by auto
        qed
        show ?thesis
          apply (rule set_mp[OF _ tu])
          apply (rule subset_trans[OF main])
          unfolding Rb conv by blast
      qed
    } note difficult_case = this
    fix a b s t u
    assume stu: "(s, t) \<in> L' a" "(s, u) \<in> R' b" 
    consider (bot) "a = bot" "b = bot" 
      | (abot) "a = bot" "b \<noteq> bot" 
      | (bbot) "b = bot" "a \<noteq> bot" 
      | (nobot) "a \<noteq> bot" "b \<noteq> bot" 
      by blast
    thus "(t, u)
       \<in> conversion'' L' R' (under r a) O (R' b)\<^sup>= O
          conversion'' L' R' (under r a \<union> under r b) O ((L' a)\<inverse>)\<^sup>= O conversion'' L' R' (under r b)" 
    proof cases
      case nobot
      from stu nobot 
      have *: "(s,t) \<in> L a" "(s,u) \<in> R b" "(a,b) \<noteq> (bot,bot)" unfolding defs by auto      
      show ?thesis
        by (rule set_mp[OF _ pk[OF *]], intro relcomp_mono conversion''_mono, auto simp: defs)
    next
      case bot
      from stu[unfolded defs bot] 
      have stu: "(s,t) \<in> (L bot)^*" "(s,u) \<in> (R bot)^*" by auto
      have Lab: "L' a = (L bot)^*" "R' b = (R bot)^*" unfolding bot defs by auto
      from comm stu obtain v where "(t,v) \<in> R' b" "(u,v) \<in> L' a" unfolding Lab
        by (meson commuteE)
      thus ?thesis by blast
    next
      case abot
      show ?thesis
        by (rule difficult_case[OF L'_def R'_def stu abot pk])
    next
      case bbot
      have "(u, t) \<in> conversion'' R' L' (under r b) O (L' a)\<^sup>= O
       conversion'' R' L' (under r b \<union> under r a) O ((R' b)\<inverse>)\<^sup>= O conversion'' R' L' (under r a)"
        (is "_ \<in> ?Rel")
      proof (rule difficult_case[OF R'_def L'_def stu(2,1) bbot])
        fix a b s t u
        assume "(s, t) \<in> R a" "(s, u) \<in> L b" "(a, b) \<noteq> (bot, bot)" 
        from pk[OF this(2,1)] this(3)
        have tu: "(t, u) \<in> (conversion'' L R (under r b) O
          (R a)\<^sup>= O conversion'' L R (under r b \<union> under r a) O ((L b)\<inverse>)\<^sup>= O conversion'' L R (under r a))^-1" by auto
        show "(t, u) \<in> conversion'' R L (under r a) O (L b)\<^sup>= O
          conversion'' R L (under r a \<union> under r b) O ((R a)\<inverse>)\<^sup>= O conversion'' R L (under r b)" 
          apply (rule set_mp[OF _ tu])
          apply (unfold converse_inward O_assoc)
          by (intro relcomp_mono subset_refl rtrancl_mono, auto)
      qed
      hence tu: "(t,u) \<in> ?Rel^-1" by simp  
      show ?thesis 
        apply (rule set_mp[OF _ tu])
        apply (unfold converse_inward O_assoc)
        by (intro relcomp_mono subset_refl rtrancl_mono, auto)
    qed
  qed
  moreover have "(\<Union> (range (prime L)))^* = (\<Union> (range L))^*" for L
  proof
    show "(\<Union> (range L))\<^sup>* \<subseteq> (\<Union> (range (prime L)))\<^sup>*" unfolding defs
      by (intro rtrancl_mono, fastforce)
    have "(\<Union> (range (prime L)))\<^sup>* \<subseteq> ((\<Union> (range L))\<^sup>*)^*" unfolding defs
      apply (intro rtrancl_mono) 
      by (simp add: SUP_least SUP_upper rtrancl_mono rtrancl_mono_rightI)
    thus "(\<Union> (range (prime L)))\<^sup>* \<subseteq> ((\<Union> (range L))\<^sup>*)" by simp
  qed
  ultimately show ?thesis unfolding L'_def R'_def commute_def rtrancl_converse by auto
qed

text \<open>Main property for proving Theorem 31 of FSCD 2022,
  now arbitrary parallel-steps are considered\<close>
lemma is_decreasing_sufficient: assumes
  ll: "left_linear_trs R" 
  "left_linear_trs S" 
  and decr: "is_decreasing R S \<phi> \<psi> lf" 
  "is_decreasing S R \<psi> \<phi> lf" 
  and steps: "(s,t) \<in> par_rstep (R_le R \<phi> k)" 
  "(s,u) \<in> par_rstep (R_le S \<psi> m)" 
  and lf: "lab_filter lf k m" 
shows "(t, u)
    \<in> (rstep (RS_conv R S \<phi> \<psi> k))\<^sup>* O
       par_rstep (R_le S \<psi> m) O
       (rstep (RS_conv R S \<phi> \<psi> (max k m)))\<^sup>* O
       (par_rstep (R_le R \<phi> k))\<inverse> O (rstep (RS_conv R S \<phi> \<psi> m))\<^sup>*" 
proof -
  note defs = RS_conv_def R_le_def  

  let ?conv = "RS_conv R S \<phi> \<psi>"
  let ?merge = "\<lambda> t u. (t,u) \<in> (rstep (?conv k))^* O par_rstep (R_le S \<psi> m) O (rstep (?conv (max k m)))^*
        O (par_rstep (R_le R \<phi> k))^-1 O (rstep (?conv m))^*" 

  from steps show "?merge t u" 
  proof (induct s t arbitrary: u rule: par_rstep.induct)
    case (root_step s t \<sigma>)
    from root_step(1) have rrstep: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rrstep (R_le R \<phi> k)" 
      unfolding R_le_def by auto
    from lf have lf': "lab_filter lf m k" by (cases lf, auto)
    from root_step(2) have "(s \<cdot> \<sigma>, u) \<in> par_rstep (R_le S \<psi> m)" unfolding defs by auto
    from is_decreasing_root_overlap_joinable[OF ll(1) decr(2) this rrstep lf']
    have merge: "(t \<cdot> \<sigma>, u)
        \<in> ((rstep (RS_conv S R \<psi> \<phi> m))\<^sup>* O
          par_rstep (R_le R \<phi> k) O
          (rstep (RS_conv S R \<psi> \<phi> (max m k)))\<^sup>* O (par_rstep (R_le S \<psi> m))\<inverse> O (rstep (RS_conv S R \<psi> \<phi> k))\<^sup>*)^-1" 
      by auto
    show ?case 
      apply (rule set_mp[OF _ merge])
      apply (unfold defs converse_inward rstep_converse[symmetric])
      by (auto simp add: Un_commute max.commute)
  next
    case *: (par_step_fun ts ss f)
    define s where "s = Fun f ss" 
    define t where "t = Fun f ts" 
    have step: "(s, t) \<in> par_rstep (R_le R \<phi> k)" 
      using *(1,3) unfolding s_def t_def by blast
    from *(4)[folded s_def]
    show ?case unfolding t_def[symmetric]
    proof cases
      case (root_step l r \<sigma>)
      from root_step have rrstep: "(s, u) \<in> rrstep (R_le S \<psi> m)" by auto
      from is_decreasing_root_overlap_joinable[OF ll(2) decr(1) step rrstep lf]
      show "?merge t u" by simp
    next
      case **: (par_step_fun us ss' f')
      with s_def have "f' = f" "ss' = ss" by auto
      note ** = **(2-)[unfolded this]
      let ?n = "length ss" 
      from * ** have len: "length ts = ?n" "length us = ?n" by auto
      {
        fix i
        assume i: "i < ?n" 
        from **(2) len i have Sstep: "(ss ! i, us ! i) \<in> par_rstep (R_le S \<psi> m)" by auto
        from *(2)[OF _ Sstep] len i have IH: "?merge (ts ! i) (us ! i)" by auto
      } note IH = this
      show "?merge t u" unfolding t_def ** par_rstep_inverse[symmetric]
        by (intro conjI all_ctxt_closedD[of UNIV] 
            all_ctxt_closed_relcomp all_ctxt_closed_par_rstep all_ctxt_closed_rsteps)
          (insert IH, auto simp add: len par_rstep_inverse)
    next
      case (par_step_var x)
      hence "s = u" by auto
      with step have "(t, u) \<in> (par_rstep (R_le R \<phi> k))^-1" by auto
      then show "?merge t u" by auto
    qed
  qed blast
qed

text \<open>Theorem 31 in FSCD 2022 Shintani Hirokawa, generalized to commutation\<close>
theorem compositional_rule_labeling_pcp_comm: assumes 
  ll: "left_linear_trs R" "left_linear_trs S" 
  and decr: "is_decreasing R S \<phi> \<psi> Zero_Zero_Filter" 
  "is_decreasing S R \<psi> \<phi> Zero_Zero_Filter" 
  and comm: "commute (rstep (R_le R \<phi> 0)) (rstep (R_le S \<psi> 0))" 
shows "commute (rstep R) (rstep S)"
proof -
  note defs = RS_conv_def R_le_def 
  note decreasing = is_decreasing_sufficient[OF ll decr]

(* now we only need to connect this to an abstract result about decreasing diagrams *)
  define RR where "RR n = par_rstep { lr \<in> R. \<phi> lr \<le> n}" for n 
  define SS where "SS n = par_rstep { lr \<in> S. \<psi> lr \<le> n}" for n 
  have trans: "trans {(x, y). (x :: nat) < y}" unfolding trans_def by auto
  have under: "under {(x, y). x < y} (a :: nat) = {x. x < a}" for a unfolding under_def by auto 
  have max: "{x. x < k} \<union> {x. x < m} = {x. x < max k m}" for k m :: nat by auto
  {
    fix k
    have "conversion'' RR SS ({x. x < k}) = ((\<Union> x \<in>  {x. x < k}. RR x)\<inverse> \<union> (\<Union> x \<in> {x. x < k}. SS x))\<^sup>*"
      unfolding RR_def SS_def by (simp add: sup_commute)
    also have "\<dots> = (rstep (RS_conv R S \<phi> \<psi> k))\<^sup>*" 
    proof (cases "k > 0")
      case True
      show ?thesis unfolding RR_def SS_def union_of_par_rsteps[OF True] defs
        unfolding rstep_union[symmetric] par_rstep_inverse[symmetric] par_rsteps_union ..        
    next
      case False
      hence empty: "RS_conv R S \<phi> \<psi> k = {}" "{x. x < k} = {}" unfolding defs by auto
      show ?thesis unfolding empty by auto
    qed
    finally have "conversion'' RR SS {x. x < k} = (rstep (RS_conv R S \<phi> \<psi> k))\<^sup>*" .
  } note conversion_to_par_steps = this
  have zero: "x = 0 \<or> (0, x) \<in> {(x, y). x < y}" for x :: nat by auto
  have comm: "commute (RR 0) (SS 0)" using assms(5) unfolding RR_def SS_def defs 
    unfolding commute_def
    by (simp add: par_rsteps_rsteps rtrancl_converse)
  have "commute (\<Union> (range RR)) (\<Union> (range SS))" 
  proof (rule dd_minimum_commute[OF wf_less trans zero], rule comm, unfold under max)
    fix k m s t u
    assume st: "(s, t) \<in> RR k"
    assume su: "(s, u) \<in> SS m" 
    assume km: "(k,m) \<noteq> (0,0)" 
    from st have st: "(s, t) \<in> par_rstep (R_le R \<phi> k)" 
      unfolding RR_def R_le_def .
    from su have su: "(s, u) \<in> par_rstep (R_le S \<psi> m)"
      unfolding SS_def defs .    
    from decreasing[OF st su, unfolded par_rstep_conversion] km
    have merge: "(t, u) \<in> (rstep (RS_conv R S \<phi> \<psi> k))\<^sup>* O
     par_rstep (R_le S \<psi> m) O
     (rstep (RS_conv R S \<phi> \<psi> (max k m)))\<^sup>* O (par_rstep (R_le R \<phi> k))\<inverse> O (rstep (RS_conv R S \<phi> \<psi> m))\<^sup>*" 
      by simp
    have id1: "par_rstep (R_le S \<psi> m) = SS m" unfolding SS_def defs ..
    have id2: "par_rstep (R_le R \<phi> k) = RR k" unfolding RR_def defs ..
    show "(t, u)
       \<in> conversion'' RR SS {x. x < k} O (SS m)\<^sup>= O conversion'' RR SS ({x. x < max k m}) O
          ((RR k)\<inverse>)\<^sup>= O conversion'' RR SS ({x. x < m})" 
      using merge unfolding id1 id2 conversion_to_par_steps by auto
  qed
  also have "\<Union> (range RR) = par_rstep R" unfolding RR_def par_rstep_as_union ..
  also have "\<Union> (range SS) = par_rstep S" unfolding SS_def par_rstep_as_union ..
  finally have "commute (par_rstep R) (par_rstep S)" .
  hence "commute (rstep R) (rstep S)" 
    by (meson commute_between_imp_commute par_rstep_rsteps rstep_par_rstep)  
  thus ?thesis
    by (simp add: CR_iff_self_commute)
qed

lemma max_list_map: assumes "\<And> x y. max (f x) (f y) = f (max x y)" 
  shows "xs \<noteq> [] \<Longrightarrow> max_list (map f xs) = f (max_list xs)" 
proof (induct xs)
  case (Cons x xs)
  thus ?case using assms by (cases xs, auto)
qed auto



text \<open>This is a generalized version of Theorem 56 in Labelings for Decreasing Diagrams
  dealing with commutation. It is derived from the compositional version.\<close>
corollary rule_labeling_pcp_commutation: 
  assumes ll: "left_linear_trs R" "left_linear_trs S" 
    and decr: "is_decreasing R S \<phi> \<psi> No_Lab_Filter" "is_decreasing S R \<psi> \<phi> No_Lab_Filter" 
  shows "commute (rstep R) (rstep S)"
proof -
  define lift where "lift \<phi> rl = Suc (\<phi> rl)" for rl :: "('a,'v)rule" and \<phi>
  let ?\<phi> = "lift \<phi>" let ?\<psi> = "lift \<psi>" 
  show ?thesis
  proof (rule compositional_rule_labeling_pcp_comm[OF ll])
    show "commute (rstep (R_le R ?\<phi> 0)) (rstep (R_le S ?\<psi> 0))" 
      unfolding R_le_def lift_def by auto
    {
      fix R S :: "('a,'v)trs" and \<phi> \<psi>
      assume decr: "is_decreasing R S \<phi> \<psi> No_Lab_Filter" 
      have "is_decreasing R S (lift \<phi>) (lift \<psi>) Zero_Zero_Filter" unfolding is_decreasing_def
      proof (intro allI impI, goal_cases)
        case (1 C t s u k m)
        from 1(1)[unfolded critical_parallel_rule_peaks_def] obtain lr rls
          where *: "lr \<in> S" "(C, t, s, u, rls) \<in> parallel_critical_peaks_of_rule R lr" "t \<noteq> u" 
            and k: "k = max_list (map (lift \<phi>) rls)" and m: "m = lift \<psi> lr" by force
        from *(2)[unfolded parallel_critical_peaks_of_rule_def] have rls: "rls \<noteq> []" 
          by (cases lr, auto)
        have k: "k = Suc (max_list (map \<phi> rls))"
          unfolding k using max_list_map[of Suc "map \<phi> rls"] rls unfolding lift_def by (auto simp: o_def)
        have m: "m = Suc (\<psi> lr)" unfolding m lift_def ..

        have "(C, t, s, u, max_list (map \<phi> rls), \<psi> lr) \<in> critical_parallel_rule_peaks R S \<phi> \<psi>" 
          unfolding critical_parallel_rule_peaks_def using * by blast
        from decr[unfolded is_decreasing_def, rule_format, OF this]
        show ?case unfolding k m RS_conv_def R_le_def lift_def by auto
      qed
    }
    from this[OF decr(1)] this[OF decr(2)]
    show "is_decreasing R S ?\<phi> ?\<psi> Zero_Zero_Filter" "is_decreasing S R ?\<psi> ?\<phi> Zero_Zero_Filter" 
      by auto
  qed
qed

text \<open>Now the CR-version. This lemma is stronger 
  than Theorem 56 in Labelings for Decreasing Diagrams,
  since the decreasing conditions uses conversions instead of rewrite steps.\<close>
corollary rule_labeling_pcp_CR: assumes
  ll: "left_linear_trs R" 
  and decr: "is_decreasing_trs R \<phi>" 
shows "CR (rstep R)"
proof -
  note decr = decr[unfolded is_decreasing_trs]
  have "commute (rstep R) (rstep R)" 
    by (rule rule_labeling_pcp_commutation[OF ll ll decr decr])
  thus ?thesis
    by (simp add: CR_iff_self_commute)
qed

text \<open>A version of Theorem 31 which is restricted to CR properties, so that
  it can be used for modular and incremental CR-proofs without requiring commutation.\<close>
corollary compositional_rule_labeling_pcp_cr: assumes 
  ll: "left_linear_trs R" 
  and decr: "is_decreasing R R \<phi> \<psi> Zero_Zero_Filter" 
  "is_decreasing R R \<psi> \<phi> Zero_Zero_Filter" 
  and id_0: "R_le R \<phi> 0 = R_le R \<psi> 0" 
  and cr: "CR (rstep (R_le R \<psi> 0))" 
shows "CR (rstep R)"
proof -
  have "commute (rstep R) (rstep R)" 
  proof (rule compositional_rule_labeling_pcp_comm[OF ll ll decr], unfold id_0 defs)
    show "commute (rstep (R_le R \<psi> 0)) (rstep (R_le R \<psi> 0))" using cr
      by (simp add: CR_iff_self_commute)
  qed
  thus ?thesis by (simp add: CR_iff_self_commute)
qed

text \<open>Theorem 24 in FSCD 2022 Shintani Hirokawa 
  (the short proof via Theorem 31, but here it is generalized to commutation)\<close>
theorem compositional_parallel_critical_pairs_comm: 
  assumes ll: "left_linear_trs R" "left_linear_trs S" 
    and sub: "C \<subseteq> R" "D \<subseteq> S" 
    and comm: "commute (rstep C) (rstep D)" 
    and conv: "parallel_critical_pairs R S \<subseteq> (rstep D \<union> (rstep C)^-1)^*" 
    "parallel_critical_pairs S R \<subseteq> (rstep C \<union> (rstep D)^-1)^*" 
  shows "commute (rstep R) (rstep S)" 
proof -
  define lab where "lab C rl = (if rl \<in> C then 0 else (1 :: nat))" for rl and C :: "('a,'v)trs" 
  define \<phi> where "\<phi> = lab C" 
  define \<psi> where "\<psi> = lab D" 
  have C: "C = R_le R \<phi> 0" unfolding \<phi>_def lab_def R_le_def using sub by auto
  have D: "D = R_le S \<psi> 0" unfolding \<psi>_def lab_def R_le_def using sub by auto
  show ?thesis
  proof (rule compositional_rule_labeling_pcp_comm[OF ll _ _ comm[unfolded C D]])
    show "is_decreasing R S \<phi> \<psi> Zero_Zero_Filter" 
      unfolding is_decreasing_def lab_filter.simps
    proof (intro allI impI)
      fix CC t s u k m
      assume peak: "(CC, t, s, u, k, m) \<in> critical_parallel_rule_peaks R S \<phi> \<psi>" 
        and km: "k \<noteq> 0 \<or> m \<noteq> 0" 
      hence km: "max k m > 0" by auto
      from peak have "t = u \<or> (t,u) \<in> parallel_critical_pairs R S" 
        unfolding parallel_critical_pairs_def critical_parallel_rule_peaks_def by auto
      thus "(t, u)
       \<in> (rstep (RS_conv R S \<phi> \<psi> k))\<^sup>* O
          par_rstep (R_le S \<psi> m) O
          (rstep (RS_conv R S \<phi> \<psi> (max k m)))\<^sup>* O
          (par_rstep_var_restr (R_le R \<phi> k) (vars_mctxt CC))\<inverse> O (rstep (RS_conv R S \<phi> \<psi> m))\<^sup>*" 
      proof
        assume "t = u" 
        thus ?thesis using par_rstep_refl par_rstep_var_restr_refl by blast
      next
        assume "(t,u) \<in> parallel_critical_pairs R S" 
        with conv have "(t,u) \<in> (rstep D \<union> (rstep C)\<inverse>)\<^sup>*" by auto
        also have "\<dots> \<subseteq> (rstep (RS_conv R S \<phi> \<psi> (max k m)))^*" 
          apply (intro rtrancl_mono)
          apply (unfold rstep_converse[symmetric] rstep_union[symmetric])
          apply (intro rstep_mono)
          apply (unfold RS_conv_def C D)
          using km by (auto simp: R_le_def)
        finally 
        show ?thesis using par_rstep_refl par_rstep_var_restr_refl by blast
      qed
    qed
    show "is_decreasing S R \<psi> \<phi> Zero_Zero_Filter" 
      unfolding is_decreasing_def lab_filter.simps
    proof (intro allI impI)
      fix CC t s u k m
      assume peak: "(CC, t, s, u, k, m) \<in> critical_parallel_rule_peaks S R \<psi> \<phi>" 
        and km: "k \<noteq> 0 \<or> m \<noteq> 0" 
      hence km: "max k m > 0" by auto
      from peak have "t = u \<or> (t,u) \<in> parallel_critical_pairs S R" 
        unfolding parallel_critical_pairs_def critical_parallel_rule_peaks_def by auto
      thus "(t, u)
       \<in> (rstep (RS_conv S R \<psi> \<phi> k))\<^sup>* O
          par_rstep (R_le R \<phi> m) O
          (rstep (RS_conv S R \<psi> \<phi> (max k m)))\<^sup>* O
          (par_rstep_var_restr (R_le S \<psi> k) (vars_mctxt CC))\<inverse> O (rstep (RS_conv S R \<psi> \<phi> m))\<^sup>*" 
      proof
        assume "t = u" 
        thus ?thesis using par_rstep_refl par_rstep_var_restr_refl by blast
      next
        assume "(t,u) \<in> parallel_critical_pairs S R" 
        with conv have "(t,u) \<in> (rstep C \<union> (rstep D)\<inverse>)\<^sup>*" by auto
        also have "\<dots> \<subseteq> (rstep (RS_conv S R \<psi> \<phi> (max k m)))^*" 
          apply (intro rtrancl_mono)
          apply (unfold rstep_converse[symmetric] rstep_union[symmetric])
          apply (intro rstep_mono)
          apply (unfold RS_conv_def C D)
          using km by (auto simp: R_le_def)
        finally 
        show ?thesis using par_rstep_refl par_rstep_var_restr_refl by blast
      qed
    qed
  qed
qed

text \<open>Theorem 24 of FSCD 2022 in its original form for confluence\<close>
corollary compositional_parallel_critical_pairs: 
  assumes ll: "left_linear_trs R" 
    and sub: "C \<subseteq> R" 
    and cr: "CR (rstep C)" 
    and conv: "parallel_critical_pairs R R \<subseteq> (rstep C)\<^sup>\<leftrightarrow>\<^sup>*" 
  shows "CR (rstep R)" 
proof -
  have "commute (rstep R) (rstep R)" 
  proof (rule compositional_parallel_critical_pairs_comm[OF ll ll sub sub])
    show "commute (rstep C) (rstep C)" using cr
      by (simp add: CR_iff_self_commute)
    show "parallel_critical_pairs R R \<subseteq> ((rstep C)\<^sup>\<leftrightarrow>)\<^sup>*" 
      by (rule subset_trans[OF conv], auto)
    show "parallel_critical_pairs R R \<subseteq> ((rstep C)\<^sup>\<leftrightarrow>)\<^sup>*" by fact
  qed
  thus ?thesis by (simp add: CR_iff_self_commute)
qed

subsection \<open>Parallel Pair Closing Systems\<close>

text \<open>Definition 36 in FSCD 2022, commutation version\<close>

abbreviation join'' where "join'' R S \<equiv> R^* O (S^*)^-1"
abbreviation conv'' where "conv'' R S \<equiv> (R \<union> S^-1)^*" 

lemma conv''_mono: "R \<subseteq> R' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> conv'' R S \<subseteq> conv'' R' S'"
  by (intro rtrancl_mono, auto)

lemma converse_join'': "(join'' R S)^-1 = join'' S R"
  unfolding converse_inward ..

lemma join''_conv'': "join'' R S \<subseteq> conv'' R S"  
  unfolding converse_inward by regexp

lemma join''_subst_closed: "(s, t) \<in> join'' (rstep A) (rstep B)
 \<Longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> join'' (rstep A) (rstep B)" 
  by (metis rstep_converse rstep_rtrancl_idemp subst.closedD subst.closed_comp subst_closed_rstep)

lemma conv''_subst_closed: "(s, t) \<in> conv'' (rstep A) (rstep B)
 \<Longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> conv'' (rstep A) (rstep B)" 
  by (metis rstep_converse rstep_union rsteps_closed_subst)


definition "PCPS_com R S C D = (\<Union> ({{(s,t), (s,u)} | D' s t u lr rls.
  (D',t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr 
  \<and> lr \<in> S \<and> (t,u) \<notin> conv'' (rstep D) (rstep C)}))" 

text \<open>Lemma 37, commutation version\<close>

lemma PCPS_com_cases_root:
  assumes st: "(s,t) \<in> par_rstep R1" and su: "(s,u) \<in> rrstep R2" and 
    sub: "R1 \<subseteq> R" "R2 \<subseteq> S" "C \<subseteq> R" "D \<subseteq> S" 
    and P1: "P1 = PCPS_com R S C D" 
    and cps: "parallel_critical_pairs R S \<subseteq> join'' (rstep S) (rstep R)" 
    and ll: "left_linear_trs S" 
  shows "(t, u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse> \<or>
    (\<exists>t'. (s, t') \<in> rstep P1 
        \<and> (t', t) \<in> par_rstep R1 
        \<and> (s, u) \<in> rstep P1 
        \<and> (t', u) \<in> join'' (rstep S) (rstep R))" 
proof -
  from st obtain C' infos where st: "(s,t) \<in> par_rstep_mctxt R1 C' infos"
    using par_rstep_par_rstep_mctxt_conv by blast
  from rrstepE[OF su] obtain \<sigma> l r where s: "s = l \<cdot> \<sigma>" and u: "u = r \<cdot> \<sigma>" and lr: "(l,r) \<in> R2"
    by metis      
  from lr sub ll have "linear_term l" unfolding left_linear_trs_def by auto
  from parallel_critical_peaks_of_rule[OF st s this u sub(1)]
  show ?thesis
  proof (elim disjE exE conjE, goal_cases)
    case (1 v)
    from 1(1) lr have "(t,v) \<in> rstep R2" 
      by (metis rrstepE rrstepI rrstep_imp_rstep singletonD)
    hence "(t,v) \<in> par_rstep R2"
      using rstep_par_rstep by blast
    thus ?case using 1(2) by auto
  next
    case (2 D' s0 t0 u0 rls \<tau> \<sigma> infos)
    note s = 2(2) note t = 2(4) note u = 2(3)
    from 2(8) have t0t: "(t0 \<cdot> \<sigma>, t) \<in> par_rstep R1" unfolding t
      by (simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
    show ?thesis
    proof (cases "(t0,u0) \<in> conv'' (rstep D) (rstep C)")
      case False
      from False have "t0 \<noteq> u0" by auto
      with 2(1) lr sub have "(t0,u0) \<in> parallel_critical_pairs R S" 
        unfolding parallel_critical_pairs_def by blast
      with cps have "(t0,u0) \<in> join'' (rstep S) (rstep R)" by auto
      hence join: "(t0 \<cdot> \<sigma>,u0 \<cdot> \<sigma>) \<in> join'' (rstep S) (rstep R)" 
        unfolding rstep_converse[symmetric] converse_inward
        using rsteps_closed_subst[of _ _ S \<sigma>] rsteps_closed_subst[of _ _ "R^-1" \<sigma>]
        by auto blast
      let ?t' = "t0 \<cdot> \<sigma>" 
      from False 2(1) lr sub have "{(s0, t0), (s0,u0)} \<subseteq> P1" 
        unfolding PCPS_com_def P1 by blast
      hence "(s,?t') \<in> rstep P1 \<and> (?t',t) \<in> par_rstep R1
            \<and> (s,u) \<in> rstep P1 
            \<and> (?t',u) \<in> join'' (rstep S) (rstep R)" 
        using t0t join unfolding s u by auto
      thus ?thesis by blast
    next
      case True
      hence tu: "(t, u0 \<cdot> \<tau>) \<in> conv'' (rstep D) (rstep C)" unfolding t 
        by (rule conv''_subst_closed)  
      from 2(8) have uu: "(u, u0 \<cdot> \<tau>) \<in> par_rstep R1" unfolding u
        by (simp add: all_ctxt_closed_par_rstep all_ctxt_closed_subst_step)
      from tu uu show ?thesis by auto
    qed
  qed
qed

lemma PCPS_com_cases:
  assumes ll: "left_linear_trs R" "left_linear_trs S"  
    and sub:    "R1 \<subseteq> R" "R2 \<subseteq> S" "C \<subseteq> R" "D \<subseteq> S" 
    and join:   "parallel_critical_pairs R S \<subseteq> join'' (rstep S) (rstep R)" 
    "parallel_critical_pairs S R \<subseteq> join'' (rstep R) (rstep S)" 
    and st:     "(s,t) \<in> par_rstep R1" 
    and su:     "(s,u) \<in> par_rstep R2" 
    and P1:     "P1 = PCPS_com R S C D" 
    and P2:     "P2 = PCPS_com S R D C" 
  shows "(t,u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse> \<or>
   (\<exists> t' u'.  (s,t') \<in> rstep P1 \<and> (t',t) \<in> par_rstep R1
            \<and> (s,u') \<in> rstep P1 \<and> (u',u) \<in> par_rstep R2
            \<and> (t',u') \<in> join'' (rstep S) (rstep R)) \<or> 
   (\<exists> t' u'.  (s,t') \<in> rstep P2 \<and> (t',t) \<in> par_rstep R1
            \<and> (s,u') \<in> rstep P2 \<and> (u',u) \<in> par_rstep R2
            \<and> (t',u') \<in> join'' (rstep S) (rstep R))" 
proof -
  let ?prop = "\<lambda> R S R1 R2 P1 s t u t' u'. (s,t') \<in> rstep P1 \<and> (t',t) \<in> par_rstep R1
            \<and> (s,u') \<in> rstep P1 \<and> (u',u) \<in> par_rstep R2
            \<and> (t',u') \<in> join'' (rstep S) (rstep R)"  
  let ?Prop = "\<lambda> s t u. (t,u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)^-1 \<or>
     (\<exists> t' u'. ?prop R S R1 R2 P1 s t u t' u') \<or> 
     (\<exists> u' t'. ?prop S R R2 R1 P2 s u t u' t')" 
  have swap: "join'' (rstep R) (rstep S) = (join'' (rstep S) (rstep R))^-1" 
    by blast
  have "?Prop s t u" 
    using st su
  proof (induct s t arbitrary: u)
    case *: (root_step l r \<sigma> u)
    define s where "s = l \<cdot> \<sigma>"
    define t where "t = r \<cdot> \<sigma>" 
    have "(s,t) \<in> rrstep R1" using * unfolding s_def t_def by force
    from PCPS_com_cases_root[OF *(2)[folded s_def] this sub(2,1,4,3) P2 join(2) ll(1)]
    show ?case unfolding s_def[symmetric] t_def[symmetric]
    proof
      assume "(u, t) \<in> par_rstep R1 O conv'' (rstep C) (rstep D) O (par_rstep R2)\<inverse>" 
      hence "(t, u) \<in> (par_rstep R1 O conv'' (rstep C) (rstep D) O (par_rstep R2)\<inverse>)^-1" by simp 
      also have "\<dots> \<subseteq> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse>" 
        unfolding converse_inward by regexp
      finally show "?Prop s t u" by simp
    qed blast
  next
    case *: (par_step_fun ts ss f)
    define s where "s = Fun f ss" 
    define t where "t = Fun f ts" 
    have step: "(s, t) \<in> par_rstep R1" 
      using *(1,3) unfolding s_def t_def by blast
    from *(4)[folded s_def]
    show ?case unfolding t_def[symmetric] s_def[symmetric]
    proof cases
      case (root_step l r \<sigma>)
      hence rrstep: "(s, u) \<in> rrstep R2" by auto
      from PCPS_com_cases_root[OF step rrstep sub P1 join(1) ll(2)]
      show "?Prop s t u" by blast
    next
      case **: (par_step_fun us ss' f')
      with s_def have "f' = f" "ss' = ss" by auto
      note ** = **(2-)[unfolded this]
      let ?n = "length ss" 
      from * ** have len: "length ts = ?n" "length us = ?n" by auto
      {
        fix i
        assume i: "i < ?n" 
        from **(2) len i have R2step: "(ss ! i, us ! i) \<in> par_rstep R2" by auto
        from *(2)[OF _ R2step] len i have IH: "?Prop (ss ! i) (ts ! i) (us ! i)" by auto
      } note IH = this
      note stu = s_def t_def **(1)
      show "?Prop s t u"  
      proof (cases "\<exists> i < ?n. (\<exists> t' u'. ?prop R S R1 R2 P1 (ss ! i) (ts ! i) (us ! i) t' u') \<or>
              (\<exists> u' t'. ?prop S R R2 R1 P2 (ss ! i) (us ! i) (ts ! i) u' t')") 
        case False
        {
          fix i
          assume i: "i < ?n" 
          from IH[OF this] False i have "(ts ! i, us ! i) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse>" 
            by blast
        } note case_1 = this
        have "(t, u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse>" using case_1
          unfolding stu par_rstep_inverse[symmetric] converse_inward rstep_converse[symmetric] 
            rstep_union[symmetric] using len
          by (intro conjI all_ctxt_closedD[of UNIV] 
              all_ctxt_closed_relcomp all_ctxt_closed_par_rstep all_ctxt_closed_rsteps, auto)
        thus ?thesis by blast
      next
        case True
        then obtain i v' w' where i: "i < ?n" and 
          choice: "?prop R S R1 R2 P1 (ss ! i) (ts ! i) (us ! i) v' w'
          \<or> ?prop S R R2 R1 P2 (ss ! i) (us ! i) (ts ! i)  v' w'" 
          by blast
        {
          fix R S R1 R2 P :: "('a,'v)trs" and ss ts us t' u' s t u f n
          assume prop': "?prop R S R1 R2 P (ss ! i) (ts ! i) (us ! i) t' u'" 
            and stu: "s = Fun f ss" "t = Fun f ts" "u = Fun f us" 
            and i: "i < n" 
            and len: "length ss = n" "length ts = n" "length us = n" 
            and st: "\<And> i. i < n \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep R1" 
            and su: "\<And> i. i < n \<Longrightarrow> (ss ! i, us ! i) \<in> par_rstep R2" 
          let ?t' = "Fun f (ss[i := t'])" 
          let ?u' = "Fun f (ss[i := u'])"   
          have "?prop R S R1 R2 P s t u ?t' ?u'" 
          proof (intro conjI)
            from prop' have "(ss ! i, t') \<in> rstep P" by auto
            thus "(s, ?t') \<in> rstep P" unfolding stu using i len
              by (metis nrrstep_iff_arg_rstep nrrstep_imp_rstep)
            from prop' have "(ss ! i, u') \<in> rstep P" by auto
            thus "(s, ?u') \<in> rstep P" unfolding stu using i len
              by (metis nrrstep_iff_arg_rstep nrrstep_imp_rstep)
            from prop' have "(t', ts ! i) \<in> par_rstep R1" by auto
            thus "(?t', t) \<in> par_rstep R1" unfolding stu using i len st
              apply (intro par_step_fun)
              subgoal for j by (cases "i = j", auto)
              by auto
            from prop' i len have "(u', us ! i) \<in> par_rstep R2" by auto
            thus "(?u', u) \<in> par_rstep R2" unfolding stu using i len su
              apply (intro par_step_fun)
              subgoal for j by (cases "i = j", auto)
              by auto
            let ?C = "More f (take i ss) Hole (drop (Suc i) ss)" 
            from prop' have "(t', u') \<in> join'' (rstep S) (rstep R)" by auto  
            with rsteps_closed_ctxt[of _ _ _ ?C]
            have "(?C \<langle>t'\<rangle>, ?C \<langle> u' \<rangle>) \<in> join'' (rstep S) (rstep R)" 
              unfolding rstep_converse[symmetric] by blast
            also have "?C \<langle>t'\<rangle> = ?t'" unfolding stu using i len
              by (simp add: upd_conv_take_nth_drop)
            also have "?C \<langle>u'\<rangle> = ?u'" unfolding stu using i len
              by (simp add: upd_conv_take_nth_drop)
            finally show "(?t', ?u') \<in> join'' (rstep S) (rstep R)" .
          qed
        } note main = this
        from choice show ?thesis
        proof
          assume "?prop R S R1 R2 P1 (ss ! i) (ts ! i) (us ! i) v' w'" 
          from main[OF this stu i refl len *(1) **(2)] len
          show ?thesis by auto
        next
          assume "?prop S R R2 R1 P2 (ss ! i) (us ! i) (ts ! i)  v' w'" 
          from main[OF this stu(1,3,2) i refl len(2,1) **(2) *(1)] len
          show ?thesis 
            by (intro disjI2, auto)
        qed
      qed
    next
      case (par_step_var x)
      hence "s = u" by auto
      with step have "(t, u) \<in> (par_rstep R1)^-1" by auto
      then show "?Prop s t u" by blast
    qed
  qed blast
  thus ?thesis unfolding swap by blast
qed


lemma PCPS_com_cases_merge_P:
  assumes ll: "left_linear_trs R" "left_linear_trs S"  
    and sub:    "R1 \<subseteq> R" "R2 \<subseteq> S" "C \<subseteq> R" "D \<subseteq> S" 
    and join:   "parallel_critical_pairs R S \<subseteq> join'' (rstep S) (rstep R)" 
    "parallel_critical_pairs S R \<subseteq> join'' (rstep R) (rstep S)" 
    and P:      "P = PCPS_com R S C D \<union> PCPS_com S R D C"   (* merge PCPSs *)
    and st:     "(s,t) \<in> par_rstep R1" 
    and su:     "(s,u) \<in> par_rstep R2" 
  shows "(t,u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse> \<or>
   (\<exists> t' u'.  (s,t') \<in> rstep P \<and> (t',t) \<in> par_rstep R1
            \<and> (s,u') \<in> rstep P \<and> (u',u) \<in> par_rstep R2
            \<and> (t',u') \<in> join'' (rstep S) (rstep R))" 
proof -
  define A where "A = ((t, u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse>)" 
  define P1 where "P1 = rstep (PCPS_com R S C D)" 
  define P2 where "P2 = rstep (PCPS_com S R D C)" 
  define J where "J = join'' (rstep S) (rstep R)" 
  note defs = A_def P1_def P2_def J_def 
  from P have "PCPS_com R S C D \<subseteq> P" "PCPS_com S R D C \<subseteq> P" by auto
  from rstep_mono[OF this(1)] rstep_mono[OF this(2)]
  show ?thesis
    using PCPS_com_cases[OF ll sub join st su refl refl] 
    unfolding defs[symmetric] by force
qed

text \<open>Theorem 38, commutation version\<close>

theorem compositional_PCPS_com:
  assumes ll: "left_linear_trs R" "left_linear_trs S"  
    and CRS:    "C \<subseteq> R" "D \<subseteq> S" 
    and join:   "parallel_critical_pairs R S \<subseteq> join'' (rstep S) (rstep R)" 
    "parallel_critical_pairs S R \<subseteq> join'' (rstep R) (rstep S)" 
    and P:      "P = PCPS_com R S C D \<union> PCPS_com S R D C" (* merge PCPSs *)
    and com:    "commute (rstep C) (rstep D)"
    and SN:     "SN (relto (rstep P) (rstep (R \<union> S)))" (* merge R and S *)
  shows "commute (rstep R) (rstep S)" 
proof -
  let ?RS = "R \<union> S" 
  let ?PRS = "relto (rstep P) (rstep ?RS)" 
  define rel where "rel = {(None, Some x) | x. True} \<union> {(Some s, Some t) | s t. (t,s) \<in> ?PRS^+}"
  have "SN (rel^-1)" 
  proof 
    fix f
    assume "\<forall> i. (f i, f (Suc i)) \<in> rel\<inverse>" 
    hence steps: "\<And> i. (f (Suc i), f i) \<in> rel" by auto
    define g where "g i = f (Suc i)" for i
    {
      fix i
      have "\<exists> x. g i = Some x" using steps[of "Suc i"] unfolding g_def rel_def by force
    }
    hence "\<forall> i. \<exists> x. g i = Some x" by auto
    from choice[OF this] obtain h where gh: "\<And> i. g i = Some (h i)" by auto
    {
      fix i
      from steps[of "Suc i"] gh[of i] gh[of "Suc i"]
      have "(h i, h (Suc i)) \<in> ?PRS^+" unfolding g_def rel_def by auto
    }
    hence "\<not> SN (?PRS^+)" by blast
    hence "\<not> SN ?PRS" using SN_trancl_SN_conv by blast
    with SN show False by blast
  qed
  from SN_imp_wf[OF this] have wf: "wf rel" by auto
  have least: "x = None \<or> (None, x) \<in> rel" for x unfolding rel_def by auto
  have trans: "trans rel" unfolding rel_def trans_def by auto
  let ?RC = "R - C" 
  let ?SD = "S - D" 
  define L where "L R C lab = (case lab of None \<Rightarrow> par_rstep C | 
    Some \<alpha> \<Rightarrow> { (s,t) | s t. (\<alpha>,s) \<in> (rstep ?RS)^* \<and> (s,t) \<in> par_rstep (R - C)})" for lab R  C
  let ?L = "L R C" let ?L' = "L S D" 
  have LN: "L R C None = par_rstep C" for R C unfolding L_def by auto

  have comm: "commute (?L None) (?L' None)"
    unfolding LN using com
    by (simp add: commute_def par_rsteps_rsteps rtrancl_converse)

  have idRC: "rstep R = rstep ?RC \<union> rstep C" unfolding rstep_union[symmetric] using CRS
    by fast
  have idSD: "rstep S = rstep ?SD \<union> rstep D" unfolding rstep_union[symmetric] using CRS
    by fast
  have commute: "commute (\<Union> (range ?L)) (\<Union> (range ?L'))" 
  proof (rule dd_minimum_commute[OF wf trans least, of ?L ?L', OF comm], goal_cases)
    case (1 a b s t u)
    from 1(1)[unfolded L_def] obtain R1 where 
      R1: "R1 = C \<or> R1 = ?RC \<and> a \<noteq> None" and st: "(s,t) \<in> par_rstep R1" by (cases a, auto)
    from 1(2)[unfolded L_def] obtain R2 where 
      R2: "R2 = D \<or> R2 = ?SD \<and> b \<noteq> None" and su: "(s,u) \<in> par_rstep R2" by (cases b, auto)
    have ab: "(a, b) \<noteq> (None, None)" by fact
    from R1 R2 CRS have R12R: "R1 \<subseteq> R" "R2 \<subseteq> S" by auto
    from st have stR: "(s,t) \<in> par_rstep ?RS" using R12R par_rstep_mono by blast
    from su have suR: "(s,u) \<in> par_rstep ?RS" using R12R par_rstep_mono by blast
    define U where "U = (under rel a \<union> under rel b)" 
    let ?U = "conversion'' ?L ?L' U" 
    have None: "None \<in> U" using 1(3) unfolding rel_def U_def under_def by auto
    from PCPS_com_cases_merge_P[OF ll R12R CRS join P st su] 
    have "(t, u) \<in> (?L' b)\<^sup>= O ?U O ((?L a)\<inverse>)\<^sup>=" 
    proof (elim disjE exE conjE)
      assume "(t, u) \<in> par_rstep R2 O conv'' (rstep D) (rstep C) O (par_rstep R1)\<inverse>" 
      then obtain t' u' where tt': "(t, t') \<in> par_rstep R2" 
        and tu': "(t',u') \<in> conv'' (rstep D) (rstep C)" 
        and uu': "(u,u') \<in> par_rstep R1" by auto
      from R2
      have tt': "(t,t') \<in> ?L' b \<union> ?L' None" 
      proof 
        assume "R2 = D" 
        with tt' have "(t,t') \<in> ?L' None" unfolding L_def by auto
        thus ?thesis by auto
      next
        assume "R2 = ?SD \<and> b \<noteq> None" 
        with set_mp[OF par_rstep_rsteps stR] 1(2) tt' have "(t,t') \<in> ?L' b" unfolding L_def by auto
        thus ?thesis by auto
      qed
      from R1
      have uu': "(u,u') \<in> ?L a \<union> ?L None" 
      proof 
        assume "R1 = C" 
        with uu' have "(u,u') \<in> ?L None" unfolding L_def by auto
        thus ?thesis by auto
      next
        assume "R1 = ?RC \<and> a \<noteq> None" 
        with set_mp[OF par_rstep_rsteps suR] 1(1) uu' have "(u,u') \<in> ?L a" unfolding L_def by auto
        thus ?thesis by auto
      qed
      have tu': "(t',u') \<in> conv'' (?L' None) (?L None)" unfolding LN 
        by (rule set_mp[OF conv''_mono tu']; intro rstep_par_rstep)
      from tt' tu' uu' have "(t,u) \<in> (?L' b)\<^sup>= O (((?L' None)\<^sup>= O conv'' (?L' None) (?L None) O ((?L None)^-1)\<^sup>=)) O ((?L a)^-1)\<^sup>=" 
        unfolding LN by blast
      also have "\<dots> \<subseteq> (?L' b)\<^sup>= O conv'' (?L' None) (?L None) O ((?L a)^-1)\<^sup>=" 
        by (intro relcomp_mono[OF subset_refl] relcomp_mono[OF _ subset_refl]) regexp
      also have "\<dots> \<subseteq> (?L' b)\<^sup>= O ?U O ((?L a)^-1)\<^sup>=" 
        apply (intro relcomp_mono subset_refl)
        apply (unfold converse_inward)
        using None
        by (intro rtrancl_mono relcomp_mono, auto)
      finally show ?thesis .
    next
      fix t' u'
      assume st: "(s, t') \<in> rstep P" 
        and tt: "(t', t) \<in> par_rstep R1" 
        and su: "(s, u') \<in> rstep P" 
        and uu: "(u', u) \<in> par_rstep R2" 
        and tu': "(t', u') \<in> join'' (rstep S) (rstep R)" 
      then obtain v where 
        tv: "(t',v) \<in> (rstep S)^*" and
        uv: "(u',v) \<in> (rstep R)^*" 
        by blast
      have sta: "(s, t) \<in> ?L a" by fact
      have sub: "(s, u) \<in> ?L' b" by fact
      {
        fix a b s t u t' R1 R S C D
        let ?L = "L R C" let ?L' = "L S D" 
        let ?U = "conversion'' ?L ?L' U" 
        assume 
          st: "(s, t') \<in> rstep P" and
          tt: "(t', t) \<in> par_rstep R1" and
          tv: "(t', v) \<in> (rstep S)^*" and
          ab: "(a, b) \<noteq> (None, None)" and
          sta: "(s, t) \<in> ?L a" and
          sub: "(s, u) \<in> ?L' b" and 
          U_def: "U = (under rel a \<union> under rel b)" and
          R1: "R1 = C \<or> R1 = R - C \<and> a \<noteq> None" and
          idSD: "rstep S = rstep (S - D) \<union> rstep D" and
          RS: "R \<union> S = ?RS" 

        from ab have "a \<noteq> None \<or> b \<noteq> None" by auto
        moreover
        {
          assume "a \<noteq> None" 
          then obtain \<alpha> where a: "a = Some \<alpha>" by auto
          from sta[unfolded L_def a] st
          have "(Some t', a) \<in> rel" unfolding a rel_def by auto
        }
        moreover
        {
          assume "b \<noteq> None" 
          then obtain \<alpha> where b: "b = Some \<alpha>" by auto
          from sub[unfolded L_def b, simplified] st
          have "(Some t', b) \<in> rel" unfolding b rel_def by auto
        }
        ultimately have t'U: "Some t' \<in> U" unfolding U_def under_def by auto
        have tt: "(t', t) \<in> ?U^-1" using R1
        proof
          assume "R1 = C" 
          hence "(t',t) \<in> ?L None" using tt unfolding LN by auto 
          with None show ?thesis by auto
        next
          assume "R1 = R - C \<and> a \<noteq> None" 
          with tt have "(t',t) \<in> ?L (Some t')" unfolding L_def by auto
          with t'U have "(t,t') \<in> ?U" by auto
          thus ?thesis by auto
        qed
        from tv have tv: "(t',v) \<in> ?U" 
        proof (induct rule: rtrancl_induct)
          case (step v w)
          from step(2)[unfolded idSD]
          have "(v,w) \<in> ?U"
          proof 
            assume "(v,w) \<in> rstep D" 
            hence "(v,w) \<in> ?L' None" unfolding LN
              using rstep_par_rstep by blast
            thus ?thesis using None by auto
          next
            assume "(v, w) \<in> rstep (S - D)" 
            hence "(v,w) \<in> ?L' (Some t')" using set_mp[OF rtrancl_mono[OF rstep_mono[of _ "R \<union> S"]] step(1)] 
                rstep_par_rstep unfolding L_def option.simps RS[symmetric] by auto
            thus ?thesis using t'U by auto
          qed
          with step show ?case by auto
        qed auto
        from tt tv have "(t,v) \<in> ?U O ?U" by blast
        also have "?U O ?U = ?U" by regexp
        finally have "(t,v) \<in> ?U" .
      } note main = this
      have tv: "(t,v) \<in> ?U"
        by (rule main[OF st tt tv ab sta sub U_def R1 idSD refl])
      have "(u,v) \<in> conversion'' ?L' ?L U" 
        by (rule main[OF su uu uv _ sub sta _ R2 idRC], insert ab U_def, auto)
      hence "(v,u) \<in> (conversion'' ?L' ?L U)^-1" by simp
      also have "\<dots> = ?U" unfolding converse_inward
        by (rule arg_cong[of _ _ rtrancl], auto)
      finally have vu: "(v,u) \<in> ?U" .
      from tv vu have "(t,u) \<in> ?U O ?U" by blast
      hence "(t, u) \<in> ?U" by simp
      thus ?thesis by auto
    qed
    thus ?case unfolding U_def[symmetric] by blast
  qed
  {
    fix C R :: "('a,'v)trs" 
    assume CR: "C \<subseteq> R" 
    have idRC: "rstep R = rstep (R - C) \<union> rstep C" unfolding rstep_union[symmetric] using CR
      by fast
    have one: "\<Union> (range (L R C)) \<subseteq> (rstep R)^*" 
      unfolding L_def using subset_trans[OF par_rstep_mono par_rstep_rsteps] CR
      by (auto split: option.splits) blast+
    moreover 
    have "rstep R \<subseteq> (\<Union> (range (L R C)))" 
    proof
      fix s t
      assume "(s,t) \<in> rstep R" 
      with idRC have "(s,t) \<in> rstep (R - C) \<or> (s,t) \<in> rstep C" by auto
      thus "(s, t) \<in> \<Union> (range (L R C))"
      proof
        assume "(s,t) \<in> rstep (R - C)" 
        thus ?thesis unfolding L_def using rstep_par_rstep[of "R - C"] 
          by (auto intro!: exI[of _ "Some s"])
      next
        show "(s, t) \<in> rstep C \<Longrightarrow> (s, t) \<in> \<Union> (range (L R C))" 
          unfolding L_def using rstep_par_rstep[of "C"] 
          by (auto intro!: exI[of _ None])
      qed
    qed
    ultimately have "(\<Union> (range (L R C)))^* = (rstep R)^*" by (metis rtrancl_subset)
  }
  from this[OF CRS(1)] this[OF CRS(2)] commute
  show ?thesis unfolding commute_def rtrancl_converse by simp
qed

text \<open>Definition 36 in FSCD 2022\<close>
definition "PCPS R C = (\<Union> ({{(s,t), (s,u)} | D s t u lr rls. 
  (D,t,s,u,rls) \<in> parallel_critical_peaks_of_rule R lr \<and> lr \<in> R \<and> (t,u) \<notin> (rstep C)\<^sup>\<leftrightarrow>\<^sup>*}))" 

lemma PCPS_is_PCPS_com: "PCPS R C = PCPS_com R R C C" 
  unfolding PCPS_def PCPS_com_def conversion_def by auto

text \<open>Theorem 38 in its original form is derived from the commutation version.\<close>

theorem compositional_PCPS: assumes
  ll: "left_linear_trs R" and
  cr: "CR (rstep C)" and
  CR: "C \<subseteq> R" and
  join: "parallel_critical_pairs R R \<subseteq> join (rstep R)" and
  SN: "SN (relto (rstep P) (rstep R))" and
  P: "P = PCPS R C" 
shows "CR (rstep R)" 
proof -
  from cr have com: "commute (rstep C) (rstep C)"
    by (simp add: CR_iff_self_commute)
  have P: "P = PCPS_com R R C C \<union> PCPS_com R R C C" unfolding P PCPS_is_PCPS_com by auto  
  have join'': "join'' (rstep R) (rstep R) = join (rstep R)" unfolding converse_inward join_def ..
  have "commute (rstep R) (rstep R)" 
    by (rule compositional_PCPS_com[OF ll ll CR CR _ _ P com], insert join[folded join''] SN, auto)
  thus ?thesis
    by (simp add: CR_iff_self_commute)
qed
end

end
