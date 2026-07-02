(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Context_Sensitive
  imports
    First_Order_Rewriting.Unification_More
    First_Order_Rewriting.Trs_Impl
    "HOL-Library.Monad_Syntax"
    Auxx.Name
    Forbidden_Patterns
begin

(* context sensitive replacement map \<mu> *)
type_synonym 'f mu = "'f \<times> nat \<Rightarrow> nat set"

definition csstep_cond :: "'f mu \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "csstep_cond c p t \<equiv> 
 \<forall> p1 i p2. p = p1 @ i # p2 \<and> p \<in> poss t \<longrightarrow> (\<exists> f ts. t |_ p1 = Fun f ts \<and> i \<in> c (f,length ts))" 

definition csstep_r_p_s :: 
  "'f mu \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) subst \<Rightarrow> 
  ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "csstep_r_p_s \<mu> rs lr p \<sigma> s t \<equiv> (s, t) \<in> rstep_r_p_s rs lr p \<sigma> \<and> csstep_cond \<mu> p s"

definition csstep_p :: "'f mu \<Rightarrow> ('f,'v)trs \<Rightarrow> pos \<Rightarrow> ('f,'v)trs"
  where "csstep_p \<mu> rs p = {(s,t) | s t.(\<exists> lr \<sigma>. (s,t) \<in> rstep_r_p_s rs lr p \<sigma> \<and> csstep_cond \<mu> p s)}"

definition csstep :: "'f mu \<Rightarrow> ('f,'v)trs  \<Rightarrow> ('f,'v)trs"
  where "csstep \<mu> rs = {(s,t). \<exists> p. (s,t) \<in>  csstep_p \<mu> rs p}"

(* Transformation of context sensitive replacement map \<mu> to forbidden patterns *)
definition to_pi :: "'f mu \<Rightarrow> ('f, string) forb_patterns"
  where "to_pi c \<equiv> {(ct, xi, loc). \<exists> f a xs i. i < a \<and> i \<notin> c (f,a) \<and>
 xs = map (\<lambda> x . Var x) (fresh_strings_list ''x'' 0 [] a) \<and> xi = xs!i \<and>
 ct = ctxt_of_pos_term [i] (Fun f xs) \<and> loc \<in> {Forbidden_Patterns.B, Forbidden_Patterns.H}}"


lemma fp_is_cs_cond: assumes posst:"p \<in> poss t" shows "fpstep_cond (to_pi c) p t = csstep_cond c p t"
proof
  assume fp:"fpstep_cond (to_pi c) p t" show "csstep_cond c p t"  unfolding csstep_cond_def
  proof((rule allI)+)
    fix p1 i p2
    show "p = p1 @ i # p2 \<and> p \<in> poss t \<longrightarrow> (\<exists>f ts. t |_ p1 = Fun f ts \<and> i \<in> c (f, length ts))"
    proof
      assume "p = p1 @ i # p2 \<and> p \<in> poss t"
      then have p':"p = p1 @ i # p2" and pt:"p \<in> poss t" by auto
      let ?t' = "t |_ p1"
      from p' pt have "is_Fun ?t'" by (metis is_VarE list.distinct(1) poss_append_poss var_pos_maximal)
      then obtain f ts where t:"?t' = Fun f ts" by blast
      let ?a = "length ts"
      let ?H = Forbidden_Patterns.H 
      let ?B = Forbidden_Patterns.B
      have "funas_term ?t' \<subseteq> funas_term t" by (metis p' poss_append_poss pt subt_at_imp_supteq supteq_imp_funas_term_subset)
      from pt have "i # p2 \<in> poss ?t'" using poss_append_poss pt[unfolded p'] by blast 
      from this[unfolded t] have ia:"i < ?a" by (metis term.sel(4) poss_Cons_poss)
      have "i \<in> c (f,?a)"
      proof(rule ccontr)
        assume nic:"i \<notin> c (f, length ts)"
        let ?fresh = "fresh_strings_list ''x'' 0 [] ?a"
        from nic ia have "\<exists> xs l ci xi. \<forall> l \<in> {?B, ?H}.
      (ci, xi, l) \<in> to_pi c \<and> ci = ctxt_of_pos_term [i] (Fun f xs) \<and>
      xs = map (\<lambda> x . Var x) ?fresh \<and> xi = xs!i" unfolding to_pi_def by blast
        then obtain xs ci xi where pH:"(ci, xi, ?H) \<in> to_pi c" and pB:"(ci, xi, ?B) \<in> to_pi c" and
          ci:"ctxt_of_pos_term [i] (Fun f xs) = ci" and xs:"xs = map (\<lambda> x . Var x) ?fresh" and xi:"xi = xs!i" by auto
        from xs fresh_name_gen_for_strings_list[unfolded fresh_name_gen_list_def] have 
          "length xs = ?a \<and> distinct ?fresh" by (metis length_map)
        then have len:"length xs = ?a" and  disj:"set ?fresh \<inter> set [] = {}" and dist:"distinct ?fresh" by auto 
        with ia have ip:"[i] \<in> poss (Fun f xs)" by force
        with ctxt_supt_id[OF ip] xi have a:"(ctxt_of_pos_term [i] (Fun f xs))\<langle>xi\<rangle> = Fun f xs" by force
        from a have b:"(ctxt_of_pos_term [i] (Fun f xs))\<langle>xi\<rangle> = Fun f xs" by fast
        define \<sigma> where "\<sigma> = mk_subst Var (zip ?fresh ts)" 
        from len[unfolded xs] have len':"length ts = length ?fresh" by auto
        with mk_subst_distinct[OF dist] have c:"map \<sigma> ?fresh = ts" unfolding \<sigma>_def by (metis map_nth_eq_conv)
        have d:"map (\<lambda> t. t \<cdot> \<sigma>) xs = map ((\<lambda> t. t \<cdot> \<sigma>) \<circ> Var) ?fresh" unfolding xs by (metis List.map.compositionality)
        have d:"map \<sigma> ?fresh =  map ((\<lambda>t. t \<cdot> \<sigma>) \<circ> Var) ?fresh" by (metis comp_apply eval_term.simps(1))
        from c have "map (\<lambda> t. t \<cdot> \<sigma>) (map Var ?fresh) = ts" unfolding map_map by (metis d)
        from this mk_subst_distinct[OF dist] have "(Fun f xs) \<cdot> \<sigma> = ?t'" unfolding xs t eval_term.simps(2) by force
        with b ci have "\<exists> \<sigma>. ?t' = ci\<langle>xi\<rangle> \<cdot> \<sigma>" by fastforce
        with p' pt have sg:"\<exists> \<sigma>. t = (ctxt_of_pos_term p1 t)\<langle>ci\<langle>xi\<rangle> \<cdot> \<sigma>\<rangle>" by (metis ctxt_supt_id poss_append_poss)
        from pt[unfolded p'] have pt':"p1 \<in> poss t" by simp
        have "\<not> fpstep_cond (to_pi c) p t" 
        proof(cases p2)
          case Nil
          from hole_pos_ctxt_of_pos_term[OF ip]  hole_pos_ctxt_of_pos_term[OF pt'] sg p'[unfolded Nil]
          have "\<exists> C' \<sigma>. t = C'\<langle>ci\<langle>xi\<rangle> \<cdot> \<sigma>\<rangle> \<and> p = hole_pos C' @ hole_pos ci" unfolding ci by force
          with pH show ?thesis unfolding fpstep_cond_def fpstep_cond_single_def by fast
        next
          case (Cons j p2')
          from hole_pos_ctxt_of_pos_term[OF ip]  hole_pos_ctxt_of_pos_term[OF pt'] sg p'[unfolded Cons]
          have "\<exists> C' \<sigma>. t = C'\<langle>ci\<langle>xi\<rangle> \<cdot> \<sigma>\<rangle> \<and> hole_pos C' @ hole_pos ci <\<^sub>p p" unfolding ci less_pos_def less_eq_pos_def 
            by auto
          with pB show ?thesis unfolding fpstep_cond_def fpstep_cond_single_def by fast
        qed
        with fp show False by auto 
      qed
      with t show "\<exists>f ts. t |_ p1 = Fun f ts \<and> i \<in> c (f, length ts)" by auto
    qed
  qed
next
  assume cs:"csstep_cond c p t" show "fpstep_cond (to_pi c) p t" unfolding fpstep_cond_def
  proof
    fix pt
    assume pt_pi:"pt \<in> to_pi c"
    show "fpstep_cond_single pt p t"
    proof(cases pt)
      fix C u loc
      assume pt:"pt = (C, u, loc)"
      from pt_pi[unfolded pt to_pi_def] obtain f a xs i where ia:"i < a" and nic:"i \<notin> c (f,a)" and 
        C:"C = ctxt_of_pos_term [i] (Fun f xs)" and xs:"xs = map Var (fresh_strings_list ''x'' 0 [] a)" and
        u:"u = xs ! i" and BH:"loc \<in> {location.B, location.H}" by blast
      let ?fresh = "fresh_strings_list ''x'' 0 [] a"
      let ?C = "ctxt_of_pos_term [i] (Fun f xs)"
      from xs fresh_name_gen_for_strings_list[unfolded fresh_name_gen_list_def] have 
        len:"length xs = a \<and> distinct ?fresh" by (metis length_map)
      then have len:"length xs = a" and dist:"distinct ?fresh" by auto
      from ia len have iposs:"[i] \<in> poss (Fun f xs)" by simp
      from C hole_pos_ctxt_of_pos_term[OF this] have Ci:"hole_pos C = [i]" by auto
      from cs[unfolded csstep_cond_def] have 
        "\<forall> p1 i p2. p = p1 @ i # p2 \<and> p \<in> poss t \<longrightarrow> (\<exists>f ts. t |_ p1 = Fun f ts \<and> i \<in> c (f, length ts))" by auto
      show "fpstep_cond_single pt p t" unfolding fpstep_cond_single_def pt split
      proof
        assume ex:"\<exists>C' \<sigma>. t = C'\<langle>C\<langle>u\<rangle> \<cdot> \<sigma>\<rangle> \<and>
           (loc = location.H \<and> p = hole_pos C' @ hole_pos C \<or> loc = location.A \<and> p <\<^sub>p hole_pos C' @ hole_pos C \<or>
            loc = location.B \<and> hole_pos C' @ hole_pos C <\<^sub>p p \<or> loc = location.R \<and> right_of_pos p (hole_pos C'))"
        from BH ex obtain C' \<sigma> where t:"t = C'\<langle>C\<langle>u\<rangle> \<cdot> \<sigma>\<rangle>" and HB:"(loc = location.H \<and> p = hole_pos C' @ hole_pos C) \<or> 
     (loc = location.B \<and> hole_pos C' @ hole_pos C <\<^sub>p p)" (is "?H \<or> ?B") by auto
        let ?tp1 = "t |_ hole_pos C'"
        have "\<exists>f ts. ?tp1 = Fun f ts \<and> i \<in> c (f, length ts)"
        proof(cases ?H)
          case True
          with Ci have p:"p = hole_pos C' @ [i]" by auto
          from cs[unfolded csstep_cond_def] posst p show ?thesis by auto
        next
          case False
          with HB have B:"loc = location.B" and p:"hole_pos C' @ hole_pos C <\<^sub>p p" by auto
          then obtain q where p:"p = hole_pos C' @ [i] @ q" 
            unfolding less_pos_def less_eq_pos_def Ci by auto
          from cs[unfolded csstep_cond_def] posst p show ?thesis by auto
        qed
        then obtain f' ts' where tp1:"?tp1 = Fun f' ts'" and ic:"i \<in> c (f', length ts')" by blast
        from subt_at_hole_pos have tp1':"?tp1 = ?C\<langle>u\<rangle> \<cdot> \<sigma>" unfolding t[unfolded C] by fast
        from tp1[unfolded tp1' u] ctxt_supt_id iposs weak_match_match have "f = f'" and "length xs = length ts'" by auto
        with ic nic show False unfolding len by auto
      qed
    qed
  qed
qed

lemma csstep_r_p_s_iff_fpstep_r_p_s: 
  "csstep_r_p_s \<mu> rs lr p \<sigma> s t = fpstep_r_p_s (to_pi \<mu>) rs lr p \<sigma> s t"
  unfolding csstep_r_p_s_def fpstep_r_p_s_def rstep_r_p_s_def
  using fp_is_cs_cond by (metis (lifting) mem_Collect_eq split_conv)

lemma csstep_p_iff_fpstep_p: 
  "csstep_p \<mu> trs p = fpstep_p (to_pi \<mu>) trs p" (is "?C = ?F")
proof(rule, rule)
  fix s t
  assume "(s,t) \<in> csstep_p \<mu> trs p"
  from this[unfolded csstep_p_def]  have r:"\<exists> lr \<sigma>. (s,t) \<in> rstep_r_p_s trs lr p \<sigma>" and cs:"csstep_cond \<mu> p s" by auto
  from r have "p \<in> poss s" unfolding rstep_r_p_s_def mem_Collect_eq 
    using rstep_r_p_s_def' by force
  from r fp_is_cs_cond[OF this] cs show "(s,t) \<in> fpstep_p (to_pi \<mu>) trs p" unfolding fpstep_p_def by auto
next
  {
    fix s t
    assume "(s,t) \<in> fpstep_p (to_pi \<mu>) trs p" (is ?FP)
    from this[unfolded fpstep_p_def]  have r:"\<exists> lr \<sigma>. (s,t) \<in> rstep_r_p_s trs lr p \<sigma>" and cs:"fpstep_cond(to_pi \<mu>) p s" by auto
    from r have "p \<in> poss s" unfolding rstep_r_p_s_def mem_Collect_eq 
      using rstep_r_p_s_def' by force
    from r fp_is_cs_cond[OF this] cs have "(s,t) \<in> csstep_p \<mu> trs p" unfolding csstep_p_def by auto
  }
  then show "?F \<subseteq> ?C" by (rule subrelI)
qed

lemma csstep_iff_fpstep: "csstep \<mu> trs = fpstep (to_pi \<mu>) trs"
  unfolding csstep_def fpstep_def using  csstep_p_iff_fpstep_p by blast

end
