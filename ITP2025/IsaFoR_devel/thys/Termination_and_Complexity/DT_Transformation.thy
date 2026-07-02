(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
section \<open>Dependency Tupel Transformation\<close>

theory DT_Transformation
  imports
    TRS.Q_Relative_Rewriting
    First_Order_Rewriting.Multihole_Context
    Ord.Complexity
    Auxx.Util
begin

locale pre_innermost_wf = 
  fixes D :: "'f sig"
  and R :: "('f, 'v) trs"
  and Q :: "('f, 'v) terms"
begin

abbreviation "rew \<equiv> qrstep False Q R"
abbreviation "rew_r_p_s \<equiv> qrstep_r_p_s False Q R"
abbreviation step (infix "\<rightarrow>" 55)
where
  "step s t \<equiv> (s, t) \<in> rew"

definition DPos :: "('f, 'v) term \<Rightarrow> pos set"
where
  "DPos s = {p. p \<in> poss s \<and> (\<exists> f \<in> D. root (s |_ p) = Some f)}"

definition RPos :: "('f, 'v) term \<Rightarrow> pos set"
where
  "RPos s = {p. p \<in> DPos s \<and> (\<exists> u. s |_ p \<rightarrow> u)}"

lemma RPos_subseteq_DPos: "RPos s \<subseteq> DPos s" by (auto simp: RPos_def)

lemma DPos_subseteq_fun_poss:
  "DPos s \<subseteq> fun_poss s"
proof
  fix p
  assume "p \<in> DPos s"
  then obtain f and n where "root (s |_ p) = Some (f, n)"
    and "p \<in> (fun_poss s \<union> var_poss s)" by (auto simp: DPos_def var_poss_iff)
  moreover then have "p \<notin> var_poss s" by (auto simp: var_poss_iff)
  ultimately show "p \<in> fun_poss s" by blast
qed

end

locale innermost_wf =
  pre_innermost_wf D R Q for D :: "'f sig" and R :: "('f, 'v) trs" and Q :: "('f, 'v) terms" +
  assumes defs_R: "{fn. defined R fn} \<subseteq> D"
    and wf_R: "wf_trs R"
    and innermost: "NF_terms Q \<subseteq> NF_trs R"
begin

lemma rew_r_p_s_imp_NF_subst:
  assumes "(s, t) \<in> rew_r_p_s lr p \<sigma>"
    and "x \<in> vars_rule lr"
  shows "\<sigma> x \<in> NF_trs R"
proof - 
  let ?l = "fst lr"
  have "lr \<in> R" using assms(1)[unfolded qrstep_r_p_s_def] by auto
  with assms(2) wf_R[unfolded wf_trs_def'] obtain f ls where 
    l: "?l = Fun f ls" and x: "x \<in> vars_term ?l"
    by (force simp: vars_rule_def)+
  have "\<sigma> x \<in> NF_terms Q" unfolding l using 
    subst_image_subterm[OF x[unfolded l], of \<sigma>] assms(1)[unfolded qrstep_r_p_s_def] l by auto
  then show ?thesis using innermost by auto
qed

lemma step_at_DPos:
  assumes "(s,t) \<in> rew_r_p_s lr p \<sigma>"
  shows "p \<in> DPos s"
proof -
  obtain l r where [simp]: "lr = (l,r)" by force
  from assms[unfolded qrstep_r_p_s_def] have lr: "(l,r) \<in> R" by auto
  from wf_trs_imp_lhs_Fun[OF wf_R lr] obtain f ls where l: "l = Fun f ls" by blast
  from assms(1)[unfolded qrstep_r_p_s_def] obtain \<sigma> where 
    s_p: "s |_ p = l \<cdot> \<sigma>" by auto
  have rt_s_p: "root (s |_ p) = root l" unfolding l s_p  by auto  
  obtain f where "root (s |_ p) = Some f" and "f \<in> D"
    unfolding rt_s_p
    using lr defs_R[unfolded defined_def] unfolding l by fastforce
  then show ?thesis unfolding DPos_def l using qrstep_r_p_s_conv(1)[OF assms(1)] by force
qed

lemma step_at_RPos:
  assumes "(s,t) \<in> rew_r_p_s lr p \<sigma>"
  shows "p \<in> RPos s"
  unfolding RPos_def
  proof (auto)
    from step_at_DPos[OF assms] show p_in_dposs_s: "p \<in> DPos s".
    from qrstep_subt_at[OF assms] have "s |_ p \<rightarrow> t |_ p" 
    using qrstep_qrstep_r_p_s_conv by blast
  then show "\<exists> u. s |_ p \<rightarrow> u" by auto
qed

lemma RPos_step_approx: 
  assumes pstep: "(s,t) \<in> rew_r_p_s lr p \<sigma>" 
  shows "RPos t \<subseteq> {q. q \<in> RPos s \<and> (q <\<^sub>p p \<or> q \<bottom> p)} \<union> {p @ q | q. q \<in> DPos (snd lr)}" (is "_ \<subseteq> ?old \<union> ?fresh")
proof
  let ?l = "fst lr"
  let ?r = "snd lr"
  fix q
  assume *: "q \<in> RPos t"
  show "q \<in> ?old \<union> ?fresh"
  proof - 
    have p_in_poss_s: "p \<in> poss s" and p_in_poss_t : "p \<in> poss t" and shape_s: "s = replace_at s p (?l \<cdot> \<sigma>)"
      using qrstep_r_p_s_conv[OF pstep] by auto
    have t_p: "t |_ p = ?r \<cdot> \<sigma>" using subt_at_ctxt_of_pos_term[OF _ p_in_poss_t] qrstep_r_p_s_conv[OF pstep] by auto

    from *[unfolded RPos_def] obtain u where 
      qstep: "t|_q \<rightarrow> u" and
      q_in_DPos_t: "q \<in> DPos t"
      by auto 
    then have q_in_poss_t: "q \<in> poss t" unfolding DPos_def by auto
    from q_in_DPos_t have q_in_funnpos_t: "q \<in> fun_poss t" using DPos_subseteq_fun_poss by auto

    {
      assume le: "p \<le>\<^sub>p q" 
      obtain p' where p': "q = p @ p'" using prefix_pos_diff[OF le,symmetric] by auto
      then have 
        t_q: "t |_ q = ?r \<cdot> \<sigma> |_ p'" 
        and p'_in_poss_rsigma: "p' \<in> poss (?r \<cdot> \<sigma>)" 
        using subterm_poss_conv[OF q_in_poss_t p' t_p] by auto

      { 
        assume p'_notin_fun_poss_r: "p' \<notin> fun_poss ?r"
        obtain p1 p2 x
          where p'_decomposed: "p' = p1 @ p2"
          and p1_in_poss_r: "p1 \<in> poss ?r"
          and p1_var_poss: "?r |_ p1 = Var x"
          and p2_in_subst: "p2 \<in> poss (\<sigma> x)"
          using poss_subst_apply_term[OF p'_in_poss_rsigma p'_notin_fun_poss_r].
        have t_q_in_subst: "\<sigma> x \<unrhd> t |_ q"
          unfolding t_q p'_decomposed 
            subt_at_append[OF poss_imp_subst_poss[OF p1_in_poss_r]]
            subt_at_subst[OF p1_in_poss_r]
            p1_var_poss
          using subt_at_imp_supteq[OF p2_in_subst] by auto
        have "x \<in> vars_rule lr" 
          using subt_at_imp_supteq[OF p1_in_poss_r, unfolded p1_var_poss] subteq_Var_imp_in_vars_term 
          unfolding vars_rule_def by force
        then have "(\<sigma> x) \<in> NF_trs R" using rew_r_p_s_imp_NF_subst[OF pstep, of x] by auto
        from NF_subterm[OF this t_q_in_subst] have "t |_q \<in> NF_trs R".
        then have t_q_nf: "t |_ q \<in> NF (qrstep False Q R)" 
          using NF_anti_mono[OF qrstep_subset_rstep] innermost by force
        from NF_no_step[OF t_q_nf] qstep have False by blast
      }
      then have p'_in_fun_poss_r: "p' \<in> fun_poss ?r" by auto
      have p'_in_poss_r: "p' \<in> poss ?r" using fun_poss_imp_poss[OF p'_in_fun_poss_r].
      from fun_poss_fun_conv[OF p'_in_fun_poss_r] obtain f ts where rp': "?r |_ p' = Fun f ts" by auto
      let ?root = "root (?r |_ p')"
      from rp' have "?root = root(?r |_ p' \<cdot> \<sigma>)" unfolding rp' by simp
      also have "... = root(t |_ q)" unfolding t_q using p'_in_poss_r by simp
      finally have rt_r_p': "?root = root(t |_ q)" .
      then obtain f n where "?root = Some (f,n)" and "(f,n) \<in> D" using 
        q_in_DPos_t[unfolded DPos_def] q_in_poss_t by auto
      then have "p' \<in> DPos ?r" unfolding DPos_def using p'_in_poss_r by auto
      then have ?thesis using p' by auto
    }
    note q_geq_p = this

    {
      assume p_gt_q: "q <\<^sub>p p"
      then obtain p' where p' : "p = q @ p'" and ne: "p' \<noteq> []" using less_pos_def' by auto
      have step_at_q: "(s |_ q, t |_ q) \<in> nrqrstep False Q R"
        using qrstep_r_p_s_imp_nrqrstep[OF qrstep_subt_at_gen[OF pstep[unfolded p']] ne] .
      from nrqrstep_preserves_root[OF this]
      obtain f n where 
        "root (s |_ q) = Some (f,n)" and
        "(f,n) \<in> D"
        using q_in_poss_t q_in_DPos_t[unfolded DPos_def] by auto
      then have "q \<in> DPos s" unfolding DPos_def 
        using poss_append_poss p_in_poss_s[unfolded p'] by auto
      then have "q \<in> ?old" using step_at_q 
        unfolding RPos_def
        using qrstep_iff_rqrstep_or_nrqrstep p_gt_q
        by blast
      then have ?thesis by auto
    } 
    note p_gt_q = this
    
    {
      assume p_par_q: "p \<bottom> q"
      have q_in_poss_s: "q \<in> poss s" unfolding shape_s[unfolded qrstep_r_p_s_conv(6)[OF pstep, symmetric]] 
        using parallel_poss_replace_at[OF p_par_q p_in_poss_t] q_in_poss_t by auto
      have "s |_ q = t |_ q" using parallel_qrstep_subt_at[OF pstep p_par_q q_in_poss_s] by auto
      then obtain f n where 
        "root(s |_ q) = Some (f,n)"
        and "(f,n) \<in> D"
        and step_q: "s |_ q \<rightarrow> u"
        using *[unfolded RPos_def DPos_def] qstep by auto
      then have "q \<in> DPos s"using q_in_poss_s unfolding DPos_def by blast
      then have ?thesis using step_q parallel_pos_sym[OF p_par_q] unfolding RPos_def by blast
    }
    note q_par_q = this
    show ?thesis using q_geq_p p_gt_q q_par_q pos_cases by auto
  qed
qed
end

locale pre_DT_trans =
  sharp_syntax shp +
  pre_innermost_wf D R Q
    for shp :: "'f \<Rightarrow> 'f" and D :: "'f sig" and R :: "('f, 'v) trs" and Q :: "('f, 'v) terms" +
  fixes F :: "'f sig"
    and Ds :: "'f sig"
begin

definition is_DT_of :: "('f, 'v) rule \<Rightarrow> ('f, 'v) rule \<Rightarrow> bool"
where 
  "is_DT_of lr uv \<longleftrightarrow>
    fst uv = \<sharp>(fst lr) \<and> (\<exists> C qs. snd uv =\<^sub>f (C, [\<sharp>(snd lr |_ q). q \<leftarrow> qs]) \<and> set qs = DPos (snd lr))"

definition goodFor :: "('f, 'v) term  \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<lless>" 55)
where
  "goodFor t u \<longleftrightarrow> (\<exists> C ps. u =\<^sub>f (C, [\<sharp>(t |_ p). p \<leftarrow> ps]) \<and> RPos t = set ps \<and> funas_term t \<subseteq> F)"

end

locale DT_trans =
  innermost_wf D R Q +
  pre_DT_trans shp D R Q F Ds for D :: "'f sig" 
    and R :: "('f, 'v) trs" 
    and Q :: "('f, 'v) terms" 
    and F :: "'f sig"
    and shp :: "'f \<Rightarrow> 'f"
    and Ds :: "'f sig"
    and Q' :: "('f, 'v) terms" +
  assumes [simp]: "Ds = \<sharp> D"
    and R_sig: "funas_trs R \<subseteq> F"
    and D_subseteq_F: "D \<subseteq> F"
    and Ds_fresh: "Ds \<inter> F = {}"
    and Q': "Q' \<subseteq> Q \<union> { Fun f ts | f ts. (f, length ts) \<notin> F }"
begin

abbreviation "rew_r_p_s' \<equiv> qrstep_r_p_s False Q' R"
abbreviation "rew' \<equiv> qrstep False Q' R"

lemma NF_termsQ'I:
  assumes sQ: "s \<in> NF_terms Q" and sF: "funas_term s \<subseteq> F"
  shows "s \<in> NF_terms Q'"
proof -
  let ?Q' = "{Fun f ts |f ts. (f, length ts) \<notin> F}"
  have sQ': "s \<in> NF_terms ?Q'"
  proof
    fix C l and \<sigma> :: "('f,'v)subst"
    assume s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and l: "l \<in> ?Q'"
    from sF[unfolded s] have "funas_term l \<subseteq> F" by (auto simp: funas_term_subst)
    with l show False by (cases l, auto)
  qed
  have s: "s \<in> NF_terms (Q \<union> ?Q')"
    unfolding NF_trs_union Id_on_union using sQ' sQ by auto
  show ?thesis by (rule set_mp[OF NF_trs_mono s], insert Q', auto)
qed

lemma rew_r_p_s'I:
  assumes st: "(s, t) \<in> rew_r_p_s lr p \<sigma>"
    and F: "p \<in> poss s \<Longrightarrow> \<Union> (funas_term ` set (args (s |_ p))) \<subseteq> F"
  shows "(s, t) \<in> rew_r_p_s' lr p \<sigma>"
proof -
  obtain l r where lr: "lr = (l,r)" by force
  note d = qrstep_r_p_s_def
  from st[unfolded d lr]
  have Q: "(\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q)" and p: "p \<in> poss s" and lr': "(l, r) \<in> R" and id: "s |_ p = l \<cdot> \<sigma>"
    and t: "t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  {
    fix u
    assume u: "u \<in> set (args (s |_ p))"
    let ?Q' = "{Fun f ts |f ts. (f, length ts) \<notin> F}"
    from u Q[folded id NF_terms_args_conv] have Q: "u \<in> NF_terms Q" by auto
    from u F[OF p] have F: "funas_term u \<subseteq> F" by auto
    have "u \<in> NF_terms Q'"
      by (rule NF_termsQ'I[OF Q F])
  }
  then have "\<forall>u\<in>set (args (s |_ p)). u \<in> NF_terms Q'" by auto
  from this[unfolded id NF_terms_args_conv] p lr' id t
  show ?thesis unfolding d lr by auto
qed

lemma funas_sharp_term: "funas_term ` set (args (\<sharp> s)) = funas_term ` set (args s)"
  by  (cases s, auto)

lemma rew_r_p_s'I_full:
  assumes st: "(s,t) \<in> rew_r_p_s lr p \<sigma>"
    and F: "\<Union> (funas_term ` set (args s)) \<subseteq> F"
  shows "(s,t) \<in> rew_r_p_s' lr p \<sigma>"
proof (rule rew_r_p_s'I[OF st subset_trans[OF _ F]], intro subsetI)
  fix f
  assume p: "p \<in> poss s"
    and f: "f \<in> \<Union>(funas_term ` set (args (s |_ p)))"
  show "f \<in> \<Union>(funas_term ` set (args s))"
  proof (cases p)
    case Nil
    then show ?thesis using f by auto
  next
    case (Cons i q)
    with p obtain g ss where s: "s = Fun g ss" and i: "i < length ss" and q: "q \<in> poss (ss ! i)" 
      by (cases s, auto)
    then have mem: "ss ! i \<in> set (args s)" by auto
    from Cons have "s |_ p = ss ! i |_ q" unfolding s by simp
    from f[unfolded this]
    obtain t where "t \<in> set (args (ss ! i |_ q))" and f: "f \<in> funas_term t" by auto
    then obtain g ts where sp: "ss ! i |_ q = Fun g ts" and t: "t \<in> set ts" by (cases "ss ! i |_ q", auto)
    from ctxt_supt_id[OF q] obtain C where s: "ss ! i = C \<langle> ss ! i |_ q \<rangle>" by metis
    from this[unfolded sp] t f have "f \<in> funas_term (ss ! i)" by auto
    with mem show ?thesis by auto
  qed
qed


subsection \<open>Tuple Transformation\<close>

lemma nrqrstep_r_p_s_imp_sharp_qrstep_r_p_s: 
  assumes ne: "p \<noteq> []"
    and step: "(s, t) \<in> rew_r_p_s lr p \<sigma>"
  shows "(\<sharp> s, \<sharp> t) \<in> rew_r_p_s lr p \<sigma>"
proof -
  let ?C = "ctxt_of_pos_term p s"
  from qrstep_r_p_s_conv[OF step] have s: "s = ?C\<langle>fst lr\<cdot>\<sigma>\<rangle>" and t: "t = ?C\<langle>snd lr\<cdot>\<sigma>\<rangle>" and p: "p \<in> poss s" by auto
  from ne obtain f D bef aft where C: "?C = More f bef D aft"
    using hole_pos_ctxt_of_pos_term[OF p] ctxt_to_term_list.cases hole_pos.simps(1) by metis
  from s t have s: "s = Fun f (bef @ D\<langle>fst lr\<cdot>\<sigma>\<rangle>  # aft)" and t: "t = Fun f (bef @ D\<langle>snd lr\<cdot>\<sigma>\<rangle> # aft)" unfolding C intp_actxt.simps(2) by auto
  let ?C' = "More (\<sharp> f) bef D aft"
  
  from hole_pos_ctxt_of_pos_term[OF p, unfolded C] have hole_pos_C': "hole_pos ?C' = p" by simp
  from s t have 
    s_sharp: "\<sharp> s = ?C'\<langle>fst lr\<cdot>\<sigma>\<rangle>" and 
    t_sharp: "\<sharp> t = ?C'\<langle>snd lr\<cdot>\<sigma>\<rangle>" by simp+
  moreover have "ctxt_of_pos_term p (\<sharp> s) = ?C'" using s_sharp hole_pos_C' by fastforce
  moreover have "\<sharp> s |_ p = fst lr \<cdot> \<sigma>" and "\<sharp> t |_ p = snd lr \<cdot> \<sigma>"
    unfolding s_sharp t_sharp using hole_pos_C' subt_at_hole_pos by auto
  moreover from hole_pos_C' have "p \<in> poss (\<sharp> s)" unfolding s_sharp using hole_pos_in_possc by auto
  ultimately show ?thesis using step unfolding qrstep_r_p_s_def  by auto 
qed

lemma step_to_dt_step:
  assumes step: "(s, t) \<in> qrstep_r_p_s False Q'' R lr p \<sigma>"
    and dt: "is_DT_of lr uv"
  obtains C t' qs where 
  "t' =\<^sub>f(C, [\<sharp>(t |_ (p @ q)) . q \<leftarrow> qs])" and
  "set qs = DPos (snd lr)" and
  "(\<sharp>(s |_ p), t') \<in> qrstep False Q'' {uv}"
proof -
  let ?C = "ctxt_of_pos_term p s"
  let ?r = "snd lr"

  from qrstep_r_p_s_conv[OF step] replace_at_subt_at
  have s_p: "s |_ p = fst lr \<cdot> \<sigma>" and t_p: "t |_ p = ?r \<cdot> \<sigma>" by metis+
  from dt[unfolded is_DT_of_def] have u: "fst uv = \<sharp> (fst lr)" by auto
  have "lr \<in> R" using step[unfolded qrstep_r_p_s_def] by auto
  then have wf_l: "is_Fun (fst lr)"  using wf_R[unfolded wf_trs_def] 
    unfolding wf_rule_def by (metis is_FunI surjective_pairing)
  then have  u_match: "\<sharp> (s |_ p) = fst uv \<cdot> \<sigma>" proof (cases "fst lr", insert s_p u, auto) qed 

  from dt[unfolded is_DT_of_def] obtain C qs where
    v: "snd uv =\<^sub>f (C,[\<sharp> (?r |_ q) . q \<leftarrow> qs])" (is "snd uv =\<^sub>f (C,?us)") and
    qs: "set qs = DPos ?r"
    by auto
  
  from wf_l step[unfolded qrstep_r_p_s_def] u have
    NF: "\<forall>u\<lhd> fst uv \<cdot> \<sigma>. u \<in> NF_terms Q''" proof (cases "fst lr", auto) qed
  from qrstep.subst[OF this] NF_subst_False 
  have dp_step: "(\<sharp> (s |_ p), fill_holes C ?us \<cdot> \<sigma>) \<in> qrstep False Q'' {uv}" 
    unfolding u_match  eqfE(1)[OF v, symmetric]
    using insertI1 surjective_pairing by auto
  
  { 
    fix q
    assume q_in_qs: "q \<in> set qs"
    have q_in_fun_r: "q \<in> fun_poss ?r" 
      using in_mono[OF DPos_subseteq_fun_poss] q_in_qs[unfolded qs] by auto
    have "(?r |_ q) \<cdot> \<sigma> = t|_(p @ q)" 
      using subt_at_subst[OF fun_poss_imp_poss[OF q_in_fun_r], symmetric, of \<sigma>] 
      unfolding t_p[symmetric] subt_at_append[OF \<open>p \<in> poss t\<close>] by auto
    then have "\<sharp> (?r |_ q) \<cdot> \<sigma> = \<sharp> (t|_(p @ q))"
      using fun_poss_fun_conv[OF q_in_fun_r] by auto
  } then have "\<And> q. q \<in> set qs \<longrightarrow> (\<lambda> x . \<sharp> (?r |_ x) \<cdot> \<sigma>) q = (\<lambda> x . \<sharp> (t|_(p @ x))) q" by metis

  from subst_apply_mctxt_sound[OF v, of \<sigma>, unfolded map_map o_def  map_ext[OF this]] qs dp_step that 
    eqfE(1)[OF v] show ?thesis by auto
qed

lemma subseq_map_same:
  assumes "subseq xs ys"
    and "\<forall>x \<in> set xs. f x = g x"
  shows "subseq (map f xs) (map g ys)"
  using assms by (induct) auto

lemma one_step_explicit: 
  assumes step: "(s,t) \<in> rew_r_p_s lr p \<sigma>"
    and dt: "is_DT_of lr lr'"
    and good: "s \<lless> u"
  shows "\<exists> v. t \<lless> v \<and> (u,v) \<in> ( rew'\<^sup>* O qrstep False Q' {lr'} )"
proof -
  let ?sharp_at = "\<lambda> tm q. \<sharp> (tm |_ q)"

  from good[unfolded goodFor_def] obtain C rpos_s_list where 
    u_decompose: "u =\<^sub>f (C,[?sharp_at s q . q \<leftarrow> rpos_s_list])" and
    rpos_s_list: "RPos s = set rpos_s_list" and
    sF: "funas_term s \<subseteq> F" 
    by auto
  from step have ps: "p \<in> poss s" unfolding qrstep_r_p_s_def by auto
  from step have step': "(s,t) \<in> rew_r_p_s' lr p \<sigma>"
    by (rule rew_r_p_s'I_full, insert sF, cases s, auto)

  let ?f = "\<lambda> q. if q <\<^sub>p p \<or> q \<bottom> p then ?sharp_at t q else ?sharp_at s q"
  let ?us = "[ ?sharp_at s q . q \<leftarrow> rpos_s_list ]"
  let ?ws = "[ ?f q . q \<leftarrow> rpos_s_list ]"
  
  let ?w = "fill_holes C ?ws"
  {
    fix q
    assume q_in_rpos_s: "q \<in> set rpos_s_list"
    { 
      assume q: "q <\<^sub>p p"
      then have q_diff: "p = q @ pos_diff p q" (is "_ = _ @ ?q'") by auto       
      then have ne: "?q' \<noteq> []" using q less_pos_simps(1) by force
      from ps[unfolded arg_cong[OF q_diff, of "\<lambda> p. p \<in> poss s"]] have qs: "q \<in> poss s" by simp
      have "(s |_ q, t |_ q) \<in> rew_r_p_s lr ?q' \<sigma>" by (metis q_diff qrstep_subt_at_gen step)
      from nrqrstep_r_p_s_imp_sharp_qrstep_r_p_s[OF ne this] have
        step: "(?sharp_at s q, ?f q) \<in> rew_r_p_s lr ?q' \<sigma>" using q by auto
      have "(?sharp_at s q, ?f q) \<in> rew_r_p_s' lr ?q' \<sigma>"
        by (rule rew_r_p_s'I_full[OF step], unfold funas_sharp_term, rule funas_term_subterm_args[OF sF qs])
      then have "(?sharp_at s q, ?f q) \<in> rew'" using qrstep_qrstep_r_p_s_conv by blast
      then have "(?sharp_at s q, ?f q) \<in> rew'\<^sup>*" by auto
    } note q_less_p = this

    { 
      assume q_par_p: "q \<bottom> p"
      from q_in_rpos_s have "q \<in> poss s" 
        unfolding rpos_s_list[symmetric] RPos_def DPos_def by auto
      from parallel_qrstep_subt_at[OF step _ this] have "?f q = ?sharp_at s q" 
        using q_par_p parallel_pos_sym by auto
      then have "(?sharp_at s q, ?f q) \<in> rew'\<^sup>*" by auto
    } note q_par_p_p = this

    { 
      assume q: "\<not> (q <\<^sub>p p \<or> q \<bottom> p)"
      then have "?f q = ?sharp_at s q" by auto
      then have "(?sharp_at s q, ?f q) \<in> rew'\<^sup>*" by auto
    } note q_nless_p = this

    have "(?sharp_at s q, ?f q) \<in> rew'\<^sup>*" using q_par_p_p q_less_p q_nless_p by auto
  } note repair_step = this
  
  { 
    fix j
    assume "j < length ?ws"
    then have "(?us!j,?ws!j) \<in> rew'\<^sup>*" using repair_step rpos_s_list by auto
  } 
  
  from eqf_all_ctxt_closed_step[OF all_ctxt_closed_qrsteps u_decompose this] length_map 
  have repair_steps: "(u,?w) \<in> (rew'\<^sup>*)" by auto

  obtain Dp t' dpos_r_list where
    t': "t' =\<^sub>f (Dp, [?sharp_at t (p @ q) . q \<leftarrow> dpos_r_list])"
    and dpos_r_list_dpos: "set dpos_r_list = DPos (snd lr)"
    and p_step: "(?sharp_at s p, t') \<in> qrstep False Q' {lr'}"
    using step_to_dt_step[OF step' dt] by metis

  let ?rs = "[?sharp_at t (p @ q) . q \<leftarrow> dpos_r_list]"
  obtain i where 
    rpos_s_list_i: "rpos_s_list!i = p" and 
    i_index_rpos_s_list: "i < length rpos_s_list" 
    using rpos_s_list step_at_RPos[OF step] List.in_set_conv_nth[of p rpos_s_list] by auto
  let ?rpos_s_left = "take i rpos_s_list"
  let ?rpos_s_right = "drop (Suc i) rpos_s_list"


  have i_index_ws: "i < length ?ws" using i_index_rpos_s_list by auto
  have nh_C_l_ws: "num_holes C = length ?ws" using eqfE[OF u_decompose] length_map by auto

  from fill_holes_ctxt[OF this i_index_ws] obtain C' where 
    C': "\<And> s. fill_holes C (?ws[i := s]) = C' \<langle> s \<rangle>" by auto
  
  let ?v = "fill_holes C (?ws[i := t'])"
  have ws_i: "?ws!i = ?sharp_at s p" 
    unfolding nth_map[OF i_index_rpos_s_list] rpos_s_list_i  
    using less_irrefl parallel_pos order_refl by auto
  then have "?ws = ?ws[i := ?sharp_at s p]" unfolding ws_i[symmetric] using  list_update_id[of ?ws i] by auto
  from this C' have C'ws: "?w = C'\<langle>?sharp_at s p\<rangle>" by (metis (lifting))
  from C' have C'vs: "?v = C'\<langle>t'\<rangle>" by (metis (lifting))
  
  have dp_step: "(fill_holes C ?ws, ?v) \<in> qrstep False Q' {lr'}" unfolding C'ws C'vs using qrstep.ctxt[OF p_step] .

  from repair_steps dp_step have step_simulation: "(u,?v) \<in> ( rew'\<^sup>* O qrstep False Q' {lr'} )" by auto

  let ?ws_left = "[ ?f q . q \<leftarrow> ?rpos_s_left]"
  let ?ws_right = "[ ?f q . q \<leftarrow> ?rpos_s_right]"
  have sep: "?ws_left @ t' # ?ws_right = ?ws[i := t']" 
    unfolding take_map[symmetric] drop_map[symmetric]
    using id_take_nth_drop[OF i_index_ws] upd_conv_take_nth_drop[OF i_index_ws] by auto
  let ?vs = "?ws_left @ ?rs @ ?ws_right"
  let ?D = "compose_mctxt C i Dp"

  have len_left: "length ?ws_left = i" using length_take i_index_rpos_s_list by auto
  moreover have "?v =\<^sub>f (C,?ws_left @ t' # ?ws_right)" unfolding sep using nh_C_l_ws by auto
  ultimately have v_decompose_D: "?v =\<^sub>f (?D, ?vs)" 
    using compose_mctxt_sound[OF _ t'] by (metis (lifting, no_types))


  let ?filter_old = "filter (\<lambda> q. q \<in> RPos s \<and> (q <\<^sub>p p \<or> q \<bottom> p))"
  let ?qs = "(?filter_old ?rpos_s_left) @ [p @ q . q \<leftarrow> dpos_r_list] @ (?filter_old ?rpos_s_right)"
  let ?rpos_t_list = "[q \<leftarrow> ?qs. q \<in> RPos t]"
  have good_RPos: "RPos t = set ?rpos_t_list" proof
    {
      fix q
      assume q_in_rpos_t: "q \<in> RPos t"
      then have q_in_approx: "q \<in> {q. q \<in> RPos s \<and> (q <\<^sub>p p \<or> q \<bottom> p)} \<or> q \<in> {p @ q | q. q \<in> DPos (snd lr)}" (is "_ \<in> ?old \<or> _ \<in> ?new") 
        using RPos_step_approx[OF step] by auto
      {
        assume q_in_old: "q \<in> ?old"
        then have "q <\<^sub>p p \<or> q \<bottom> p" by auto then have q_noteq_p: "q \<noteq> p" using less_pos_def parallel_pos by auto

        have "q \<in> set rpos_s_list" using q_in_old rpos_s_list by auto 
        then have "q \<in> set (?rpos_s_left @ rpos_s_list!i # ?rpos_s_right)" 
          by (metis i_index_rpos_s_list id_take_nth_drop)
        then have "q \<in> set (?rpos_s_left @ ?rpos_s_right)" 
          unfolding rpos_s_list_i using q_noteq_p by auto
        then have "q \<in> set ?qs" using q_in_old by auto
      } note q_in_old = this
      { 
        assume q_in_new: "q \<in> ?new"
        then have "q \<in> set ?qs" unfolding dpos_r_list_dpos[symmetric] by auto
      } note q_in_new = this
      
      from q_in_approx q_in_old q_in_new q_in_rpos_t have "q \<in> set ?rpos_t_list" by auto
    }
    then show "RPos t \<subseteq> set ?rpos_t_list" by auto
    next show "set ?rpos_t_list \<subseteq> RPos t" by auto
  qed

  { fix q 
    fix pos_lst
    assume "q \<in> set (?filter_old pos_lst)"
    then have "q <\<^sub>p p \<or> q \<bottom> p" by auto then have "?sharp_at t q = ?f q" by simp
  } 
  then have f_of_q_in_filter_old: "\<And> pos_lst. \<forall> q \<in> set (?filter_old pos_lst). ?sharp_at t q = ?f q" by blast

  have good_sharp: "subseq [?sharp_at t q . q \<leftarrow> ?rpos_t_list] ?vs"
    proof -
      have left: "subseq [ ?sharp_at t q. q \<leftarrow> ?filter_old ?rpos_s_left] ?ws_left" (is "subseq ?lft _")
        using subseq_map_same [OF subseq_filter_left f_of_q_in_filter_old] .
      
      have right: "subseq [ ?sharp_at t q. q \<leftarrow> ?filter_old ?rpos_s_right] ?ws_right" (is "subseq ?rght _")
        using subseq_map_same [OF subseq_filter_left f_of_q_in_filter_old] .

      have middle: "subseq [ ?sharp_at t q . q \<leftarrow> [(p @ q'). q' \<leftarrow> dpos_r_list]] ?rs" (is "subseq ?mid _") 
        unfolding map_map  comp_def by auto

      have "[?sharp_at t q. q \<leftarrow> ?qs ] = ?lft @ ?mid @ ?rght" 
        unfolding map_append by simp
      then have "subseq [?sharp_at t q. q \<leftarrow> ?qs ] ?vs" using left middle right list_emb_append_mono
        by (metis (lifting, no_types))
      then show ?thesis using subseq_filter_left subseq_map subseq_trans by blast
    qed

  from step have "(s,t) \<in> qrstep False Q R" unfolding qrstep_qrstep_r_p_s_conv by blast
  then have "(s,t) \<in> rstep R" by auto
  from rstep_preserves_funas_terms[OF R_sig sF this wf_R] have tF: "funas_term t \<subseteq> F" .

  from mctxt_fill_partially[OF good_sharp v_decompose_D] obtain C' where
    "?v =\<^sub>f (C',[?sharp_at t q . q \<leftarrow> ?rpos_t_list])" by auto
  from v_decompose_D good_RPos tF this
  have good: "t \<lless> ?v" unfolding goodFor_def
    by (metis (lifting, no_types))
  then show ?thesis using step_simulation by auto
qed


context
  fixes S W DT_S DT_W :: "('f, 'v) trs" and nfs :: bool
  assumes DT_S: "\<And> lr. lr \<in> S \<Longrightarrow> \<exists> dt \<in> DT_S. is_DT_of lr dt"
    and DT_W: "\<And> lr. lr \<in> W \<Longrightarrow> \<exists> dt \<in> DT_W. is_DT_of lr dt"
    and S: "S \<subseteq> R"
    and W: "W \<subseteq> R"
    and nfs: "nfs = False"
begin

lemma one_step_generic: 
  assumes good: "s \<lless> u"
    and step: "(s, t) \<in> qrstep nfs' Q S_W"
    and DT: "\<And> lr. lr \<in> S_W \<Longrightarrow> \<exists> dt \<in> DT. is_DT_of lr dt"
    and S_W: "S_W \<subseteq> R"
  shows "\<exists> v. t \<lless> v \<and> (u, v) \<in> ( (qrstep nfs Q' R)\<^sup>* O qrstep nfs Q' DT)"
proof -
  from step[unfolded qrstep_qrstep_r_p_s_conv] obtain lr p \<sigma>
    where step: "(s, t) \<in> qrstep_r_p_s nfs' Q S_W lr p \<sigma>" by auto
  from step have lr: "lr \<in> S_W" unfolding qrstep_r_p_s_def by auto
  from DT[OF this] obtain dt where dt: "dt \<in> DT" and dt_of: "is_DT_of lr dt" by auto
  from lr S_W step have "(s,t) \<in> qrstep_r_p_s False Q R lr p \<sigma>" unfolding qrstep_r_p_s_def by auto
  from one_step_explicit[OF this dt_of good]
  obtain v where tv: "t \<lless> v" and uv: "(u, v) \<in> rew'\<^sup>* O qrstep nfs Q' {dt}" by (auto simp: nfs)
  from dt qrstep_mono[OF _ subset_refl] have "qrstep nfs Q' {dt} \<subseteq> qrstep nfs Q' DT"
    by (metis qrstep_rule_conv subrelI)
  with uv have "(u,v) \<in> rew'\<^sup>* O qrstep nfs Q' DT" by auto
  with tv show ?thesis unfolding nfs by blast
qed

lemma many_relative_steps: 
  assumes good: "s \<lless> u"
    and step: "(s, t) \<in> (relto (qrstep nfs' Q S) (qrstep nfs' Q W))^^n"
  shows "\<exists> v. t \<lless> v \<and> (u, v) \<in> (relto (qrstep nfs Q' DT_S) (qrstep nfs Q' (R \<union> DT_W)))^^n"
proof -
  let ?S = "qrstep nfs Q' DT_S"
  let ?W = "qrstep nfs Q' DT_W"
  let ?R = "qrstep nfs Q' R"
  let ?RW = "qrstep nfs Q' (R \<union> DT_W)"
  have main: "\<exists> v. t \<lless> v \<and> (u, v) \<in> (relto (?R^* O ?S) (?R^* O ?W))^^n"
    by (rule simulate_conditional_relative_steps_count[of "\<lambda> s t. s \<lless> t", 
      OF one_step_generic[OF _ _ DT_S S] one_step_generic[OF _ _ DT_W W] step good])
  have "relto (?R^* O ?S) (?R^* O ?W) \<subseteq> relto ?S ?RW" unfolding qrstep_union by regexp
  from relpow_mono[OF this, of n] main
  show ?thesis by blast
qed

lemma dependency_tuples_sound: 
  assumes bound: "deriv_bound_measure_class 
    (relto (qrstep nfs Q' DT_S) (qrstep nfs Q' (R \<union> DT_W))) 
    (Runtime_Complexity C' D'') cc"
    and D': "D \<subseteq> set D'"
    and C': "set C' \<inter> D = {}"
    and CD'_F: "set C' \<union> set D' \<subseteq> F"
    and D'': "set D'' = (\<lambda>(f, n). (\<sharp> f, n)) ` set D'"
  shows "deriv_bound_measure_class 
    (relto (qrstep nfs' Q S) (qrstep nfs' Q W)) 
    (Runtime_Complexity C' D') cc"  
proof -
  let ?D = "relto (qrstep nfs Q' DT_S) (qrstep nfs Q' (R \<union> DT_W))"
  let ?R = "relto (qrstep nfs' Q S) (qrstep nfs' Q W)"
  let ?T = "terms_of_nat (Runtime_Complexity C' D')"
  let ?TS = "terms_of_nat (Runtime_Complexity C' D'')"
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def
  note d' = deriv_bound_rel_def
  note d'' = deriv_bound_def
  from bound[unfolded d] obtain f where
    f: "f \<in> O_of cc" and bound: "deriv_bound_rel ?D ?TS f" by blast
  show ?thesis unfolding d
  proof (intro exI[of _ f] conjI[OF f], unfold d' d'', clarify)
    fix n s t
    assume sT: "s \<in> ?T n" and st: "(s,t) \<in> ?R  ^^ Suc (f n)"
    from sT CD'_F have sF: "funas_term s \<subseteq> F"
      by (cases s) (auto simp: funas_args_term_def)
    from relpow_Suc_E2[OF st] obtain u where "(s,u) \<in> ?R" by metis
    then have "(s,u) \<in> (qrstep nfs' Q (S \<union> W))^+" unfolding qrstep_union by regexp
    then obtain u where "(s,u) \<in> qrstep nfs' Q (S \<union> W)" by (induct, auto)
    with S W qrstep_all_mono[OF _ subset_refl, of "S \<union> W" R Q False nfs'] 
    have su: "(s,u) \<in> rew" by auto
    let ?s = "\<sharp> s"
    have ss: "?s \<in> ?TS n" using sT by (cases s) (auto simp: D'' funas_args_term_def)
    have rpos: "RPos s = {[]}"
    proof -
      from sT obtain f ss where s: "s = Fun f ss" by auto
      let ?n = "length ss"
      let ?f = "(f,?n)"
      from sT s have f: "?f \<in> set D'"
      and args: "\<And> s. s \<in> set ss \<Longrightarrow> funas_term s \<subseteq> set C'" by (auto simp: funas_args_term_def)
      {
        fix p
        assume "p \<in> RPos s"
        with RPos_subseteq_DPos have "p \<in> DPos s" by auto
        from this[unfolded DPos_def] obtain g where 
          p: "p \<in> poss s" and root: "root (s |_ p) = Some g" and g: "g \<in> D" by auto        
        {
          assume "p \<noteq> []"
          then obtain i q where pq: "p = i # q" by (cases p, auto)
          with p s root have mem: "ss ! i \<in> set ss" and q: "q \<in> poss (ss ! i)" 
            and root: "root (ss ! i |_ q) = Some g" by auto
          from root q have "g \<in> funas_term (ss ! i)" unfolding funas_term_poss_conv
            by (cases "ss ! i |_ q", auto)
          with args[OF mem] have "g \<in> set C'" by auto
          with C' g have False by auto
        }
        then have "p = []" by auto
      } note eps = this
      moreover {
        from su[unfolded qrstep_qrstep_r_p_s_conv] obtain lr p \<sigma> where 
          su: "(s, u) \<in> rew_r_p_s lr p \<sigma>" by auto
        from step_at_RPos[OF this] have "p \<in> RPos s" by auto
        with eps[OF this] have "[] \<in> RPos s" by simp
      }
      ultimately show ?thesis by auto
    qed
    have "s \<lless> ?s" unfolding goodFor_def
      by (rule exI[of _ MHole], rule exI[of _ "[[]]"], auto simp: rpos sF)
    from many_relative_steps[OF this st] obtain v where
      "(\<sharp> s, v) \<in> ?D ^^ Suc (f n)" by auto
    from deriv_bound_steps[OF this bound[unfolded d', rule_format, OF ss]]
    show False by simp
  qed
qed

end

end

end
