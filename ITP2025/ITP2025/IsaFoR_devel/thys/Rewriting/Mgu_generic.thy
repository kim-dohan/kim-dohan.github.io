theory Mgu_generic
  imports 
    First_Order_Rewriting.Unification_More
    Auxx.RenamingN
begin

definition
  mgu_var_disjoint_list_generic ::
    "(nat \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term)list \<Rightarrow> 
      (('f,'v)subst list \<times> ('f, 'v) subst) option"
where
  "mgu_var_disjoint_list_generic rename_many' ren_l sls = (
     let pairs = map (\<lambda> (i, (si, li)). (map_vars_term (rename_many' i) si, map_vars_term ren_l li)) (zip [0 ..< length sls] sls)
     in case unify pairs [] of 
       None \<Rightarrow> None
     | Some \<gamma>list \<Rightarrow> let \<gamma> = subst_of \<gamma>list in 
        Some (map (\<lambda> i. \<gamma> \<circ> rename_many' i) [0 ..< length sls], \<gamma> \<circ> ren_l))"

lemma  mgu_var_disjoint_list_generic_sound: 
  assumes unif: "mgu_var_disjoint_list_generic rename_many' ren_l sls = Some (\<mu> , \<tau>)"
  shows "i < length sls \<Longrightarrow> fst(sls!i) \<cdot> \<mu>!i = snd(sls!i) \<cdot> \<tau>"
    "length \<mu> = length sls" 
proof -
  let ?pairs = "map (\<lambda> (i, (si, li)). (map_vars_term (rename_many' i) si, map_vars_term ren_l li)) (zip [0 ..< length sls] sls)"
  obtain \<gamma>list where 
    unif2:"unify ?pairs [] = Some \<gamma>list" using assms
    unfolding mgu_var_disjoint_list_generic_def by (auto split: option.splits)
  let ?\<gamma> = "subst_of \<gamma>list"
  from unif[unfolded mgu_var_disjoint_list_generic_def Let_def unif2, simplified]
  have mu: "\<mu> = map (\<lambda>i. ?\<gamma> \<circ> rename_many' i) [0..<length sls]" 
    and tau: "\<tau> = ?\<gamma> \<circ> ren_l" by auto
  show "length \<mu> = length sls" unfolding mu by simp
  assume i: "i < length sls" 
  with mu have mui: "\<mu> ! i = ?\<gamma> \<circ> rename_many' i" by auto 
  from unify_sound[OF unif2]
  have unify: "\<And> s t. (s, t) \<in> set ?pairs \<Longrightarrow> s \<cdot> ?\<gamma> = t \<cdot> ?\<gamma>" 
    by (auto simp:is_imgu_def unifiers_def)
  from i unify have "fst (?pairs ! i) \<cdot> ?\<gamma> = snd (?pairs ! i) \<cdot> ?\<gamma>" 
    unfolding set_conv_nth by force
  also have "fst (?pairs ! i) = map_vars_term (rename_many' i) (fst (sls ! i))" using i
    by (auto split: prod.splits)
  also have "snd (?pairs ! i) = map_vars_term ren_l (snd (sls ! i))" using i 
    by (cases "sls ! i", auto)
  finally 
  have "map_vars_term (rename_many' i) (fst(sls!i)) \<cdot> ?\<gamma> = map_vars_term ren_l (snd(sls!i)) \<cdot> ?\<gamma>" .
  also have "map_vars_term (rename_many' i) (fst(sls!i)) \<cdot> ?\<gamma> = fst (sls ! i) \<cdot> (Var \<circ> rename_many' i) \<circ>\<^sub>s subst_of \<gamma>list"  
    unfolding map_vars_term_eq subst_subst ..
  also have "(Var \<circ> rename_many' i) \<circ>\<^sub>s subst_of \<gamma>list = \<mu>!i" unfolding mui subst_compose_def
    by auto
  also have "map_vars_term ren_l (snd(sls!i)) \<cdot> ?\<gamma> = snd (sls ! i) \<cdot> (Var \<circ> ren_l) \<circ>\<^sub>s subst_of \<gamma>list" 
    unfolding map_vars_term_eq subst_subst ..
  also have "(Var \<circ> ren_l) \<circ>\<^sub>s subst_of \<gamma>list = \<tau>" unfolding tau subst_compose_def
    by auto
  finally show "fst (sls ! i) \<cdot> \<mu> ! i = snd (sls ! i) \<cdot> \<tau>" .
qed

context
  fixes ren :: "'v :: infinite renamingN"
begin

definition rename_many' where "rename_many' i == \<lambda> v. rename_many ren (i,v)" 
abbreviation (input) ren_l where "ren_l == rename_single ren" 

private lemma rdisj: "range (rename_many' i) \<inter> range ren_l = {}" 
  unfolding rename_many'_def
  using renameN by blast

private lemma rdisj2: "i \<noteq> j \<Longrightarrow> range (rename_many' i) \<inter> range (rename_many' j) = {}" 
  unfolding rename_many'_def
  using renameN(1)[of ren] 
  using injD by fastforce

private lemma inj: "inj (rename_many' i)"  "inj ren_l"
  unfolding rename_many'_def
  using renameN(1,2)[of ren] 
  by (meson Pair_inject injD injI)+

lemmas renameN = rdisj rdisj2 inj

lemma rename_many_disj:
  assumes "i \<noteq> j"
  shows "vars_term (map_vars_term (rename_many' i) t) \<inter> vars_term (map_vars_term (rename_many' j) s) = {}"
  by (smt (verit, best) renameN(2) assms disjoint_iff imageE rangeI term.set_map(2)) 

lemma mgu_var_disjoint_list_generic_complete_pre:
  fixes \<sigma> :: "nat \<Rightarrow> ('f, 'v) subst" and \<theta> :: "('f, 'v) subst"
    and pairs :: "(('f, 'v)term \<times> ('f,'v)term) list"
  assumes unif_disj: "\<And> i. i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>"
  shows "\<exists>\<mu> \<tau> \<delta>. mgu_var_disjoint_list_generic rename_many' ren_l pairs = Some (\<mu>, \<tau>) \<and> 
    \<theta> = \<tau> \<circ>\<^sub>s \<delta> \<and>
    (\<forall> i < length pairs. \<sigma> i = \<mu>!i \<circ>\<^sub>s \<delta>  \<and> fst(pairs!i) \<cdot> \<mu>!i = snd(pairs!i) \<cdot> \<tau>)"
proof -
  define \<delta> where "\<delta> x = (if (\<exists> i. i < length pairs \<and> x \<in> range (rename_many' i)) then 
    let i = (SOME i. i < length pairs \<and> x \<in> range (rename_many' i)) in 
    (\<sigma> i) (the_inv (rename_many' i) x) else \<theta> (the_inv ren_l x))" for x
  have ids: "\<And> i. i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> (\<sigma> i) = map_vars_term (rename_many' i) (fst(pairs!i)) \<cdot> \<delta>" 
    unfolding map_vars_term_eq
    unfolding subst_subst o_def subst_compose_def
  proof (rule term_subst_eq, simp)
    fix i x
    assume len: "i < length pairs" 
    let ?y = "rename_many' i x" 
    have cond: "(\<exists> i. i < length pairs \<and> ?y \<in> range (rename_many' i))" using len by auto
    have some: "(SOME i. i < length pairs \<and> ?y \<in> range (rename_many' i)) = i"
    proof (rule some_equality)
      show i1: "i < length pairs \<and> rename_many' i x \<in> range (rename_many' i)" using len by auto
      fix j
      assume i2: "j < length pairs \<and> rename_many' i x \<in> range (rename_many' j)" 
      show "j = i" using i1 i2 
        by (meson i1 i2 disjoint_iff rdisj2)
    qed
    have delta: "\<delta> ?y =  (\<sigma> i) (the_inv (rename_many' i) ?y)" unfolding \<delta>_def Let_def some using cond by auto
    show "(\<sigma> i) x = \<delta> ?y" unfolding delta the_inv_f_f[OF inj(1)] ..
  qed

  have idt: "\<And> i. i < length pairs \<Longrightarrow> snd(pairs!i) \<cdot> \<theta> = map_vars_term (ren_l) (snd(pairs!i)) \<cdot> \<delta>" 
    unfolding map_vars_term_eq
    unfolding subst_subst o_def subst_compose_def
  proof (rule term_subst_eq, simp)
    fix x
    let ?z = "ren_l x" 
    have delta2: "\<delta> ?z =  \<theta> (the_inv (ren_l) ?z)" unfolding \<delta>_def Let_def
      using rdisj by auto
    show "\<theta> x = \<delta> ?z" unfolding delta2 
      by (simp add: renameN the_inv_f_f)
  qed

  from ids idt unif_disj 
  have unif: "\<And> i. i < length pairs \<Longrightarrow> map_vars_term (rename_many' i) (fst(pairs!i)) \<cdot> \<delta> = map_vars_term ren_l (snd(pairs!i)) \<cdot> \<delta>" by auto
  let ?E = "map2 (\<lambda>i (si, li). (map_vars_term (rename_many' i) si, map_vars_term ren_l li)) [0..<length pairs] pairs" 
  from unif have unE:"\<delta> \<in> unifiers (set ?E)" unfolding unifiers_def 
    by (smt (z3) add_0 case_prod_beta in_set_conv_nth length_map map_nth map_snd_zip mem_Collect_eq nth_map nth_upt nth_zip prod.sel(1) prod.sel(2))
  hence "unify ?E [] \<noteq> None" using unify_complete by force
  then obtain \<gamma> where unify: "unify ?E [] = Some \<gamma>"  by (cases "unify ?E []", auto)
  have mgu_var_defn:"mgu_var_disjoint_list_generic rename_many' ren_l pairs = Some (map (\<lambda>i. subst_of \<gamma> \<circ> rename_many' i) [0..<length pairs], subst_of \<gamma> \<circ> ren_l)" 
    (is "_ = Some (?\<mu>, ?\<tau>)") unfolding mgu_var_disjoint_list_generic_def Let_def unify by simp

  moreover have  "\<And> i. i < length pairs \<Longrightarrow>  \<sigma> i = (?\<mu>)!i \<circ>\<^sub>s \<delta>" 
  proof (rule ext)
    fix i y
    assume len2: "i < length pairs"
    let ?w = "rename_many' i y"
    have cond2: "(\<exists> i. i < length pairs \<and> ?w \<in> range (rename_many' i))" using len2 by auto
    have some2: "(SOME i. i < length pairs \<and> ?w \<in> range (rename_many' i)) = i"
    proof (rule some_equality)
      show i1: "i < length pairs \<and> rename_many' i y \<in> range (rename_many' i)" using len2 by auto
      fix j
      assume i2: "j < length pairs \<and> rename_many' i y \<in> range (rename_many' j)" 
      show "j = i" 
        by (meson i1 i2 disjoint_iff renameN)
    qed

    have sub:"\<delta> = subst_of \<gamma>  \<circ>\<^sub>s \<delta> "
      using unE is_imgu_def unify unify_sound by blast
    then have ids1:"(?\<mu>!i \<circ>\<^sub>s \<delta>) y = \<delta> ?w" unfolding \<delta>_def mgu_var_defn  subst_compose_def rdisj2
      using some2 fun_cong[OF sub, of ?w] cond2 len2  length_map map_nth nth_map nth_upt subst_compose_def
      by (smt (verit, best) Eps_cong add_0 comp_eq_dest_lhs)
    then have ids2:"\<delta> ?w = \<sigma> i y" unfolding \<delta>_def mgu_var_defn  using inj(1) some2 cond2 len2 rdisj2
      by (simp add: the_inv_f_f)
    from ids1 ids2  show "\<sigma> i y = (?\<mu> !i \<circ>\<^sub>s \<delta>) y" by simp
  qed

  moreover have "\<theta> = ?\<tau> \<circ>\<^sub>s \<delta>" 
  proof(rule ext)
    fix z
    have "(?\<tau> \<circ>\<^sub>s \<delta>)z = \<delta>(ren_l z)"  unfolding subst_compose_def 
      by (metis (mono_tags, lifting) unE is_imgu_def o_apply subst_compose_def unify unify_sound)
    also have "... = \<theta> z" unfolding the_inv_f_f[OF inj(2)]
      using rdisj \<delta>_def inj(2) the_inv_f_f by fastforce
    finally show "\<theta> z = (?\<tau> \<circ>\<^sub>s \<delta>)z"   by simp
  qed

  moreover 
  {
    fix i
    assume i: "i < length pairs" 
    have "fst(pairs!i) \<cdot> ?\<mu>!i = map_vars_term (rename_many' i) (fst(pairs!i)) \<cdot> (subst_of \<gamma>)" 
      unfolding mgu_var_defn unify apply_subst_map_vars_term using i by simp
    also have "\<dots> = map_vars_term (ren_l) (snd(pairs!i)) \<cdot> (subst_of \<gamma>)" 
      using i unfolding mgu_var_disjoint_list_generic_def unify apply_subst_map_vars_term unif_disj Let_def 
      using mgu_var_disjoint_list_generic_sound[OF mgu_var_defn] by simp 
    also have "\<dots> = snd(pairs!i) \<cdot> ?\<tau>"        
      unfolding mgu_var_disjoint_list_generic_def apply_subst_map_vars_term unify by simp
    finally have "fst(pairs!i) \<cdot> ?\<mu>!i = snd(pairs!i) \<cdot> ?\<tau>" .
  }  

  ultimately show ?thesis by auto
qed

lemma mgu_var_disjoint_list_generic_complete:
  fixes \<sigma> :: "nat \<Rightarrow> ('f, 'v) subst" and \<theta> :: "('f, 'v) subst"
    and pairs :: "(('f, 'v)term \<times> ('f,'v)term) list"
  defines "V \<equiv> \<Union> (vars_term ` snd ` set pairs)" 
  defines "W \<equiv> UNIV - V" 
  assumes unif: "\<And> i. i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>"
  shows "\<exists>\<mu> \<tau> \<delta>. mgu_var_disjoint_list_generic rename_many' ren_l pairs = Some (\<mu>, \<tau>) \<and> 
    \<theta> = \<tau> \<circ>\<^sub>s \<delta> \<and>
    (\<forall> i < length pairs. \<sigma> i = \<mu>!i \<circ>\<^sub>s \<delta>  \<and> fst(pairs!i) \<cdot> \<mu>!i = snd(pairs!i) \<cdot> \<tau>) \<and>
    \<tau> ` W \<subseteq> Var ` (UNIV - \<Union> (vars_term ` \<tau> ` V) - (\<Union> {\<Union> (vars_term ` range (\<mu> ! i)) | i. i < length pairs})) \<and> inj_on \<tau> W"
proof -
  let ?mgu = "mgu_var_disjoint_list_generic rename_many' ren_l" 
  from mgu_var_disjoint_list_generic_complete_pre[OF unif]
  obtain \<mu> \<tau> \<delta> where mgu: "?mgu pairs = Some (\<mu>, \<tau>)"
    and theta: "\<theta> = \<tau> \<circ>\<^sub>s \<delta>" and rest: "(\<forall> i < length pairs. \<sigma> i = \<mu>!i \<circ>\<^sub>s \<delta>  \<and> fst(pairs!i) \<cdot> \<mu>!i = snd(pairs!i) \<cdot> \<tau>)" by auto
  show ?thesis
  proof (intro exI conjI, rule mgu, rule theta, rule rest)
    {
      fix x y
      assume x: "x \<in> W" and y: "y \<in> W" 
      from x have x: "i < length pairs \<Longrightarrow> x \<notin> vars_term (snd (pairs ! i))" for i 
        unfolding W_def set_conv_nth V_def by fastforce
      from y have y: "i < length pairs \<Longrightarrow> y \<notin> vars_term (snd (pairs ! i))" for i 
        unfolding W_def set_conv_nth V_def by fastforce
      define \<theta>' where "\<theta>' = \<theta>(y := Var y, x := Var x)" 
      have "i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>'" for i 
        using unif[of i] x[of i] y[of i] unfolding \<theta>'_def
        by (auto intro: term_subst_eq)
      from mgu_var_disjoint_list_generic_complete_pre[OF this, unfolded mgu]
      obtain \<delta>' where "\<theta>' = \<tau> \<circ>\<^sub>s \<delta>'" by auto
      from arg_cong[OF this, of "\<lambda> f. f x", unfolded \<theta>'_def subst_compose_def]
        arg_cong[OF this, of "\<lambda> f. f y", unfolded \<theta>'_def subst_compose_def]
      have x: "\<tau> x \<cdot> \<delta>' = Var x" and y: "\<tau> y \<cdot> \<delta>' = (if x = y then Var x else Var y)" 
        by (auto split: if_splits)
      from x have ran: "\<tau> x \<in> range Var" by (cases "\<tau> x", auto)
      from x y have inj: "\<tau> x = \<tau> y \<Longrightarrow> x = y" by (cases "\<tau> x"; cases "\<tau> y", auto split: if_splits)
      note ran inj
    } note part_1 = this
    from part_1 show "inj_on \<tau> W" by (auto simp: inj_on_def)
    from part_1 have "\<tau> ` W \<subseteq> range Var" by auto
    let ?Union = "\<Union> {\<Union> (vars_term ` range (\<mu> ! i)) | i. i < length pairs}" 
    {
      fix x
      assume x: "x \<in> W" 
      from part_1[OF this this] obtain y where id: "\<tau> x = Var y" by auto
      {
        assume "y \<in> \<Union> (vars_term ` \<tau> ` V) \<union> ?Union" 
        hence "y \<in> \<Union> (vars_term ` \<tau> ` V) \<or> y \<in> ?Union" by auto
        hence False
        proof
          assume "y \<in> ?Union" 
          then obtain i z where i: "i < length pairs" and y: "y \<in> vars_term ((\<mu> ! i) z)" by auto
          let ?t = "(\<mu> ! i) z" 
          from y obtain p where p: "p \<in> poss ?t" and eq: "?t |_ p = Var y" (is "_ = ?y") by (rule vars_term_poss_subt_at)
          {
            fix u
            define \<theta>' where "\<theta>' = \<theta>(x := u)" 
            from x have x: "i < length pairs \<Longrightarrow> x \<notin> vars_term (snd (pairs ! i))" for i 
              unfolding W_def set_conv_nth V_def by fastforce
            have "i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>'" for i 
              using unif[of i] x[of i] unfolding \<theta>'_def
              by (auto intro: term_subst_eq)
            from mgu_var_disjoint_list_generic_complete_pre[OF this, unfolded mgu] i
            obtain \<delta>' where theta': "\<theta>' = \<tau> \<circ>\<^sub>s \<delta>'" and sigma: "\<sigma> i = \<mu> ! i \<circ>\<^sub>s \<delta>'" by auto
            {
              fix \<delta>''
              assume "\<delta>'' \<in> {\<delta>, \<delta>'}" 
              hence "\<sigma> i z = ?t \<cdot> \<delta>''" using sigma rest[rule_format,OF i, THEN conjunct1] 
                by (metis insert_iff singletonD subst_compose)
              hence "\<sigma> i z |_ p = ?t \<cdot> \<delta>'' |_ p" by simp
              also have "\<dots> = \<delta>'' y" using p eq by auto
              finally have "\<sigma> i z |_ p = \<delta>'' y" by auto
            }
            hence "\<delta> y = \<delta>' y" by (metis insertCI)
            from this id have "\<tau> x \<cdot> \<delta> = \<tau> x \<cdot> \<delta>'" by auto
            hence "\<theta> x = \<theta>' x" using theta theta' by (simp add: subst_compose_def)
            hence "\<theta> x = u" unfolding \<theta>'_def by simp
          }
          from this[of "Fun _ _", unfolded this[of "Var undefined"]]
          show False by simp
        next
          assume "y \<in> \<Union> (vars_term ` \<tau> ` V)" 
          from this[unfolded V_def set_conv_nth] obtain i
            where i: "i < length pairs" and y: "y \<in> \<Union> (vars_term ` \<tau> ` vars_term (snd (pairs ! i)))" 
            by force
          let ?t = "snd (pairs ! i) \<cdot> \<tau>"
          from y have y: "y \<in> vars_term ?t" 
            by (metis vars_term_subst)
          then obtain p where p: "p \<in> poss ?t" and eq: "?t |_ p = Var y" (is "_ = ?y") by (rule vars_term_poss_subt_at)

          {
            fix u
            define \<theta>' where "\<theta>' = \<theta>(x := u)" 
            from x have x: "i < length pairs \<Longrightarrow> x \<notin> vars_term (snd (pairs ! i))" for i 
              unfolding W_def set_conv_nth V_def by fastforce
            have "i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>'" for i 
              using unif[of i] x[of i] unfolding \<theta>'_def
              by (auto intro: term_subst_eq)
            from mgu_var_disjoint_list_generic_complete_pre[OF this, unfolded mgu]
            obtain \<delta> where theta: "\<theta>' = \<tau> \<circ>\<^sub>s \<delta>" by auto
            from eq have "(?t |_ p) \<cdot> \<delta> = ?y \<cdot> \<delta>" by simp
            also have "(?t |_ p) \<cdot> \<delta> = (?t \<cdot> \<delta>) |_ p" using p by auto
            also have "?t \<cdot> \<delta> = snd (pairs ! i) \<cdot> \<theta>'" unfolding theta by simp
            also have "\<dots> = snd (pairs ! i) \<cdot> \<theta>" unfolding \<theta>'_def
              by (rule term_subst_eq, insert x[OF i], auto)
            also have "?y \<cdot> \<delta> = \<delta> y" by simp
            also have "\<dots> = \<theta>' x" unfolding theta using id by (auto simp: subst_compose_def)
            also have "\<dots> = u" unfolding \<theta>'_def by simp
            finally have "snd (pairs ! i) \<cdot> \<theta> |_ p = u" .
          }
          from this[of "Fun _ _", unfolded this[of "Var undefined"]]
          show False by simp
        qed        
      }
      hence "\<tau> x \<in> Var ` (UNIV - \<Union> (vars_term ` \<tau> ` V) - ?Union)" using id by blast
    }
    with part_1 show "\<tau> ` W \<subseteq> Var ` (UNIV - \<Union> (vars_term ` \<tau> ` V) - ?Union)" by auto
  qed
qed
end


definition "mgu_vd_list ren = mgu_var_disjoint_list_generic (rename_many' ren) (rename_single ren)"


lemma mgu_vd_list_sound: 
  assumes "mgu_vd_list ren pairs = Some (\<mu> , \<tau>)"
  shows "i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<mu>!i = snd(pairs!i) \<cdot> \<tau>"
    "length \<mu> = length pairs" 
  using assms mgu_var_disjoint_list_generic_sound
  unfolding mgu_vd_list_def by blast+

lemma mgu_vd_list_complete:
  fixes \<sigma> :: "nat \<Rightarrow> ('f, 'v :: infinite) subst" and \<theta> :: "('f, 'v) subst"
    and pairs :: "(('f, 'v)term \<times> ('f,'v)term) list"
  defines "V \<equiv> \<Union> (vars_term ` snd ` set pairs)" 
  defines "W \<equiv> UNIV - V" 
  assumes unif: "\<And> i. i < length pairs \<Longrightarrow> fst(pairs!i) \<cdot> \<sigma> i = snd(pairs!i) \<cdot> \<theta>"
  shows "\<exists>\<mu> \<tau> \<delta>. mgu_vd_list ren pairs = Some (\<mu>, \<tau>) \<and> 
    \<theta> = \<tau> \<circ>\<^sub>s \<delta> \<and>
    (\<forall> i < length pairs. \<sigma> i = \<mu>!i \<circ>\<^sub>s \<delta>  \<and> fst(pairs!i) \<cdot> \<mu>!i = snd(pairs!i) \<cdot> \<tau>) \<and>
    \<tau> ` W \<subseteq> Var ` (UNIV - \<Union> (vars_term ` \<tau> ` V) - (\<Union> {\<Union> (vars_term ` range (\<mu> ! i)) | i. i < length pairs})) \<and> inj_on \<tau> W"
  unfolding mgu_vd_list_def V_def W_def
  by (rule mgu_var_disjoint_list_generic_complete; (intro unif)?)

end