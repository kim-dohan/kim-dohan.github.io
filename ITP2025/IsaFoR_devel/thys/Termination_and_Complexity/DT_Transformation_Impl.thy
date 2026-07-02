(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory DT_Transformation_Impl
imports
  DT_Transformation
  Framework.Termination_Problem_Spec
  Auxx.Map_Choice
  Framework.QDP_Framework_Impl
  "HOL-Combinatorics.List_Permutation"
  TRS.Q_Restricted_Rewriting_Impl
begin    

datatype ('f, 'v) dt_transformation_info = DT_Transformation_Info 
  "(('f, 'v) rule \<times> ('f, 'v) rule) list" \<comment> \<open>map strict rules to DTs\<close>
  "(('f, 'v) rule \<times> ('f, 'v) rule) list" \<comment> \<open>map weak rules to DTs\<close>
  "(('f, 'v) term list)" \<comment> \<open>new Q-components\<close>

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

fun DPos_impl :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) term \<Rightarrow> (pos \<times> ('f, 'v) term) list"
where
  "DPos_impl D (Var x) = []" |
  "DPos_impl D (Fun f ts) =
    (let n = length ts in
    (if (f, n) \<in> D then Cons ([], Fun (\<sharp> f) ts) else id) 
      (concat (map (\<lambda> (i, ti). map (\<lambda> (p, t).
        (Cons i p, t)) (DPos_impl D ti)) (zip [0 ..< n] ts))))"

end

lemma (in pre_innermost_wf) DPos_Fun:
  "DPos (Fun f ss) = 
    (if (f,length ss) \<in> D then insert [] else id)
      {Cons i p | i p. i < length ss \<and> p \<in> DPos (ss ! i)}" (is "?l = ?r")
proof -
  note d = DPos_def
  let ?n = "length ss"
  {
    fix p
    assume p: "p \<in> ?l"
    from this[unfolded d] obtain g where p: "p \<in> poss (Fun f ss)" and g: "g \<in> D"
    and root: "root (Fun f ss |_ p) = Some g" by auto
    then have "p \<in> ?r"
    proof (cases p)
      case Nil
      from root[unfolded Nil] have "g = (f,?n)" by auto
      with g show "p \<in> ?r" unfolding Nil by auto
    next
      case (Cons i q)
      with p have i: "i < ?n" and q: "q \<in> poss (ss ! i)" by auto
      with root g Cons have "q \<in> DPos (ss ! i)" unfolding d by auto
      with i show "p \<in> ?r" unfolding Cons by auto
    qed
  }
  moreover
  {
    fix p
    assume p: "p \<in> ?r"
    have "p \<in> ?l"
    proof (cases p)
      case Nil
      with p have "(f,?n) \<in> D" by (auto split: if_splits)
      then show "p \<in> ?l" unfolding d Nil by auto
    next
      case (Cons i q)
      with p have i: "i < ?n" and q: "q \<in> DPos (ss ! i)" by (auto split: if_splits)
      from q[unfolded d] obtain g where q: "q \<in> poss (ss ! i)"
        and g: "g\<in>D" and root: "root (ss ! i |_ q) = Some g" by auto      
      show "p \<in> ?l" unfolding d using root q i g Cons by auto
    qed
  }
  ultimately show ?thesis by blast
qed

lemma (in pre_innermost_wf) DPos_impl:
  "set (DPos_impl shp D s) = { (p, sharp_term shp (s |_ p)) | p. p \<in> DPos s}"
proof (induct s)
  case (Var x)
  then show ?case by (auto simp: DPos_def)
next
  interpret sharp_syntax .
  case (Fun f ss)
  let ?n = "length ss"
  {
    fix i
    assume "i < ?n"
    then have "ss ! i \<in> set ss" by auto
    note Fun[OF this]
  } note IH = this  
  let ?l = "concat (map (\<lambda>(i, ti). map (\<lambda>(p, y). (i # p, y)) (DPos_impl \<sharp> D ti))
              (zip [0..<?n] ss))"
  let ?r = "{i # p |i p. i < ?n \<and> p \<in> DPos (ss ! i)}"
  let ?f = "(if (f,?n) \<in> D then insert ([], Fun (\<sharp> f) ss) else id)"
  have "set ((if (f,?n) \<in> D then (#) ([], Fun (\<sharp> f) ss) else id)
          ?l) = ?f (set ?l)" by auto
  also have "\<dots> = ?f {(p, \<sharp> (Fun f ss |_ p)) | p. p \<in> ?r}"
  proof (rule arg_cong[where f = ?f])
    show "set ?l = {(p, \<sharp> (Fun f ss |_ p)) | p. p \<in> ?r}"
      by (force simp: set_zip IH)
  qed
  also have "\<dots> = {(p, \<sharp> (Fun f ss |_ p)) |p. p \<in> (if (f,?n) \<in> D then insert [] else id) ?r}"
  by auto
  finally show ?case unfolding DPos_Fun DPos_impl.simps Let_def by auto
qed 

fun check_tup :: "'f set \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "check_tup T (Var x) \<longleftrightarrow> False" |
  "check_tup T (Fun f ts) \<longleftrightarrow> f \<in> T"

context
  fixes shp :: "'f \<Rightarrow> 'f:: showl"
begin

interpretation sharp_syntax .

definition
  check_rule_dt ::
    "'f sig \<Rightarrow> 'f set \<Rightarrow> ('f :: showl, 'v :: showl) rule \<times> ('f, 'v) rule \<Rightarrow> showsl check"
where
  "check_rule_dt D Ds  = (\<lambda>((l, r), (dl, dr)). do {
    let sl = \<sharp> l;
    check (sl = dl) (showsl_lit (STR ''wrong lhs, expected '') \<circ> showsl sl \<circ> showsl_lit (STR '' but got '') \<circ> showsl dl);
    let pts = DPos_impl \<sharp> D r;
    let spts = map snd pts;
    let (C, dts) = split_term (check_tup Ds) dr;
    check (mset dts = mset spts)
      (showsl_lit (STR ''multiset of subterms with defined roots differs''))
  } <+? (\<lambda> e. showsl_lit (STR ''could not ensure that '') \<circ> showsl_rule (dl, dr) \<circ> 
    showsl_lit (STR '' is a valid dependency tuple for '') \<circ> showsl_rule (l, r) \<circ> showsl_nl \<circ> e))"

lemma check_rule_dt:
  assumes ok: "isOK (check_rule_dt D Ds (lr, dt))"
  shows "pre_DT_trans.is_DT_of (\<sharp> :: 'f \<Rightarrow> 'f) D lr dt"
proof -
  interpret pre_DT_trans \<sharp> D undefined undefined undefined undefined .
  obtain l r where lr: "lr = (l, r)" by force
  obtain dl dr where dt: "dt = (dl, dr)" by force
  obtain C dts where sg: "split_term (check_tup Ds) dr = (C, dts)" by force
  from split_term_eqf [of dr "check_tup Ds"] and sg
    have dr: "dr =\<^sub>f (C, dts)" by (simp)
  note ok = ok [unfolded lr dt check_rule_dt_def sg split, simplified]
  let ?ps = "map fst (DPos_impl \<sharp> D r)"
  let ?dts = "map snd (DPos_impl \<sharp> D r)"
  from ok have id: "mset dts = mset ?dts" by auto  
  from mset_eq_length [OF id] have len: "length dts = length (DPos_impl \<sharp> D r)" by simp
  from id  have "dts <~~> ?dts" .
  from permutation_Ex_bij [OF this] len obtain f where
    bij: "bij_betw f {..<length dts} {..<length dts}" and
    f: "\<And> i. i<length dts \<Longrightarrow> dts ! i = map snd (DPos_impl \<sharp> D r) ! f i" by auto
  from bij_betw_imp_surj_on[OF bij] have bij: "f ` {..< length dts} = {..< length dts}" .
  let ?pps = "map (\<lambda> i. fst (DPos_impl \<sharp> D r ! f i)) [0 ..< length dts]"
  from ok have l: "dl = \<sharp> l" by simp
  let ?pps' = "(\<lambda>i. fst (DPos_impl \<sharp> D r ! f i)) ` {0 ..< length dts}"
  let ?ps' = "fst ` {DPos_impl \<sharp> D r ! i |i. i < length dts}"
  {
    fix p
    assume "p \<in> ?pps'"
    then obtain i where p: "p = fst (DPos_impl \<sharp> D r ! f i)" and i: "i < length dts" by auto
    from i bij have "f i < length dts" by auto
    then have "p \<in> ?ps'" unfolding p by auto
  }
  moreover
  {
    fix p
    assume "p \<in> ?ps'" 
    then obtain i where p: "p = fst (DPos_impl \<sharp> D r ! i)" and i: "i < length dts" by auto
    from i bij have "i \<in> f ` {..<length dts}" by auto 
    then obtain j where i: "i = f j" and j: "j < length dts" by auto
    have "p \<in> ?pps'" unfolding p i using j by auto
  }
  ultimately have pps: "?pps' = ?ps'" by blast
  show ?thesis unfolding lr dt is_DT_of_def fst_conv snd_conv
  proof (rule conjI[OF l], rule exI[of _ C], rule exI[of _ ?pps], rule conjI)
    have "set ?pps = set ?ps" 
      unfolding set_map set_upt
      unfolding set_conv_nth pps
      by (simp add: len)
    also have "\<dots> = DPos r"
      by (auto simp: DPos_impl)
    finally show "set ?pps = DPos r" .
  next
    have "dr =\<^sub>f (C, dts)" by fact
    also have "dts = map (\<lambda>q. \<sharp> (r |_ q)) ?pps"
    proof (rule nth_equalityI, simp)
      fix i
      assume i: "i < length dts"      
      with bij have fi: "f i < length dts" by auto
      let ?goal = "dts ! i = map (\<lambda>q. \<sharp> (r |_ q)) ?pps ! i"
      have "?goal = 
        (map snd (DPos_impl \<sharp> D r) ! f i = \<sharp> (r |_ fst (DPos_impl \<sharp> D r ! f i)))"
        unfolding f[OF i] using i by simp
      also have "\<dots>" using fi by (insert DPos_impl[of \<sharp> r, unfolded set_conv_nth] len, auto)
      finally show ?goal by simp
    qed
    finally show "dr =\<^sub>f (C, map (\<lambda>q. \<sharp> (r |_ q)) ?pps)" .
  qed
qed

definition dt_transformation ::
  "('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow> ('f, 'v) dt_transformation_info \<Rightarrow>
    ('f, 'v) complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp \<Rightarrow>
    (('f, 'v) complexity_measure \<times> 'tp) result"
where
  "dt_transformation I info cm cc cp =
  (case info of DT_Transformation_Info S_DT_s W_DT_w Q' \<Rightarrow>
    (case cm of Runtime_Complexity C' D' \<Rightarrow> (do {
    let S' = tp_ops.R I cp;
    let W' = tp_ops.Rw I cp;
    let S = map fst S_DT_s;
    let W = map fst W_DT_w;
    let R = S @ W;
    let DD = defined_list R;
    let DD' = set D';
    check_allm (\<lambda> lr. check (\<exists> lr' \<in> set S. lr =\<^sub>v lr') (showsl_lit (STR ''could not find DT for strict rule '') \<circ> showsl lr)) S';
    check_allm (\<lambda> lr. check (\<exists> lr' \<in> set W. lr =\<^sub>v lr') (showsl_lit (STR ''could not find DT for weak rule '') \<circ> showsl lr)) W';
    check_allm (\<lambda> f. check (f \<in> DD') (showsl_lit (STR ''defined symbol '') \<circ> showsl f \<circ> 
      showsl_lit (STR '' does not occur in defined symbols from RC''))) DD;    
    let DTs = map snd S_DT_s;
    let DTw = map snd W_DT_w;
    let D = set DD;
    let shpf = (\<lambda> (f, n :: nat). (\<sharp> f, n));
    let Ds = shpf ` D;
    let DDD = (\<sharp> o fst) ` D;
    let F = funas_trs_list R @ C' @ D';
    let Fs = set F;
    check_allm (\<lambda> q. check (is_Fun q \<and> the (root q) \<notin> Fs) (showsl_lit (STR ''new Q-term '') \<circ> showsl q \<circ> showsl_lit (STR '' not allowed''))) Q';
    check_wf_trs R;
    check_NF_terms_subset (tp_ops.is_QNF I cp) (map fst R) <+? (\<lambda> s. showsl_lit (STR ''innermost required''));
    check_allm (\<lambda> f. check (f \<notin> Ds) (showsl f \<circ> showsl_lit (STR '' as sharped symbol is not fresh''))) F;
    check (set C' \<inter> D = {}) (showsl_lit (STR ''constructors of RC and defined symbols of TRSs are not disjoint''));
    check_allm (check_rule_dt D DDD) S_DT_s;
    check_allm (check_rule_dt D DDD) W_DT_w;
    return (Runtime_Complexity C' (map shpf D'), tp_ops.mk I False (tp_ops.Q I cp @ Q') DTs (R @ DTw))
  })
  | Derivational_Complexity _ \<Rightarrow>  
    error (showsl_lit (STR ''only runtime complexity supported for dependency tuples''))))
    <+? (\<lambda> e. showsl_lit (STR ''error when switching to dependency tuples\<newline>'') \<circ> e)"

lemma dt_transformation:
  assumes "tp_spec I"
    and res: "dt_transformation I info cm cc tp = return (cm', tp')"
    and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm' cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  obtain S_DT_s W_DT_w Q' where info: "info = DT_Transformation_Info S_DT_s W_DT_w Q'" 
    by (cases info, auto)
  note res = res[unfolded dt_transformation_def info]
  interpret tp_spec I by fact
  from res obtain C' D' where cm: "cm = Runtime_Complexity C' D'"
    by (cases cm, simp, blast)
  let ?S' = "set (R tp)"
  let ?W' = "set (Rw tp)"
  let ?S = "fst ` set S_DT_s"
  let ?W = "fst ` set W_DT_w"
  let ?R = "?S \<union> ?W"
  let ?nfs = "NFS tp"
  let ?D = "Collect (defined ?R)"
  let ?DDD = "(\<sharp> \<circ> fst) ` ?D"
  let ?shp = "\<lambda> (f, n :: nat). (shp f, n)"
  let ?Ds = "?shp ` ?D"
  let ?D'' = "map ?shp D'"
  let ?Q = "set (Q tp)"
  let ?Q' = "?Q \<union> set Q'"
  let ?DT_S = "snd ` set S_DT_s"
  let ?DT_W = "snd ` set W_DT_w"
  let ?F = "funas_trs ?R \<union> set C' \<union> set D'"
  let ?NF = "NF_terms ((fst \<circ> fst) ` set S_DT_s \<union> (fst \<circ> fst) ` set W_DT_w)"
  note res = res[unfolded cm Let_def, simplified]
  from res have wf: "wf_trs ?R" and 
    D: "set C' \<inter> ?D = {}" and 
    inn: "NF_terms ?Q \<subseteq> ?NF" and
    Ds: "?Ds \<inter> ?F = {}" and 
    D': "?D \<subseteq> set D'" and
    tp': "tp' = mk False (Q tp @ Q') (map snd S_DT_s) (map fst S_DT_s @ map fst W_DT_w @ map snd W_DT_w)" and
    cm': "cm' = Runtime_Complexity C' ?D''" and
    DT_S: "(\<forall>x\<in> ?S'. \<exists> lr \<in> ?S. x =\<^sub>v lr)" and 
    DT_W: "(\<forall>x\<in> ?W'. \<exists> lr \<in> ?W. x =\<^sub>v lr)" and 
    check_S: "(\<forall>x\<in>set S_DT_s. isOK (check_rule_dt ?D ?DDD x))" and
    check_W: "(\<forall>x\<in>set W_DT_w. isOK (check_rule_dt ?D ?DDD x))"
    by auto
  have "?NF = NF_trs ?R" unfolding NF_terms_lhss[of ?R, symmetric]
    by (rule arg_cong[of _ _ NF_terms], force)
  with inn have inn: "NF_terms ?Q \<subseteq> NF_trs ?R" by simp
  have DF: "?D \<subseteq> ?F" using defined_funas_trs by blast
  interpret innermost_wf ?D ?R ?Q
    by (unfold_locales, insert wf inn, auto)
  interpret DT_trans ?D ?R ?Q ?F shp ?Ds ?Q'
    by (unfold_locales, force, force, rule DF, rule Ds, insert res, force)
  have subset: "?S \<subseteq> ?R" "?W \<subseteq> ?R" by auto
  from cpx[unfolded cm' tp' mk_sound]
  have cpx: "deriv_bound_measure_class
     ((qrstep False ?Q' (?R \<union> ?DT_W))\<^sup>* O
      qrstep False ?Q' ?DT_S O
      (qrstep False ?Q' (?R \<union> ?DT_W))\<^sup>*)
     (Runtime_Complexity C' ?D'') cc" by (simp add: ac_simps)
  show ?thesis unfolding qreltrs_sound split cm
  proof (rule deriv_bound_measure_class_mono[OF relto_mono subset_refl subset_refl dependency_tuples_sound[of ?S ?DT_S ?W ?DT_W _ C' ?D'' cc D', OF _ _ subset refl cpx D' D]])
    show "qrstep ?nfs ?Q ?S' \<subseteq> qrstep ?nfs ?Q ?S"
      by (rule qrstep_rename_vars, insert DT_S, force)
    show "qrstep ?nfs ?Q ?W' \<subseteq> qrstep ?nfs ?Q ?W" 
      by (rule qrstep_rename_vars, insert DT_W, force)
  next
    fix lr
    assume "lr \<in> ?S"
    with DT_S obtain dt where lr_dt: "(lr,dt) \<in> set S_DT_s" by auto
    then have dt: "dt \<in> ?DT_S" by auto
    with check_rule_dt[OF check_S[rule_format, OF lr_dt]]
    show "\<exists> dt \<in> ?DT_S. is_DT_of lr dt" by blast
  next
    fix lr
    assume "lr \<in> ?W"
    with DT_W obtain dt where lr_dt: "(lr,dt) \<in> set W_DT_w" by auto
    then have dt: "dt \<in> ?DT_W" by auto
    with check_rule_dt[OF check_W[rule_format, OF lr_dt]]
    show "\<exists> dt \<in> ?DT_W. is_DT_of lr dt" by blast
  qed auto
qed

end

end
