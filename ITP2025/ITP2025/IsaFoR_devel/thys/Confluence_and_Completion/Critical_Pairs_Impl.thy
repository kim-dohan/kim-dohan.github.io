(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Critical_Pairs_Impl
imports 
  TRS.Critical_Pairs_Innermost
  Check_Joins
  TRS.Q_Restricted_Rewriting_Impl
  Show.Shows_Literal
begin

context fixes
  ren :: "'v :: infinite renaming2" 
begin
definition critical_pairs_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> (bool \<times> ('f,'v)rule)list" 
  where "critical_pairs_impl P R \<equiv> concat (map (\<lambda> (l,r). concat (map (\<lambda> p. let C = ctxt_of_pos_term p l; l'' = l |_ p; b = (C = \<box>) in 
  if is_Var l'' then [] else concat (map (\<lambda> (l',r'). case mgu_vd ren l'' l' of Some (\<sigma>,\<tau>) \<Rightarrow> [(b, (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, r \<cdot> \<sigma>)] | None \<Rightarrow> []) R)) (poss_list l))) P)"

lemma critical_pairs_impl[simp]: "set (critical_pairs_impl P R) = critical_pairs ren (set P) (set R)" (is "?l = ?r")
proof -
  note cpdefs = critical_pairs_impl_def critical_pairs_def set_concat
    set_map Let_def poss_list_sound
  {
    fix b s t
    assume "(b,s,t) \<in> ?r"
    from this[unfolded cpdefs]
    obtain l r l' r' l'' C \<sigma> \<tau> where
      b: "b = (C = \<box>)" and t: "t = r \<cdot> \<sigma>" and s: "s = (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>"
      and P: "(l,r) \<in> set P" and R: "(l', r') \<in> set R"
      and l: "l = C\<langle>l''\<rangle>" and l'': "is_Fun l''"
      and mgu: "mgu_vd ren l'' l' = Some (\<sigma>, \<tau>)"
      by auto
    let ?p = "hole_pos C"
    from l have p: "?p \<in> poss l" by auto
    from l p have C: "C = ctxt_of_pos_term ?p l" by auto
    from l p have l: "l |_ ?p = l''" by auto
    have "(b,s,t) \<in> ?l" unfolding cpdefs b s t
      by (rule, rule, rule P, unfold cpdefs, rule, rule imageI[OF p],
      insert C l R l'' mgu, force)
  } 
  then have "?r \<subseteq> ?l" by auto
  moreover
  {
    fix b s t
    assume "(b,s,t) \<in> ?l"
    from this[unfolded cpdefs]
    obtain l r p l' r' \<sigma> \<tau> where
      P: "(l,r) \<in> set P" and p: "p \<in> poss l" and lp: "is_Fun (l |_ p)" 
      and R: "(l',r') \<in> set R" and mgu: "Some (\<sigma>,\<tau>) = mgu_vd ren (l |_ p) l'" and b: "b = (ctxt_of_pos_term p l = \<box>)" and t: "t = r \<cdot> \<sigma>" and s: "s = (ctxt_of_pos_term p l \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>"  by force
    have "(b,s,t) \<in> ?r"
      by (rule critical_pairsI[OF P R _ lp mgu[symmetric] t s b], insert ctxt_supt_id[OF p], simp)
  }
  then have "?l \<subseteq> ?r" by auto
  ultimately show ?thesis by auto
qed

definition critical_pairs_top_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> (('f,'v)rule)list" 
  where "critical_pairs_top_impl P R \<equiv> concat (map (\<lambda> (l,r).  
  if is_Var l then [] else concat (map (\<lambda> (l',r'). case mgu_vd ren l l' of Some (\<sigma>,\<tau>) \<Rightarrow> [(r' \<cdot> \<tau>, r \<cdot> \<sigma>)] | None \<Rightarrow> []) R)) P)"

lemma critical_pairs_top_impl[simp]: "set (critical_pairs_top_impl P R) = {(s,t). (True,s,t) \<in> critical_pairs ren (set P) (set R)}" (is "?l = ?r")
proof -
  note cpdefs = critical_pairs_top_impl_def critical_pairs_def set_concat
    set_map
  {
    fix s t
    assume "(s,t) \<in> ?r"
    from this[unfolded cpdefs]
    obtain l r l' r' l'' C \<sigma> \<tau> where
      C: "C = \<box>" and t: "t = r \<cdot> \<sigma>" and s: "s = (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>"
      and P: "(l,r) \<in> set P" and R: "(l', r') \<in> set R"
      and l: "l = C\<langle>l''\<rangle>" and l'': "is_Fun l''"
      and mgu: "mgu_vd ren l'' l' = Some (\<sigma>, \<tau>)"
      by auto
    have "(s,t) \<in> ?l" unfolding cpdefs s t 
      by (rule, rule, rule P, insert l[unfolded C] l'' mgu[symmetric] R C, force)
  }
  then have "?r \<subseteq> ?l" by auto
  moreover
  {
    fix s t
    assume st: "(s,t) \<in> ?l"
    have id: "\<And> p b t e. p \<in> set (if b then t else e) = (b \<and> p \<in> set t \<or> \<not> b \<and> p \<in> set e)" by auto
    from st[unfolded cpdefs]
    obtain l r l' r' \<sigma> \<tau> where
      P: "(l,r) \<in> set P" and lp: "is_Fun l" 
      and R: "(l',r') \<in> set R" and mgu: "Some (\<sigma>,\<tau>) = mgu_vd ren l l'" and t: "t = r \<cdot> \<sigma>" and s: "s = r' \<cdot> \<tau>" by (auto simp: id)
    have "(s,t) \<in> ?r" unfolding s t
      by (rule, unfold split, rule critical_pairsI[OF P R _ lp mgu[symmetric] refl, of \<box>], auto)
  }
  then have "?l \<subseteq> ?r" by auto
  ultimately show ?thesis by auto
qed
end

definition showsl_crit_pair :: "('f :: showl,'w :: showl)rule \<Rightarrow> showsl"
  where "showsl_crit_pair lr \<equiv> 
  showsl_lit (STR ''('') \<circ> showsl (fst lr) \<circ> showsl_lit (STR '', '') \<circ> 
  showsl (snd lr) \<circ> showsl_lit (STR '')'')"

definition check_critical_pairs_cp_info :: "('f :: showl,'v :: showl)rules \<Rightarrow> (bool \<times> ('f,'v)rule) list \<Rightarrow> ('f, 'v) cp_join_hints \<Rightarrow> showsl check"
  where "check_critical_pairs_cp_info R cp hints \<equiv> do {
     checker \<leftarrow> is_rsteps_join_one R hints;
     check_allm (\<lambda> (b,st). checker st) cp
  }"

definition check_critical_pairs_NF :: "('f :: showl,'v :: showl)rules \<Rightarrow> (bool \<times> ('f,'v)rule) list \<Rightarrow> showsl check"
  where "check_critical_pairs_NF R cp \<equiv> do {
    check_allm (\<lambda> (_,s,t). 
       if (s = t) then succeed else
       check_join_NF R s t
           <+? (\<lambda> e. showsl_lit (STR ''problem when joining critical pair '') \<circ> showsl_crit_pair (s,t) \<circ> showsl_nl \<circ> e)
    ) cp
  }"

datatype ('f,'v) join_info = Guided_BFS "('f,'v)cp_join_hints" | Join_NF

definition check_critical_pairs :: "('f :: showl,'v :: showl)rules \<Rightarrow> (bool \<times> ('f,'v)rule) list \<Rightarrow> ('f,'v) join_info \<Rightarrow> showsl check"
  where "check_critical_pairs R cp join_info \<equiv> case join_info of 
            Guided_BFS joins \<Rightarrow> check_critical_pairs_cp_info R cp joins 
          | Join_NF      \<Rightarrow> check_critical_pairs_NF R cp"

context fixes
  ren :: "'v :: {infinite,showl} renaming2" 
begin

definition check_critical_pairs_innermost :: "('f :: showl,'v)rules \<Rightarrow> showsl check"
  where "check_critical_pairs_innermost R \<equiv> 
    check_allm (\<lambda> (l,r). check (l = r) (showsl_lit (STR ''there is a non-trivial critical pair '') 
      \<circ> showsl_crit_pair (l,r))) (critical_pairs_top_impl ren R R)"

lemma check_critical_pairs_innermost: assumes ok: "isOK(check_critical_pairs_innermost R)" and NF: "NF_terms Q \<subseteq> NF_trs (set R)" 
  and var: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> is_Fun l"
  shows "CR (qrstep nfs Q (set R))"
proof (rule critical_pairs_innermost[OF _ NF var])
  fix l r
  assume "(True,l,r) \<in> critical_pairs ren (set R) (set R)"
  with ok[unfolded check_critical_pairs_innermost_def]
  show "l = r" by simp
qed

lemma check_critical_pairs_NF: fixes R :: "('f :: showl, 'v)rules"
  assumes ok: "isOK(check_critical_pairs_NF R (critical_pairs_impl ren R R))"
  shows "WCR (rstep (set R))"
proof (rule critical_pairs)
  fix t1 t2 b
  assume cp: "(b,t1,t2) \<in> critical_pairs ren (set R) (set R)" and neq: "t1 \<noteq> t2"
  note ok = ok[unfolded check_critical_pairs_NF_def, unfolded Let_def, simplified]
  let ?Rel = "(rstep (set R))^*"
  from cp neq ok have "isOK(check_join_NF R t1 t2)"
    by auto
  from check_join_NF_sound[OF this] have "(t1,t2) \<in> ?Rel O ?Rel^-1" by auto
  then obtain s where t1: "(t1,s) \<in> ?Rel" and t2: "(t2,s) \<in> ?Rel" by auto
  show "\<exists> l' r' u. instance_rule (t1,t2) (l',r') \<and> (l',u) \<in> ?Rel \<and> (r', u) \<in> ?Rel"
  proof (intro exI conjI)
    show "instance_rule (t1,t2) (t1,t2)" by simp
  qed (insert t1 t2, auto)
qed    


lemma check_critical_pairs_NF_SN: fixes R :: "('f :: showl, 'v)rules"
  assumes SN: "SN (rstep (set R))"
  shows "isOK(check_critical_pairs_NF R (critical_pairs_impl ren R R)) = CR (rstep (set R))" (is "?check = ?CR")
proof (cases ?check)
  case True
  from check_critical_pairs_NF[OF True] have "WCR (rstep (set R))" .
  from Newman[OF SN this] True show ?thesis by simp
next
  case False
  let ?R = "rstep (set R)"
  from False[unfolded check_critical_pairs_NF_def]
  obtain b s t where bst: "(b,s,t) \<in> critical_pairs ren (set R) (set R)" and ok: "\<not> isOK (check_join_NF R s t)"
    by force
  from critical_pairs_fork[OF bst] obtain u where us: "(u,s) \<in> ?R" and ut: "(u,t) \<in> ?R" by blast+
  note get_NF = compute_rstep_NF_SN[OF SN]
  from get_NF[of s] obtain s' where s: "compute_rstep_NF R s = Some s'" ..
  from get_NF[of t] obtain t' where t: "compute_rstep_NF R t = Some t'" ..
  from ok[unfolded check_join_NF_def s t split option.simps] have neq: "s' \<noteq> t'" by simp
  from us compute_rstep_NF_sound[OF s] have "(u,s') \<in> ?R^*" by auto
  with compute_rstep_NF_complete[OF s] have us: "(u,s') \<in> ?R^!" by auto
  from ut compute_rstep_NF_sound[OF t] have "(u,t') \<in> ?R^*" by auto
  with compute_rstep_NF_complete[OF t] have ut: "(u,t') \<in> ?R^!" by auto
  {
    assume ?CR
    from CR_imp_UNF[OF this] have "UNF ?R" .
    from UNF_onD[OF this _ us ut] neq have False by simp
  }
  with False show ?thesis by auto
qed

lemma check_critical_pairs_cp_info: 
  fixes R :: "('f :: showl, 'v)rules"
  and n :: nat
  assumes ok: "isOK(check_critical_pairs_cp_info R (critical_pairs_impl ren R R) infos)"
  shows "WCR (rstep (set R))"
proof (rule critical_pairs)
  fix t1 t2 b
  assume cp: "(b,t1,t2) \<in> critical_pairs ren (set R) (set R)" and neq: "t1 \<noteq> t2"
  note ok = ok[unfolded check_critical_pairs_cp_info_def, simplified]
  from ok obtain checker where checker: "is_rsteps_join_one R infos = return checker" by auto
  note ok = ok[unfolded checker, simplified, rule_format, OF cp]
  let ?Rel = "(rstep (set R))^*"
  from ok have "isOK(checker (t1,t2))" by auto
  from is_rsteps_join_one[OF checker this] have "(t1,t2) \<in> ?Rel O ?Rel^-1" by auto
  then obtain s where t1: "(t1,s) \<in> ?Rel" and t2: "(t2,s) \<in> ?Rel" by auto
  show "\<exists> l' r' u. instance_rule (t1,t2) (l',r') \<and> (l',u) \<in> ?Rel \<and> (r',u) \<in> ?Rel"
  proof (intro exI conjI)
    show "instance_rule (t1,t2) (t1,t2)" by simp
  qed (insert t1 t2, auto)
qed


lemma check_critical_pairs: 
  fixes R :: "('f :: showl, 'v)rules"
  and n :: nat
  assumes ok: "isOK(check_critical_pairs R (critical_pairs_impl ren R R) joins_i)"
  shows "WCR (rstep (set R))"
proof -
  note ok = ok[unfolded check_critical_pairs_def]
  show ?thesis
  proof (cases joins_i)
    case (Guided_BFS joins)
    show ?thesis
      by (rule check_critical_pairs_cp_info, insert Guided_BFS ok, auto)
  next
    case Join_NF
    show ?thesis
      by (rule check_critical_pairs_NF, insert Join_NF ok, auto)
  qed
qed
    
end
end
