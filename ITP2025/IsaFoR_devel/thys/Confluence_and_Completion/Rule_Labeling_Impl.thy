(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  Harald Zankl (2014, 2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Rule_Labeling_Impl
imports
  Decreasing_Diagrams2
  Critical_Pairs_Impl
  Equational_Reasoning_Impl
  Auxx.Map_Choice
begin


abbreviation DD2_last where "DD2_last \<equiv> Decreasing_Diagrams2.last"

context
  fixes ren :: "'v :: infinite renaming2" 
begin

definition critical_peaks_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> (bool \<times> ('f,'v) lpeak) list" 
  where "critical_peaks_impl P R \<equiv> concat (map (\<lambda> (l,r). 
    concat (map (\<lambda> p. let C = ctxt_of_pos_term p l; l'' = l |_ p; b = (C = \<box>) in 
      if is_Var l'' then [] else 
      concat (map (\<lambda> (l',r'). case mgu_vd ren l'' l' of 
        Some (\<sigma>,\<tau>) \<Rightarrow> [(b, (l \<cdot> \<sigma>, (l, r), [], \<sigma>, True, r \<cdot> \<sigma>), (l \<cdot> \<sigma>, (l', r'), p, \<tau>, True, (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>))] 
      | None \<Rightarrow> []) R)) (poss_list l))) P)"

lemma critical_peaks_impl: 
  "set (critical_peaks_impl R R) = critical_peaks ren (set R)" (is "?l = ?r")
proof -
  note cpdefs = critical_peaks_impl_def critical_peaks_def set_concat
    set_map Let_def poss_list_sound
  {
    fix b s1 s2
    assume "(b,s1,s2) \<in> ?r"
    from this[unfolded cpdefs]
    obtain l r l' r' l'' C \<sigma> \<tau> where
      b: "b = (C = \<box>)" and s1: "s1 = (l \<cdot> \<sigma>, (l, r), [], \<sigma>, True, r \<cdot> \<sigma>)" 
      and s2: "s2 = ( l \<cdot> \<sigma>, (l', r'), hole_pos C, \<tau>, True, (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>)"
      and lr: "(l, r) \<in> set R" and lr': "(l', r') \<in> set R"
      and l: "l = C\<langle>l''\<rangle>" and l'': "is_Fun l''"
      and mgu: "mgu_vd ren l'' l' = Some (\<sigma>, \<tau>)"
      by auto
    let ?p = "hole_pos C"
    from l have p: "?p \<in> poss l" by auto
    from l p have C: "C = ctxt_of_pos_term ?p l" by auto
    from l p have l: "l |_ ?p = l''" by auto
    have "(b,s1,s2) \<in> ?l" unfolding cpdefs b s1 s2
      by (rule, rule, rule lr, unfold cpdefs, rule, rule imageI[OF p],
      insert C l lr' l'' mgu, force)
  } 
  then have "?r \<subseteq> ?l" by auto
  moreover
  {
    fix b s1 s2
    assume "(b,s1,s2) \<in> ?l"
    from this[unfolded cpdefs]
    obtain l r p l' r' \<sigma> \<tau> where
      lr: "(l,r) \<in> set R" and p: "p \<in> poss l" and lp: "is_Fun (l |_ p)" 
      and lr': "(l',r') \<in> set R" 
      and mgu: "Some (\<sigma>,\<tau>) = mgu_vd ren (l |_ p) l'" 
      and b: "b = (ctxt_of_pos_term p l = \<box>)" 
      and s1: "s1 = (l \<cdot> \<sigma>, (l, r), [], \<sigma>, True, r \<cdot> \<sigma>)" 
      and s2: "s2 = (l \<cdot> \<sigma>, (l', r'), p, \<tau>, True, (ctxt_of_pos_term p l \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>)"  
    by force  
    from p have pp: "hole_pos (ctxt_of_pos_term p l) = p" by simp
    from s1 have s: "get_target s1 = r \<cdot> \<sigma>" unfolding get_target_def by simp    
    from s2 have t: "get_target s2 = (ctxt_of_pos_term p l \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>" 
      unfolding get_target_def by simp    
    from critical_peaksI[OF lr lr' _ lp mgu[symmetric] s t b] 
    have "(b,s1,s2) \<in> ?r" using  ctxt_supt_id[OF p, symmetric] s1 s2 pp
    unfolding get_target_def by auto
  }
  then have "?l \<subseteq> ?r" by auto
  ultimately show ?thesis by auto
qed
end

type_synonym ('f, 'v) rule_lab_repr = "(('f, 'v) rule \<times> nat) list"

definition rule_lab_repr_to_lab :: "('f :: compare_order, 'v :: compare_order ) rule_lab_repr \<Rightarrow> ('f, 'v) rule \<Rightarrow> nat"
where
  "rule_lab_repr_to_lab ps = fun_of_map (ceta_map_of ps) 0"

lemma steps_to_seq: assumes "(s,t) \<in> (rstep R)^*" 
  shows "\<exists> ts. (s, ts) \<in> seq R \<and> DD2_last (s, ts) = t \<and> rule_labeling l ` set ts \<subseteq> l ` R"
  using assms
proof (induct rule: converse_rtrancl_induct)
  case base
  then show ?case by (intro exI[of _ Nil], auto intro: seq.intros)
next
  case (step v u)
  from step(3) obtain ts where seq: "(u,ts) \<in> seq R" and last: "DD2_last (u,ts) = t"
    and lab: "rule_labeling l ` set ts \<subseteq> l ` R" by auto
  from step(1) obtain p sig lr where vu: "(v,u) \<in> rstep_r_p_s R lr p sig"
    using rstep_iff_rstep_r_p_s by blast  
  hence lr: "l lr \<in> l ` R" unfolding rstep_r_p_s_def Let_def by auto
  let ?ts = "(v, lr, p, sig, True, u) # ts" 
  from seq.intros(2)[OF vu seq] have "(v, ?ts) \<in> seq R" .
  then show ?case by (intro exI[of _ ?ts], insert last lab lr, auto simp: get_target_def)
qed

lemma opt_step_to_seq: assumes "(s,t) \<in> (rstep R)^=" 
  shows "\<exists> ts. (s, ts) \<in> seq R \<and> DD2_last (s, ts) = t \<and> rule_labeling l ` set ts \<subseteq> l ` R \<and> length ts \<le> 1"
  using assms
proof 
  assume "(s,t) \<in> Id" 
  thus ?thesis by (intro exI[of _ Nil], auto intro: seq.intros)
next
  assume "(s,t) \<in> rstep R" 
  then obtain p sig lr where st: "(s,t) \<in> rstep_r_p_s R lr p sig"
    using rstep_iff_rstep_r_p_s by blast  
  hence lr: "l lr \<in> l ` R" unfolding rstep_r_p_s_def Let_def by auto
  let ?ts = "[(s, lr, p, sig, True, t)]" 
  from seq.intros(2)[OF st seq.intros(1)] have "(s, ?ts) \<in> seq R" .
  then show ?thesis by (intro exI[of _ ?ts], insert lr, auto simp: get_target_def)
qed

lemma seq_mono: assumes "R \<subseteq> S" 
  and "(s,ss) \<in> seq R"
shows "(s,ss) \<in> seq S" 
  using assms(2) 
proof (induct rule: seq.induct)
  case (1 s)
  then show ?case by (auto intro: seq.intros)
next
  case (2 s t r p \<sigma> ts)
  from 2(1) assms(1) have "(s, t) \<in> rstep_r_p_s S r p \<sigma>" unfolding rstep_r_p_s_def Let_def by auto
  with 2(3) show ?case by (auto intro: seq.intros)
qed


definition check_cpeak_eld :: 
  "(('f :: showl, 'v :: showl) rule \<times> nat)list \<Rightarrow> (('f, 'v) rule \<Rightarrow> nat) \<Rightarrow> ('f, 'v) lpeak \<Rightarrow> ('f, 'v) crit_pair_info \<Rightarrow> showsl check"
where
  "check_cpeak_eld lR lab p cp_info = 
     (case p of ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) \<Rightarrow>
       let cp = (cp_left cp_info, cp_right cp_info)
         in
      do {
        check (instance_rule (t1, t2) cp) id;
        let \<alpha> = lab r1;
        let \<beta> = lab r2;
        let R1 = map fst (filter (\<lambda> r. snd r < \<alpha>) lR);
        let R2 = map fst (filter (\<lambda> r. snd r \<le> \<beta>) lR);
        let R3 = map fst (filter (\<lambda> r. snd r < max \<alpha> \<beta>) lR);
        let R4 = map fst (filter (\<lambda> r. snd r \<le> \<alpha>) lR);
        let R5 = map fst (filter (\<lambda> r. snd r < \<beta>) lR);
        check_rl_decreasing_sequence R1 R2 R3 R4 R5 
           (cp_left cp_info) (cp_right cp_info) (cp_join cp_info)
      })"

definition check_cpeak_eldc :: 
  "('f,'v)rules \<Rightarrow> (('f :: showl, 'v :: showl) rule \<times> nat)list \<Rightarrow> (('f, 'v) rule \<Rightarrow> nat) \<Rightarrow> nat option \<Rightarrow> ('f, 'v) lpeak \<Rightarrow> ('f, 'v) crit_pair_info \<Rightarrow> showsl check"
where
  "check_cpeak_eldc R lR lab n p cp_info = 
     (case p of ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) \<Rightarrow>
       let cl = cp_left cp_info;
           cr = cp_right cp_info;
           cpo = cp_peak cp_info
         in
      do {
        check (case cpo of None \<Rightarrow> False | Some _ \<Rightarrow> True) (showsl_lit (STR ''critical pair info does not specify peak''));
        let cp = the cpo;
        check (case match_list Var [(cl,t1),(cr,t2),(cp,s1)] of None \<Rightarrow> False | Some _ \<Rightarrow> True) (showsl_lit (STR ''crit-pair info does not fit to this critical pair''));
        let reach = (case n of None \<Rightarrow> (\<lambda> _. True) | Some m \<Rightarrow> (\<lambda> t. t \<in> set (reachable_terms R cp m)));
        let \<alpha> = lab r1;
        let \<beta> = lab r2;
        let R1 = map fst (filter (\<lambda> r. snd r < \<alpha>) lR);
        let R2 = map fst (filter (\<lambda> r. snd r \<le> \<beta>) lR);
        let R3 = map fst (filter (\<lambda> r. snd r < max \<alpha> \<beta>) lR);
        let R4 = map fst (filter (\<lambda> r. snd r \<le> \<alpha>) lR);
        let R5 = map fst (filter (\<lambda> r. snd r < \<beta>) lR);
        check_generic_decreasing_sequence 
          (\<lambda> (s,t). (s,t) \<in> rstep (set R1) \<or> (t,s) \<in> rstep (set R1) \<and> reach t)
          (\<lambda> (s,t). (s,t) \<in> rstep (set R2))
          (\<lambda> (s,t). (s,t) \<in> rstep (set R3) \<or> (t,s) \<in> rstep (set R3) \<and> reach t)
          (\<lambda> _. False)
          (\<lambda> (s,t). (t,s) \<in> rstep (set R4) \<and> reach t)
          (\<lambda> (t,s). (s,t) \<in> rstep (set R5) \<or> (t,s) \<in> rstep (set R5) \<and> reach t)
          (STR '' <->* . ->? . <->* . ?<- . <->* '')
           cl cr (cp_join cp_info)
      })"

lemma check_cpeak_eldc:
  defines "r \<equiv> ({(n, m) . n < m}, {(n, m) . n \<le> m})"
  assumes "(b, (s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) \<in> critical_peaks ren (set R)" (is "(b, ?p) \<in> critical_peaks ren (set R)")
  and "isOK (check_cpeak_eldc R (map (\<lambda> r. (r, lab r)) R) lab n ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) cp_info)"
  and "n = None \<longrightarrow> linear_trs (set R)"
  shows "eld_fan (set R) (rule_labeling lab) r ?p \<or> eldc (set R) (rule_labeling lab) r ?p \<and> linear_trs (set R)" (is "eld_fan _ ?l _ _ \<or> _")
proof -
  note ok = assms(3)[unfolded check_cpeak_eldc_def split bool.simps Let_def]
  from ok obtain cp where "cp_peak cp_info = Some cp" by (cases "cp_peak cp_info", auto)
  note ok = ok[unfolded this option.simps option.sel]
  define reach where "reach = (case n of None \<Rightarrow> \<lambda>_. True | Some m \<Rightarrow> \<lambda>t. t \<in> set (reachable_terms R cp m))" 
  note ok = ok[folded reach_def]
  let ?cl = "cp_left cp_info"
  let ?cr = "cp_right cp_info" 
  let ?mp = "[(?cl,t1),(?cr,t2),(cp,s1)]" 
  from ok obtain \<sigma> where match: "match_list Var ?mp = Some \<sigma>" 
    by (cases "match_list Var ?mp", auto)
  from match_list_sound[OF match, unfolded matchers_def, simplified]
  have sigma: "t1 = ?cl \<cdot> \<sigma>" "t2 = ?cr \<cdot> \<sigma>" "s1 = cp \<cdot> \<sigma>" by auto
  have id: "set (map fst (filter (\<lambda>r. snd r < l) (map (\<lambda>r. (r, lab r)) R))) = {r \<in> set R. lab r < l}"
       "set (map fst (filter (\<lambda>r. snd r \<le> l) (map (\<lambda>r. (r, lab r)) R))) = {r \<in> set R. lab r \<le> l}" for l by auto
  note ok = ok[unfolded match option.simps id, simplified]
  let ?r1 = "{r \<in> set R. lab r < lab r1}"
  let ?r2 = "{r \<in> set R. lab r \<le> lab r2}" 
  let ?r3 = "{r \<in> set R. lab r < max (lab r1) (lab r2)}" 
  let ?r4 = "{r \<in> set R. lab r \<le> lab r1}" 
  let ?r5 = "{r \<in> set R. lab r < lab r2}" 
  let ?R1 = "rstep ?r1"
  let ?R2 = "rstep ?r2" 
  let ?R3 = "rstep ?r3" 
  let ?R4 = "rstep ?r4" 
  let ?R5 = "rstep ?r5" 
  define con where "con reach R = {(s, t). (s,t) \<in> rstep R \<or> (t,s) \<in> rstep R \<and> reach t}" for R :: "('a,'b)trs" and reach
  define forw where "forw R = {(s, t). (s,t) \<in> rstep R}" for R :: "('a,'b)trs"
  define backw where "backw reach R = {(s, t). (t,s) \<in> rstep R \<and> reach t}" for R :: "('a,'b)trs" and reach
  define fanp where "fanp t = (case n of None \<Rightarrow> True | Some m \<Rightarrow> (s1,t) \<in> (rstep (set R))^*)" for t
  have reach_fan: "reach t \<Longrightarrow> fanp (t \<cdot> \<sigma>)" for t unfolding reach_def fanp_def sigma
    by (cases n, auto dest!: reachable_terms intro: rsteps_closed_subst)  
  from check_generic_decreasing_sequence[OF ok]
  have "(?cl, ?cr) \<in> (con reach ?r1)\<^sup>* O (forw ?r2)\<^sup>= O (con reach ?r3)\<^sup>* O (backw reach ?r4)\<^sup>= O ((con reach ?r5)^-1)\<^sup>*" 
    by (auto simp: con_def forw_def backw_def)
  then obtain u1 u2 u3 u4 where
    u1: "(?cl,u1) \<in> (con reach ?r1)^*" and
    u2: "(u1,u2) \<in> (forw ?r2)^=" and
    u3: "(u2,u3) \<in> (con reach ?r3)^*" and
    u4: "(u3,u4) \<in> (backw reach ?r4)^=" and
    u5: "(u4,?cr) \<in> ((con reach ?r5)^-1)^*" by blast
  have "fanp t1" "fanp t2" unfolding fanp_def using critical_peak_is_local_peak[OF assms(2), unfolded local_peaks_def]
    by (cases n, auto dest!: rstep_r_p_s_imp_rstep)+
  hence fan_start: "fanp (?cl \<cdot> \<sigma>)" "fanp (?cr \<cdot> \<sigma>)" unfolding sigma .
  {
    fix s t r
    assume st: "(s,t) \<in> con reach r" and fan: "fanp (s \<cdot> \<sigma>)" and r: "r \<subseteq> set R" 
    from st[unfolded con_def, simplified]
    have "(s \<cdot> \<sigma> , t \<cdot> \<sigma>) \<in> (rstep r)\<^sup>\<leftrightarrow> \<and> fanp (t \<cdot> \<sigma>)" 
    proof
      assume "(s,t) \<in> rstep r" 
      hence st: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep r" by auto
      hence "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep (set R)" using r by auto
      with fan have "fanp (t \<cdot> \<sigma>)" unfolding fanp_def by (cases n, auto)
      with st show ?thesis by auto
    next
      assume "(t,s) \<in> rstep r \<and> reach t" 
      with reach_fan[of t] show ?thesis by auto
    qed
  } note con_step = this
  {
    fix s t r
    assume st: "(s,t) \<in> (con reach r)^*" and fan: "fanp (s \<cdot> \<sigma>)" and r: "r \<subseteq> set R" 
    from st fan have "\<exists> ts. (s \<cdot> \<sigma>, ts) \<in> conv (set R) \<and> DD2_last (s \<cdot> \<sigma>, ts) = t \<cdot> \<sigma> 
       \<and> rule_labeling lab ` set ts \<subseteq> lab ` r \<and> Ball (set (s \<cdot> \<sigma> # t \<cdot> \<sigma> # map fst ts)) fanp" 
    proof (induct rule: converse_rtrancl_induct)
      case base
      thus ?case by (intro exI[of _ Nil], auto intro: conv.intros)
    next
      case (step s u)
      from con_step[OF step(1,4) r] have su: "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep r)\<^sup>\<leftrightarrow>" and fanu: "fanp (u \<cdot> \<sigma>)" by auto
      from step(3)[OF fanu] obtain ts where conv: "(u \<cdot> \<sigma>, ts) \<in> conv (set R)" 
       and last: "DD2_last (u \<cdot> \<sigma>, ts) = t \<cdot> \<sigma>" and lab: "rule_labeling lab ` set ts \<subseteq> lab ` r" 
       and fants: "(Ball (set (u \<cdot> \<sigma> # t \<cdot> \<sigma> # map fst ts)) fanp)" 
        by auto
      from su show ?case
      proof
        assume "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> rstep r"
        then obtain p sig lr where su: "(s \<cdot> \<sigma> ,u \<cdot> \<sigma>) \<in> rstep_r_p_s r lr p sig"
          using rstep_iff_rstep_r_p_s by blast
        hence lab': "lab lr \<in> lab ` r" unfolding rstep_r_p_s_def Let_def by auto
        from su r have su: "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> rstep_r_p_s (set R) lr p sig"  unfolding rstep_r_p_s_def Let_def by auto
        show ?thesis
          by (intro exI conjI, rule conv.intros(2)[OF su conv], insert last lab lab' fants fanu step(4), auto simp: get_source_def get_target_def)
      next
        assume "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep r)\<inverse>" 
        hence "(u \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> rstep r" by auto
        then obtain p sig lr where su: "(u \<cdot> \<sigma> ,s \<cdot> \<sigma>) \<in> rstep_r_p_s r lr p sig"
          using rstep_iff_rstep_r_p_s by blast
        hence lab': "lab lr \<in> lab ` r" unfolding rstep_r_p_s_def Let_def by auto
        from su r have su: "(u \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> rstep_r_p_s (set R) lr p sig"  unfolding rstep_r_p_s_def Let_def by auto
        show ?thesis
          by (intro exI conjI, rule conv.intros(3)[OF su conv], insert last lab lab' fants fanu step(4), auto simp: get_source_def get_target_def)
      qed
    qed
  } note conv = this
  define v1 where "v1 = u1 \<cdot> \<sigma>" 
  define v2 where "v2 = u2 \<cdot> \<sigma>" 
  define v3 where "v3 = u3 \<cdot> \<sigma>" 
  define v4 where "v4 = u4 \<cdot> \<sigma>" 

  from conv[OF u1 fan_start(1), folded v1_def sigma]
  obtain ts1 where ts1: "(t1, ts1) \<in> conv (set R)" and 
    last1: "DD2_last (t1, ts1) = v1" and
    lab1: "rule_labeling lab ` set ts1 \<subseteq> lab ` ?r1" and
    fan1: "Ball (set (map fst ts1)) fanp" and
    fanv1: "fanp v1" 
    by auto
  from u2[unfolded forw_def] have v12: "(v1, v2) \<in> (rstep ?r2)^=" unfolding v1_def v2_def by auto
  hence "(v1, v2) \<in> (rstep (set R))^=" by blast
  with fanv1 have fanv2: "fanp v2" unfolding fanp_def by (cases n, auto)
  from opt_step_to_seq[OF v12] obtain ts2 
    where "(v1, ts2) \<in> seq ?r2" 
      and last2: "DD2_last (v1, ts2) = v2"
      and lab2: "rule_labeling lab ` set ts2 \<subseteq> lab ` ?r2" 
      and len2: "length ts2 \<le> 1" 
    by blast
  from seq_mono[OF _ this(1)] have ts2: "(v1, ts2) \<in> seq (set R)" by auto
  from ts2 len2 fanv1 have fan2: "Ball (set (map fst ts2)) fanp" 
    by (cases, auto)
  from conv[OF u3, folded v2_def v3_def, OF fanv2]
  obtain ts3 where ts3: "(v2, ts3) \<in> conv (set R)" and 
    last3: "DD2_last (v2, ts3) = v3" and
    lab3: "rule_labeling lab ` set ts3 \<subseteq> lab ` ?r3" and
    fan3: "Ball (set (map fst ts3)) fanp" and
    fanv3: "fanp v3" 
    by auto
  from u4[unfolded backw_def, simplified] have "\<exists> ts4. (v4, ts4) \<in> seq ?r4
    \<and> DD2_last (v4, ts4) = v3 \<and> rule_labeling lab ` set ts4 \<subseteq> lab ` ?r4 \<and> length ts4 \<le> 1
    \<and> fanp v4" 
  proof
    assume "u3 = u4" 
    thus ?thesis using fanv3 unfolding v3_def v4_def by (intro exI[of _ Nil], auto intro: seq.intros)
  next
    assume "(u4, u3) \<in> rstep ?r4 \<and> reach u4" 
    hence v43: "(v4, v3) \<in> rstep ?r4" and fan: "fanp v4" using reach_fan[of u4] unfolding v4_def v3_def by auto
    hence "(v4,v3) \<in> (rstep ?r4)^=" by auto
    from opt_step_to_seq[OF this, of lab] fan show ?thesis by auto
  qed
  then obtain ts4 where "(v4, ts4) \<in> seq ?r4" and 
    last4: "DD2_last (v4, ts4) = v3" and
    lab4: "rule_labeling lab ` set ts4 \<subseteq> lab ` ?r4" and
    len4: "length ts4 \<le> 1" and
    fanv4: "fanp v4" 
    by auto
  from seq_mono[OF _ this(1)] have ts4: "(v4,ts4) \<in> seq (set R)" by auto
  from ts4 len4 fanv4 have fan4: "Ball (set (map fst ts4)) fanp" 
    by (cases, auto)
  from u5 have "(?cr,u4) \<in> (con reach ?r5)^*" by (rule rtrancl_converseD)
  from conv[OF this, folded v4_def, OF fan_start(2), folded sigma]
  obtain ts5 where ts5: "(t2, ts5) \<in> conv (set R)" and 
    last5: "DD2_last (t2, ts5) = v4" and
    lab5: "rule_labeling lab ` set ts5 \<subseteq> lab ` ?r5" and
    fan5: "Ball (set (map fst ts5)) fanp"
    by auto
  have ldc_trs: "ldc_trs (set R) ((s1, r1, p1, \<sigma>1, True, t1), s2, r2, p2, \<sigma>2, True, t2)
    (t1,ts1) (v1,ts2) (v2,ts3) (t2,ts5) (v4,ts4) (v3,[])" 
    unfolding ldc_trs_def first.simps fst_conv get_target_def split snd_conv if_True
    apply (intro conjI ts1 ts2 ts3  ts5  ts4 last1 last2 last3 last4 last5 refl)
    subgoal using assms(2) by (rule critical_peak_is_local_peak)
    subgoal by (intro conv.intros)
    subgoal using last3 by simp
    done
  
  have eld_conv: "eld_conv (rule_labeling lab) r ((s1, r1, p1, \<sigma>1, True, t1), s2, r2, p2, \<sigma>2, True, t2) 
    (t1,ts1) (v1,ts2) (v2,ts3) (t2,ts5) (v4,ts4) (v3,[])" 
    unfolding eld_conv_def ELD_1_def snd_conv set_map fst_conv rule_labeling.simps length_map assms(1)
    apply (intro conjI)
    subgoal using lab1 by (auto simp: under_def)
    subgoal using len2 .
    subgoal using lab2 by (auto simp: under_def)
    subgoal using lab3 by (auto simp: under_def)
    subgoal using lab5 by (auto simp: under_def)
    subgoal using len4 .
    subgoal using lab4 by (auto simp: under_def)
    subgoal by simp
    done

  show ?thesis 
  proof (cases n)
    case None
    with assms have lin: "linear_trs (set R)" by auto
    show ?thesis
      apply (intro disjI2 conjI lin)
      apply (unfold eldc_def)
      apply (intro exI conjI)
       apply (rule ldc_trs)
      apply (rule eld_conv)
      done
  next
    case (Some m)
    show ?thesis 
      apply (intro disjI1)
      apply (unfold eld_fan_def)
      apply (intro exI conjI)
        apply (rule ldc_trs)
       apply (rule eld_conv)
      apply (unfold fan_def snd_def split fst_conv get_source_def)
      apply (unfold all_set_conv_nth[where P = "\<lambda> x. (s1, fst x) \<in> (rstep (set R))\<^sup>*", symmetric])
      apply (insert fan1 fan2 fan3 fan4 fan5)
      by (auto simp: fanp_def Some)
  qed
qed

lemma linear_imp_SN_rel_d_nd:
  assumes "linear_trs R"
  shows "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
proof -
  from assms have "R_d R = {}" unfolding R_d_def linear_trs_def by auto
  then show ?thesis using SN_rel_empty1 by auto
qed

context
  fixes ren :: "'v :: {infinite,showl,compare_order} renaming2" 
begin
definition check_rule_labeling_eld ::
  "('f :: {compare_order, showl}, 'v) rules \<Rightarrow>  ('f :: {compare_order, showl}, 'v) rule_lab_repr \<Rightarrow> 
     ('f,'v)crit_pair_info list \<Rightarrow> showsl check"
where
  "check_rule_labeling_eld R lab cp_infos = do {
  let cps = critical_peaks_impl ren R R;
  let l = rule_lab_repr_to_lab lab;
  let lR = map (\<lambda> r. (r, l r)) R;
  check_allm (\<lambda>(b, (s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)). 
    try check (t1 = t2) (showsl_lit (STR '' pair non-trivial '')) catch
    (\<lambda>e. check_exm (\<lambda> cp_info. 
          (check_cpeak_eld lR l ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) cp_info))
        cp_infos (\<lambda>es. showsl_lit (STR ''\<newline>the critical peak '') \<circ> showsl_rule' showsl showsl (STR '' <- . -> '') (t1, t2) 
        \<circ> showsl_lit (STR '' could not be joined decreasingly:\<newline>'') \<circ> showsl_sep id id es)))
    cps
  }"

lemma check_rule_labeling_eld:
  assumes "isOK (check_rule_labeling_eld R lab cp_infos)"
  and "SN_rel (rstep (R_d (set R))) (rstep (R_nd (set R)))"
  and "left_linear_trs (set R)"
  shows "CR (rstep (set R))"
using assms (3,2)
proof (rule rule_labeling_is_sound_ll)
  note ok = assms(1)[unfolded check_rule_labeling_eld_def, simplified]
  let ?l = "rule_lab_repr_to_lab lab"
  define l where "l = ?l" 
  let ?rl = "rule_labeling l"
  define r where "r = ({(n, m). n < (m :: nat)}, {(n, m). n \<le> (m :: nat)})"
  let ?lR = "map (\<lambda> r. (r, l r)) R" 
  show "\<forall>(b, p) \<in> critical_peaks ren (set R). eld (set R) ?rl r p"
  proof
    fix b p
    assume p:"(b, p) \<in> critical_peaks ren (set R)"
    then have pi:"(b, p) \<in> set (critical_peaks_impl ren R R)" using critical_peaks_impl by auto
    then obtain s1 r1 p1 \<sigma>1 t1 s2 r2 p2 \<sigma>2 t2 where
      fields: "p = ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2))" 
      by (cases p, auto simp: critical_peaks_impl critical_peaks_def)
    from bspec[OF ok pi]
    have "(t1 = t2) \<or> (isOK (existsM (\<lambda> cp_info. check_cpeak_eld ?lR l p cp_info) cp_infos))"
      unfolding fields l_def by simp
    then show "eld (set R) ?rl r p"
    proof
      assume "t1 = t2"
      moreover have "p \<in> local_peaks (set R)" using critical_peak_is_local_peak fields p by fast
      ultimately show ?thesis using trivial_peak_eld unfolding fields by fast
    next
      assume "isOK (existsM (\<lambda> cp_info. check_cpeak_eld ?lR l p cp_info) cp_infos)"
      then obtain cp_info where "isOK(check_cpeak_eld ?lR l p cp_info)" by auto
      note check = this[unfolded check_cpeak_eld_def fields split bool.simps Let_def, simplified]
      have id: "fst ` set (filter (\<lambda>r. p (snd r)) (map (\<lambda>r. (r, l r)) R)) = { r \<in> set R. p (l r)}" for p
        by force
      let ?left = "cp_left cp_info"
      let ?right = "cp_right cp_info" 
      from check have inst: "instance_rule (t1, t2) (?left, ?right)" by auto
      let ?r1 = "{r \<in> set R. l r < l r1}"
      let ?r2 = "{r \<in> set R. l r \<le> l r2}" 
      let ?r3 = "{r \<in> set R. l r < max (l r1) (l r2)}" 
      let ?r4 = "{r \<in> set R. l r \<le> l r1}" 
      let ?r5 = "{r \<in> set R. l r < l r2}" 
      let ?R1 = "rstep ?r1"
      let ?R2 = "rstep ?r2" 
      let ?R3 = "rstep ?r3" 
      let ?R4 = "rstep ?r4" 
      let ?R5 = "rstep ?r5" 
      from inst obtain \<sigma> where inst: "t1 = ?left \<cdot> \<sigma>" "t2 = ?right \<cdot> \<sigma>" 
        unfolding instance_rule_def by auto
      from check_rl_decreasing_sequence[OF check[THEN conjunct2], unfolded set_map,
          unfolded id[of "\<lambda> x. x < l r1"] id[of "\<lambda> x. x \<le> l r2"] id[of "\<lambda> x. x < max (l r1) (l r2)"]
            id[of "\<lambda> x. x \<le> l r1"] id[of "\<lambda> x. x < l r2"]]
      have "(?left, ?right) \<in> ?R1^* O ?R2^= O ?R3^* O (?R3^*)^-1 O (?R4^=)^-1 O (?R5^*)^-1" 
        by auto
      also have "\<dots> = ?R1^* O ?R2^= O ?R3^* O (?R5^* O ?R4^= O ?R3^*)^-1" 
        by blast
      finally obtain u where lu: "(?left, u) \<in> ?R1^* O ?R2^= O ?R3^*" 
         and ru: "(?right,u) \<in> ?R5^* O ?R4^= O ?R3^*" by blast
      define v where "v = u \<cdot> \<sigma>" 
      from lu have t1v: "(t1,v) \<in> ?R1^* O ?R2^= O ?R3^*"  
        unfolding inst v_def using rsteps_closed_subst[of _ _ _ \<sigma>] rstep_subst[of _ _ _ \<sigma>] 
        by blast
      from ru have t2v: "(t2,v) \<in> ?R5^* O ?R4^= O ?R3^*"  
        unfolding inst v_def using rsteps_closed_subst[of _ _ _ \<sigma>] rstep_subst[of _ _ _ \<sigma>] 
        by blast
      from t1v obtain u1 w1 where tu: "(t1,u1) \<in> ?R1^*" and uw: "(u1,w1) \<in> ?R2^=" and wv: "(w1,v) \<in> ?R3^*" by auto
      from steps_to_seq[OF tu] obtain ts1 where ts1: "(t1,ts1) \<in> seq ?r1" "DD2_last (t1, ts1) = u1" "rule_labeling l ` set ts1 \<subseteq> l ` ?r1" by blast
      from opt_step_to_seq[OF uw] obtain us1 where us1: "(u1,us1) \<in> seq ?r2" "DD2_last (u1,us1) = w1" "rule_labeling l ` set us1 \<subseteq> l ` ?r2" "length us1 \<le> 1" by blast
      from steps_to_seq[OF wv] obtain ws1 where ws1: "(w1,ws1) \<in> seq ?r3" "DD2_last (w1,ws1) = v" "rule_labeling l ` set ws1 \<subseteq> l ` ?r3" by blast

      from t2v obtain u2 w2 where tu: "(t2,u2) \<in> ?R5^*" and uw: "(u2,w2) \<in> ?R4^=" and wv: "(w2,v) \<in> ?R3^*" by auto
      from steps_to_seq[OF tu] obtain ts2 where ts2: "(t2,ts2) \<in> seq ?r5" "DD2_last (t2, ts2) = u2" "rule_labeling l ` set ts2 \<subseteq> l ` ?r5" by blast
      from opt_step_to_seq[OF uw] obtain us2 where us2: "(u2,us2) \<in> seq ?r4" "DD2_last (u2,us2) = w2" "rule_labeling l ` set us2 \<subseteq> l ` ?r4" "length us2 \<le> 1" by blast
      from steps_to_seq[OF wv] obtain ws2 where ws2: "(w2,ws2) \<in> seq ?r3" "DD2_last (w2,ws2) = v" "rule_labeling l ` set ws2 \<subseteq> l ` ?r3" by auto
      show ?thesis
        unfolding r_def fields eld_def ld_trs_def eld_conv_def fst_conv snd_conv
           rule_labeling.simps get_target_def split if_True
        unfolding ELD_1_def length_map snd_conv fst_conv set_map 
        apply (rule exI[of _ "(t1,ts1)"])
        apply (rule exI[of _ "(u1,us1)"])
        apply (rule exI[of _ "(w1,ws1)"])
        apply (rule exI[of _ "(t2,ts2)"])
        apply (rule exI[of _ "(u2,us2)"])
        apply (rule exI[of _ "(w2,ws2)"])
        apply (intro conjI)
        subgoal by (rule critical_peak_is_local_peak, insert p fields, auto)
        subgoal by (rule seq_mono[OF _ ts1(1)], auto)
        subgoal by (rule seq_mono[OF _ us1(1)], auto)
        subgoal by (rule seq_mono[OF _ ws1(1)], auto)
        subgoal by (rule seq_mono[OF _ ts2(1)], auto)
        subgoal by (rule seq_mono[OF _ us2(1)], auto)
        subgoal by (rule seq_mono[OF _ ws2(1)], auto)
        subgoal by force
        subgoal using ts1 by force
        subgoal using us1 by force
        subgoal by force
        subgoal using ts2 by force
        subgoal using us2 by force
        subgoal using ws1 ws2 by force
        subgoal using ts1(3) by (auto simp: under_def)
        subgoal using us1 by force
        subgoal using us1(3) by (auto simp: under_def)
        subgoal using ws1(3) by (auto simp: under_def)
        subgoal using ts2(3) by (auto simp: under_def)
        subgoal using us2 by force
        subgoal using us2(3) by (auto simp: under_def)
        subgoal using ws2(3) by (auto simp: under_def)
        done
    qed
  qed
qed

definition check_rule_labeling_eldc ::
  "('f :: {compare_order, showl}, 'v) rules \<Rightarrow>  ('f :: {compare_order, showl}, 'v) rule_lab_repr \<Rightarrow> 
     _ \<Rightarrow> nat option \<Rightarrow> showsl check"
where
  "check_rule_labeling_eldc R lab cp_infos n = do {
  let cps = critical_peaks_impl ren R R;
  let l = rule_lab_repr_to_lab lab;
  let lR = map (\<lambda> r. (r, l r)) R;
  check_allm (\<lambda>(b, (s1, r1, p1, \<sigma>1, True, t1),(s2, r2, p2, \<sigma>2, True, t2)). 
    try check (t1 = t2) (showsl_lit (STR '' pair non-trivial '')) catch
    (\<lambda>e. check_exm (check_cpeak_eldc R lR l n ((s1, r1, p1, \<sigma>1, True, t1),(s2, r2, p2, \<sigma>2, True, t2)))
      cp_infos (\<lambda>es. showsl_nl \<circ> showsl_lit (STR ''the critical peak '') \<circ> 
        showsl t1 \<circ> showsl_lit (STR '' <- '') \<circ> showsl s1 \<circ> showsl_lit (STR '' -> '') \<circ> showsl t2 \<circ>
        showsl_lit (STR '' could not be joined decreasingly:'') \<circ> showsl_nl \<circ> showsl_sep id id es)))
    cps
  }"

lemma check_rule_labeling_eldc:
  assumes "isOK (check_rule_labeling_eldc R lab cp_infos n)"
  and "SN_rel (rstep (R_d (set R))) (rstep (R_nd (set R)))"
  and "left_linear_trs (set R)"
  and "n = None \<longrightarrow> linear_trs (set R)"
  shows "CR (rstep (set R))"
proof -
  note ok = assms(1)[unfolded check_rule_labeling_eldc_def, simplified]
  let ?l = "rule_lab_repr_to_lab lab"
  define l where "l = ?l" 
  let ?rl = "rule_labeling l"
  define r where "r = ({(n, m). n < (m :: nat)}, {(n, m). n \<le> (m :: nat)})"
  let ?lR = "map (\<lambda> r. (r, l r)) R" 
  define r where "r = ({(n, m). n < (m :: nat)}, {(n, m). n \<le> (m :: nat)})"
  { fix b p
    assume p:"(b, p) \<in> critical_peaks ren (set R)"
    then have pi:"(b, p) \<in> set (critical_peaks_impl ren R R)" using critical_peaks_impl by auto
    then obtain s r1 p1 \<sigma>1 t1 r2 p2 \<sigma>2 t2 where fields: "p = ((s,r1,p1,\<sigma>1,True,t1),(s,r2,p2,\<sigma>2,True,t2))" 
      by (cases p, auto simp: critical_peaks_impl critical_peaks_def)
    from bspec[OF ok pi, unfolded split fields, folded l_def, simplified, folded fields]
    consider (trivial) "(t1 = t2)" | (ok) cp_info where "isOK (check_cpeak_eldc R ?lR l n p cp_info)"
      by fastforce
    then have "eld_fan (set R) ?rl r p \<or> eldc (set R) ?rl r p \<and> linear_trs (set R)"
    proof (cases)
      case (trivial)
      moreover have "p \<in> local_peaks (set R)" using critical_peak_is_local_peak fields p by fast
      ultimately show ?thesis using trivial_peak_eld_fan unfolding fields by fast
    next
      case (ok)
      from check_cpeak_eldc[OF p[unfolded fields] this[unfolded fields]] assms(4) show ?thesis 
        unfolding r_def fields by auto
    qed
  }
  then consider (fan) "(\<forall>(b, p) \<in> critical_peaks ren (set R). eld_fan (set R) ?rl r p)"
    | (linear) "(\<forall>(b, p) \<in> critical_peaks ren (set R). eldc (set R) ?rl r p) \<and> linear_trs (set R)"
    unfolding eld_fan_def eldc_def by blast
  then show ?thesis
  proof (cases)
    case fan
    then show ?thesis using rule_labeling_conv_is_sound_ll[OF assms(3,2)] unfolding r_def by auto
  next
    case linear
    then show ?thesis using rule_labeling_is_sound unfolding r_def by auto
  qed
qed

end
end
