theory Location_Addition
  imports
    Cooperation_Program
begin
  
datatype ('f,'v,'t,'l,'tr) location_addition_info = Location_Addition_Info 'l 'l 'tr "('f,'v,'t,'l) transition_rule"

fun change_target :: "'l \<Rightarrow> ('f,'v,'t,'l) transition_rule \<Rightarrow> ('f,'v,'t,'l) transition_rule" where
  "change_target l (Transition src tgt \<phi>) = Transition src l \<phi>" 

fun change_source :: "'l \<Rightarrow> ('f,'v,'t,'l) transition_rule \<Rightarrow> ('f,'v,'t,'l) transition_rule" where
  "change_source l (Transition src tgt \<phi>) = Transition l tgt \<phi>" 
  
lemma if_sharp_change_target[simp]: "is_sharp_transition (change_target l tau) = is_sharp_transition tau" by (cases tau, auto)
lemma if_sharp_change_source[simp]: "is_sharp_transition (change_source l tau) = is_sharp l" by (cases tau, auto)

context lts
begin

lemma transition_rule_change_target[simp]: "transition_rule (change_target l tau) = transition_rule tau" 
  by (cases tau, auto)

lemma transition_rule_change_source[simp]: "transition_rule (change_source l tau) = transition_rule tau" 
  by (cases tau, auto)
    
context
  fixes P P'
  assumes SN: "cooperation_SN P'"
  and flat_id: "flat_transitions_of P' = flat_transitions_of P"
  and init_id: "lts.initial P' = lts.initial P" 
    "\<And> l. l \<in> lts.initial P \<Longrightarrow> assertion P l = assertion P' l"
  and lc: "\<And> l. l \<in> nodes_lts P \<Longrightarrow> assertion P' l = assertion P l" 
begin
lemma add_new_sharp_location_in_out:  
  assumes sharp_new: "\<And> \<tau>. \<tau> \<in> sharp_transitions_of P - sharp_transitions_of P' \<Longrightarrow> 
    \<exists> \<tau>' l. \<tau>' \<in> sharp_transitions_of P' \<and> skip_transition \<tau>' \<and> 
      ((change_target l \<tau> \<in> sharp_transitions_of P' 
        \<and> source \<tau>' = l \<and> target \<tau>' = target \<tau> 
        \<and> assertion P' l = assertion P (target \<tau>)) 
    \<or> (change_source l \<tau> \<in> sharp_transitions_of P' 
        \<and> source \<tau>' = source \<tau> \<and> target \<tau>' = l 
        \<and> assertion P' l = assertion P (source \<tau>)))" 
  shows "cooperation_SN P" 
proof -
  interpret P': indexed_rewriting "transition_step_lts P'" .
  from init_id have init: "initial_states P' = initial_states P" unfolding initial_states_def  by auto
  show ?thesis
  proof (rule cooperation_SN_on_trancl_image[OF _ _ SN[unfolded init flat_id]])
    fix \<tau>
    assume mem: "\<tau> \<in> sharp_transitions_of P"
    with lc[of "source \<tau>"] lc[of "target \<tau>"]
    have lc: "assertion P' (source \<tau>) = assertion P (source \<tau>)" 
      "assertion P' (target \<tau>) = assertion P (target \<tau>)" 
      unfolding nodes_lts_def by auto
    show "\<exists>ps. ps \<noteq> {} \<and> ps \<subseteq> {\<tau> \<in> transition_rules P'. is_sharp_transition \<tau>} \<and> transition_step_lts P \<tau> \<subseteq> indexed_rewriting.traverse (transition_step_lts P') ps"
    proof(cases "\<tau> \<in> sharp_transitions_of P'")
      case True
      have "transition_step_lts P \<tau> \<subseteq> P'.traverse {\<tau>}" 
      proof
        fix a b
        assume "(a,b) \<in> transition_step_lts P \<tau>" 
        then have "(a,b) \<in> transition_step_lts P' \<tau>" using lc
          by (cases a; cases b; cases \<tau>, auto)
        then show "(a,b) \<in> P'.traverse {\<tau>}" 
          by (intro P'.mem_traverseI[of "\<lambda> i. if i = 0 then a else b" _ 1], auto intro: indexed_rewriting.traversed.intros)
      qed
      then show ?thesis
        by (intro exI[of _ "{\<tau>}"], insert mem True, auto)
    next
      case False
      with mem sharp_new[of \<tau>] obtain \<tau>2 l where 
          t2: "\<tau>2 \<in> sharp_transitions_of P'" 
           "skip_transition \<tau>2" 
        and choice: "change_target l \<tau> \<in> sharp_transitions_of P' \<and> source \<tau>2 = l \<and> target \<tau>2 = target \<tau>
          \<and> assertion P' l = assertion P (target \<tau>) \<or>
            change_source l \<tau> \<in> sharp_transitions_of P' \<and> source \<tau>2 = source \<tau> \<and> target \<tau>2 = l
          \<and> assertion P' l = assertion P (source \<tau>)
            " (is "?one \<or> ?two") by auto
      from choice
      show ?thesis
      proof 
        assume *: ?one
        let ?t1 = "change_target l \<tau>" 
        have "transition_step_lts P \<tau> \<subseteq> P'.traverse {\<tau>2, ?t1}" 
        proof
          fix a b
          assume ab: "(a,b) \<in> transition_step_lts P \<tau>" 
          obtain la sa where a: "a = State sa la" by (cases a, auto)
          obtain lb sb where b: "b = State sb lb" by (cases b, auto)
          let ?c = "State sb l" 
          from ab * t2 have 1: "(a, ?c) \<in> transition_step_lts P' ?t1" and 
            t2'': "target \<tau>2 = lb" and sb: "assignment sb" 
            unfolding a b using lc by (cases \<tau>, auto)                       
          from * have src: "source \<tau>2 = l" by simp
          have 2: "(?c, b) \<in> transition_step_lts P' \<tau>2" unfolding b 
            by (rule skip_transition_step[OF t2(2) sb, unfolded src t2''], 
              insert lc * a b ab, cases \<tau>, auto)
          show "(a,b) \<in> P'.traverse {\<tau>2, ?t1}" by 
            (intro P'.mem_traverseI[of "\<lambda> i. if i = 0 then a else if i = 1 then ?c else b" _ "Suc (Suc 0)"], 
            force+, intro P'.traversed.intros, insert 1 2, auto)        
        qed
        with * t2 show ?thesis by (intro exI[of _ "{\<tau>2, ?t1}"], auto)
      next
        assume *: ?two
        let ?t1 = "change_source l \<tau>" 
        have "transition_step_lts P \<tau> \<subseteq> P'.traverse {?t1, \<tau>2}" 
        proof
          fix a b
          assume ab: "(a,b) \<in> transition_step_lts P \<tau>" 
          obtain la sa where a: "a = State sa la" by (cases a, auto)
          obtain lb sb where b: "b = State sb lb" by (cases b, auto)
          let ?c = "State sa l" 
          from ab * have 1: "(?c, b) \<in> transition_step_lts P' ?t1" and t2'': "source ?t1 = l" "source \<tau> = la" and sa: "assignment sa" 
            unfolding a b using lc * by (cases \<tau>, auto)
          from * have src: "source \<tau>2 = source \<tau>" by simp
          have 2: "(a, ?c) \<in> transition_step_lts P' \<tau>2" unfolding a
            by (insert skip_transition_step[OF t2(2) sa, unfolded src t2'']
              lc * a b ab, cases \<tau>, auto)
          show "(a,b) \<in> P'.traverse {?t1, \<tau>2}" by 
            (intro P'.mem_traverseI[of "\<lambda> i. if i = 0 then a else if i = 1 then ?c else b" _ "Suc (Suc 0)"], 
            force+, intro P'.traversed.intros, insert 1 2, auto)        
        qed
        with * t2 show ?thesis by (intro exI[of _ "{ ?t1, \<tau>2}"], auto)
      qed
    qed
  next
    fix \<tau>
    assume mem: "\<tau> \<in> flat_transitions_of P"
    with lc[of "source \<tau>"] lc[of "target \<tau>"]
    have lc: "assertion P' (source \<tau>) = assertion P (source \<tau>)" 
      "assertion P' (target \<tau>) = assertion P (target \<tau>)" 
      unfolding nodes_lts_def by auto
    then show "transition_step_lts P \<tau> = transition_step_lts P' \<tau>" by (cases \<tau>, auto)
  qed
qed

  
lemma add_new_sharp_location_incoming:  
  assumes sharp_new: "\<And> \<tau>. \<tau> \<in> sharp_transitions_of P - sharp_transitions_of P' \<Longrightarrow> 
    \<exists> \<tau>' l. change_target l \<tau> \<in> sharp_transitions_of P' \<and> \<tau>' \<in> sharp_transitions_of P' 
        \<and> skip_transition \<tau>' 
        \<and> source \<tau>' = l \<and> target \<tau>' = target \<tau> 
        \<and> assertion P' l = assertion P (target \<tau>)" 
  shows "cooperation_SN P" 
  by (rule add_new_sharp_location_in_out, insert sharp_new, blast)
    
lemma add_new_sharp_location_outgoing:  
  assumes sharp_new: "\<And> \<tau>. \<tau> \<in> sharp_transitions_of P - sharp_transitions_of P' \<Longrightarrow> 
    \<exists> \<tau>' l. change_source l \<tau> \<in> sharp_transitions_of P' \<and> \<tau>' \<in> sharp_transitions_of P' 
        \<and> skip_transition \<tau>'       
        \<and> source \<tau>' = source \<tau> \<and> target \<tau>' = l 
        \<and> assertion P' l = assertion P (source \<tau>)" 
  shows "cooperation_SN P" 
  by (rule add_new_sharp_location_in_out, insert sharp_new, blast)
end
end

context pre_lts_checker
begin
fun location_addition_incoming where
  "location_addition_incoming P (Location_Addition_Info new old skip_ID skip) = (do {
      check (new \<notin> set (nodes_lts_impl P)) (showsl_lit (STR ''location-id '') o showsl new o showsl_lit (STR '' is not fresh''));
      check (is_sharp new) (showsl_lit (STR ''new location '') o showsl new o showsl_lit (STR '' must be sharp location'')); 
      check (is_sharp old) (showsl_lit (STR ''copied location '') o showsl old o showsl_lit (STR '' must be sharp location'')); 
      check (transition_rule skip) (showsl_lit (STR ''new transition '') o showsl skip_ID o showsl_lit (STR '' seems to be ill-formed''));
      check_skip_transition skip <+? (\<lambda> s. showsl_lit (STR ''new transition '') o showsl skip_ID o showsl_lit (STR '' must be skip transition\<newline>'') o s); 
      check (source skip = new \<and> target skip = old) (showsl_lit (STR ''new skip transition '') o showsl skip_ID o showsl_lit (STR '' must be from '')
        o showsl new o showsl_lit (STR '' to '') o showsl old);
      let trans = lts_impl.transitions_impl P;
      let (sharp, flat) = partition (\<lambda> tau. is_sharp_transition (snd tau)) trans;
      let (sharp_modify, sharp_keep) = partition (\<lambda> tau. target (snd tau) = old) sharp;
      let Q = Lts_Impl (lts_impl.initial P) ((skip_ID, skip) # 
         flat @ sharp_keep @ map (\<lambda> tau. (fst tau, change_target new (snd tau))) sharp_modify)
         ((new, assertion_of P old) # assertion_impl P);
      check_allm (\<lambda> l. check (assertion_of P l =
        assertion_of Q l) (showsl_lit (STR ''location condition of initial state '') o showsl l o showsl_lit (STR '' has been changed''))) (lts_impl.initial P);
      return Q
    })" 

fun location_addition_outgoing where
  "location_addition_outgoing P (Location_Addition_Info old new skip_ID skip) = (do {
      check (new \<notin> set (nodes_lts_impl P)) (showsl_lit (STR ''location-id '') o showsl new o showsl_lit (STR '' is not fresh''));
      check (is_sharp new) (showsl_lit (STR ''new location '') o showsl new o showsl_lit (STR '' must be sharp location'')); 
      check (is_sharp old) (showsl_lit (STR ''copied location '') o showsl old o showsl_lit (STR '' must be sharp location'')); 
      check (transition_rule skip) (showsl_lit (STR ''new transition '') o showsl skip_ID o showsl_lit (STR '' seems to be ill-formed''));
      check_skip_transition skip <+? (\<lambda> s. showsl_lit (STR ''new transition '') o showsl skip_ID o showsl_lit (STR '' must be skip transition\<newline>'') o s); 
      check (source skip = old \<and> target skip = new) (showsl_lit (STR ''new skip transition '') o showsl skip_ID o showsl_lit (STR '' must be from '')
        o showsl old o showsl_lit (STR '' to '') o showsl new);
      let trans = lts_impl.transitions_impl P;
      let (sharp, flat) = partition (\<lambda> tau. is_sharp_transition (snd tau)) trans;
      let (sharp_modify, sharp_keep) = partition (\<lambda> tau. source (snd tau) = old) sharp;
      let Q = Lts_Impl (lts_impl.initial P) ((skip_ID, skip) # 
         flat @ sharp_keep @ map (\<lambda> tau. (fst tau, change_source new (snd tau))) sharp_modify)
         ((new, assertion_of P old) # assertion_impl P); 
      check_allm (\<lambda> l. check (assertion_of P l =
        assertion_of Q l) (showsl_lit (STR ''location condition of initial state '') o showsl l o showsl_lit (STR '' has been changed''))) (lts_impl.initial P);
      return Q
    })" 
  
definition location_addition where
  "location_addition P info = (case info of Location_Addition_Info src tgt _ _ \<Rightarrow> if
     src \<notin> set (nodes_lts_impl P) 
    then location_addition_incoming P info 
    else location_addition_outgoing P info)"
  
end

declare pre_lts_checker.location_addition_incoming.simps[code]
declare pre_lts_checker.location_addition_outgoing.simps[code]
declare pre_lts_checker.location_addition_def[code]

lemma filter_mset_union:
  shows "filter_mset f M + filter_mset g M = filter_mset (\<lambda>x. f x \<or> g x) M + filter_mset (\<lambda>x. f x \<and> g x) M"
  by(fold count_inject, auto)

lemma mset_filter_union:
  "mset (filter f xs) + mset (filter g xs) = mset (filter (\<lambda>x. f x \<or> g x) xs) + mset (filter (\<lambda>x. f x \<and> g x) xs)"
proof-
  have "mset (filter f xs) + mset (filter g xs) = filter_mset f (mset xs) + filter_mset g (mset xs)" by (simp add: mset_filter)
  also have "... = filter_mset (\<lambda>x. f x \<or> g x) (mset xs) + filter_mset (\<lambda>x. f x \<and> g x) (mset xs)"
    by (rule filter_mset_union)
  finally show ?thesis by (simp add: mset_filter)
qed

context lts_checker
begin

lemma location_addition_incoming: assumes SN: "cooperation_SN_impl Q"
  and la: "location_addition_incoming P info = return Q"
shows "cooperation_SN_impl P"
proof (cases info)
  case (Location_Addition_Info new old skip_ID skip)
  note la = la[unfolded this]
  note la = la[simplified, unfolded Let_def o_def, simplified]
  from la have Q: "Q = Lts_Impl (lts_impl.initial P)
   ((skip_ID, skip) #
    [tau\<leftarrow>transitions_impl P . \<not> is_sharp_transition (snd tau)] @
    [x\<leftarrow>transitions_impl P . is_sharp_transition (snd x) \<and> target (snd x) \<noteq> old] @
    map (\<lambda>tau. (fst tau, change_target new (snd tau))) [x\<leftarrow>transitions_impl P . is_sharp_transition (snd x) \<and> target (snd x) = old])
    ( (new, assertion_of P old) # assertion_impl P)" by auto
  from la have "isOK(check_skip_transition skip)" by auto
  from check_skip_transition[OF this] la
  have skip: "skip_transition skip" "transition_rule skip" by auto
  from la have sharp_skip: "skip \<in> sharp_transitions_of (lts_of Q)" by (cases skip; auto)
  then have flat_skip: "is_sharp_transition skip" by (cases skip; cases "source skip", auto)
  show ?thesis
  proof (intro cooperation_SN_implI)
    assume P: "lts_impl P"
    then have impl: "lts_impl Q"
    proof (intro lts_implI)
      show "(tr, \<tau>) \<in> set (transitions_impl Q) \<Longrightarrow> transition_rule \<tau>" for tr \<tau>
        using P skip(2) by (auto elim!: lts_implE simp: Q)
      show "(l, \<phi>) \<in> set (assertion_impl Q) \<Longrightarrow> formula \<phi> " for l \<phi>
        using P by (auto elim!: lts_implE simp: Q assertion_of_def intro: map_of_defaultI)
    qed
    show "cooperation_SN (lts_of P)"
    proof (rule add_new_sharp_location_incoming)
      show "cooperation_SN (lts_of Q)" using SN impl by (elim cooperation_SN_implE)
      show "lts.initial (lts_of Q) = lts.initial (lts_of P)" by (auto simp: Q)
      show "flat_transitions_of (lts_of Q) = flat_transitions_of (lts_of P)" by (auto simp: flat_skip Q)
      show "l \<in> lts.initial (lts_of P) \<Longrightarrow> assertion (lts_of P) l = assertion (lts_of Q) l" for l using la by auto
      fix \<tau>
      assume "\<tau> \<in> sharp_transitions_of (lts_of P) - sharp_transitions_of (lts_of Q)" 
      then have tau: "target \<tau> = old" "change_target new \<tau> \<in> sharp_transitions_of (lts_of Q)" unfolding Q by auto
      have lc: "assertion (lts_of Q) new = assertion (lts_of P) old" 
        unfolding Q 
        by (auto simp: assertion_of_def map_of_default_def lookup_default_def lookup_of_alist)
      show "\<exists>\<tau>' l. change_target l \<tau> \<in> sharp_transitions_of (lts_of Q) \<and>
                \<tau>' \<in> sharp_transitions_of (lts_of Q) \<and> skip_transition \<tau>' \<and> source \<tau>' = l \<and> target \<tau>' = target \<tau>
             \<and> assertion (lts_of Q) l = assertion (lts_of P) (target \<tau>)" 
        by (intro exI conjI, rule tau(2), rule sharp_skip, rule skip, unfold tau, insert la lc, auto)
    next
      fix l 
      assume "l \<in> nodes_lts (lts_of P)" 
      with la have "l \<noteq> new" by auto
      then show "assertion (lts_of Q) l = assertion (lts_of P) l"
        by (auto simp: Q map_of_default_def lookup_default_def assertion_of_def lookup_of_alist)
    qed
  qed
qed

lemma location_addition_outgoing: assumes SN: "cooperation_SN_impl Q"
  and la: "location_addition_outgoing P info = return Q"
shows "cooperation_SN_impl P"
proof (cases info)
  case (Location_Addition_Info old new skip_ID skip) 
  note la = la[unfolded this]
  note la = la[simplified, unfolded Let_def o_def, simplified]
  from la have Q: "Q = Lts_Impl (lts_impl.initial P)
   ((skip_ID, skip) #
    [tau\<leftarrow>transitions_impl P . \<not> is_sharp_transition (snd tau)] @
    [x\<leftarrow>transitions_impl P . is_sharp_transition (snd x) \<and> source (snd x) \<noteq> old] @
    map (\<lambda>tau. (fst tau, change_source new (snd tau))) [x\<leftarrow>transitions_impl P . is_sharp_transition (snd x) \<and> source (snd x) = old])
    ( (new, assertion_of P old) # assertion_impl P)" by auto
  from la have "isOK(check_skip_transition skip)" by auto
  from check_skip_transition[OF this] la
  have skip: "skip_transition skip" "transition_rule skip" by auto
  from la have sharp_skip: "skip \<in> sharp_transitions_of (lts_of Q)" by (cases skip; auto)
  then have flat_skip: "is_sharp_transition skip" by (cases skip; cases "source skip", auto)
  show ?thesis
  proof
    assume P: "lts_impl P"
    then have impl: "lts_impl Q"
    proof (intro lts_implI)
      show "(tr, \<tau>) \<in> set (transitions_impl Q) \<Longrightarrow> transition_rule \<tau>" for tr \<tau>
        using P skip(2) by (auto elim!: lts_implE simp: Q)
      show "(l, \<phi>) \<in> set (assertion_impl Q) \<Longrightarrow> formula \<phi> " for l \<phi>
        using P by (auto elim!: lts_implE simp: Q assertion_of_def intro: map_of_defaultI)
    qed
    show "cooperation_SN (lts_of P)"
    proof (rule add_new_sharp_location_outgoing)
      show "cooperation_SN (lts_of Q)" using impl SN by auto
      show "lts.initial (lts_of Q) = lts.initial (lts_of P)" by (auto simp: Q)
      from la have sharp_new: "is_sharp new" by auto
      then show "flat_transitions_of (lts_of Q) = flat_transitions_of (lts_of P)" by (auto simp: flat_skip Q)
      show "l \<in> lts.initial (lts_of P) \<Longrightarrow> assertion (lts_of P) l = assertion (lts_of Q) l" for l using la by auto
      fix \<tau>
      assume "\<tau> \<in> sharp_transitions_of (lts_of P) - sharp_transitions_of (lts_of Q)" 
      with sharp_new have tau: "source \<tau> = old" "change_source new \<tau> \<in> sharp_transitions_of (lts_of Q)" unfolding Q by auto
      have lc: "assertion (lts_of Q) new = assertion (lts_of P) old" 
        unfolding Q 
        by (auto simp: assertion_of_def map_of_default_def lookup_default_def lookup_of_alist)
      show "\<exists>\<tau>' l. change_source l \<tau> \<in> sharp_transitions_of (lts_of Q) \<and>
                \<tau>' \<in> sharp_transitions_of (lts_of Q) \<and> skip_transition \<tau>' \<and> source \<tau>' = source \<tau> \<and> target \<tau>' = l
             \<and> assertion (lts_of Q) l = assertion (lts_of P) (source \<tau>)" 
        by (intro exI conjI, rule tau(2), rule sharp_skip, rule skip, unfold tau, insert la lc, auto)
    next
      fix l 
      assume "l \<in> nodes_lts (lts_of P)" 
      with la have "l \<noteq> new" by auto
      then show "assertion (lts_of Q) l = assertion (lts_of P) l"
        by (auto simp: Q map_of_default_def lookup_default_def assertion_of_def lookup_of_alist)
    qed
  qed
qed

lemma location_addition: assumes SN: "cooperation_SN_impl Q"
  and la: "location_addition P info = return Q"
shows "cooperation_SN_impl P"
proof (cases info)
  case (Location_Addition_Info src)
  from la[unfolded location_addition_def this location_addition_info.simps, folded this]
    location_addition_incoming location_addition_outgoing SN
  show ?thesis by (auto split: if_splits)
qed

end

end
