(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Dual_Multiset_Impl
imports 
  Dual_Multiset
  Weighted_Path_Order.Multiset_Extension2_Impl
begin

definition dms_order_ext :: "nat \<Rightarrow> 'a list_ext_impl" where 
  "dms_order_ext n S_NS as bs \<equiv> let S = {(a,b). fst (S_NS a b)}; NS = {(a,b). snd (S_NS a b)}
       in ((as,bs) \<in> dms_order n True S NS, (as,bs) \<in> dms_order n False S NS)"

lemma dms_order_ext_list_ext: "\<exists> s ns. list_order_extension_impl s ns (dms_order_ext n)"
proof(intro exI)
  let ?s = "dms_order n True"
  let ?ns = "dms_order n False"
  let ?o = "dms_order_ext n"
  show "list_order_extension_impl ?s ?ns ?o"
  proof
    fix s ns
    show "?s {(a,b). s a b} {(a,b). ns a b} = {(as,bs). fst (?o (\<lambda> a b. (s a b, ns a b)) as bs)}" 
      unfolding dms_order_ext_def Let_def by auto
  next
    fix s ns
    show "?ns {(a,b). s a b} {(a,b). ns a b} = {(as,bs). snd (?o (\<lambda> a b. (s a b, ns a b)) as bs)}" 
      unfolding dms_order_ext_def Let_def by auto
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?s s ns"
    then show "(as,bs) \<in> ?s s' ns'" by (rule dms_order_mono)
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?ns s ns"
    then show "(as,bs) \<in> ?ns s' ns'" by (rule dms_order_mono)
  qed
qed

text \<open>towards executable version of dms_order_ext,
  idea:
  -  first convert into boolean problem after computing all relations
     has been performed as preprocessing step; 
  -  solve boolean problem 
\<close>

definition dms_convert :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list 
  \<Rightarrow> (nat \<times> (bool \<times> bool))list list"
  where "dms_convert f as bs \<equiv> let jbs = zip [0 ..< length bs] bs in
            map (\<lambda> a. map (\<lambda> (j,b). (j,f a b)) jbs) as"

abbreviation dms_bool_idx_i where "dms_bool_idx_i idx jsns i \<equiv>
     fst (idx i) < length (jsns ! i) \<and>
     (snd (idx i) \<longrightarrow> fst (snd (jsns ! i ! fst (idx i)))) \<and>
     (\<not> snd (idx i) \<longrightarrow> snd (snd (jsns ! i ! fst (idx i)))) \<and>
     (\<not> snd (idx i) \<longrightarrow> (\<forall> i' < length jsns. fst (jsns ! i ! fst (idx i)) = fst (jsns ! i' ! fst (idx i')) \<longrightarrow> i = i'))"

abbreviation dms_bool_idx where "dms_bool_idx idx jsns stri lts \<equiv> (\<forall> i < length jsns. dms_bool_idx_i idx jsns i) \<and> (stri \<longrightarrow> (\<exists> j < lts. (\<forall> i < length jsns. (fst (jsns ! i ! fst (idx i)), snd (idx i)) \<noteq> (j,False))))"


lemma dms_order_idx_bool: "(\<exists> idx. dms_order_idx {(a,b). fst (f a b)} {(a,b). snd (f a b)} idx as bs stri) = (\<exists> idx. dms_bool_idx idx (dms_convert f as bs) stri (length bs))" (is "?l = ?r")
proof -
  let ?S = "{(a,b). fst (f a b)}"
  let ?NS = "{(a,b). snd (f a b)}"
  let ?p = "dms_convert f as bs"
  note d = dms_convert_def[of f as bs, unfolded Let_def]
  show ?thesis
  proof
    assume ?l
    then obtain idx where idx: "dms_order_idx ?S ?NS idx as bs stri" ..
    {
      fix i
      assume "i < length ?p"
      then have i: "i < length as" unfolding d by simp
      from idx i have idx_i: "dms_order_idx_i ?S ?NS idx as bs i" by simp
      {
        assume nsnd: "\<not> snd (idx i)"
        {
          fix i'
          assume i': "i' < length ?p" and eq: "fst (?p ! i ! fst (idx i)) = fst (?p ! i' ! fst (idx i'))"
          from i'[unfolded d] have i': "i' < length as" by simp
          from i i' nsnd idx_i have goal: "fst (idx i) = fst (idx i') \<Longrightarrow> i = i'"
             by blast
          {
            fix i
            assume i: "i < length as"
            from i idx have idx_i: "fst (idx i) < length bs" by auto            
            then have "fst (map (\<lambda>a. map (\<lambda>(j, b). (j, f a b)) (zip [0..<length bs] bs)) as ! i ! fst (idx i)) = fst (idx i)" using i by auto
          } note id = this
          have "i = i'" 
            by (rule goal, insert eq, unfold d id[OF i] id[OF i'], simp)
        }
      } note cond = this
      have "dms_bool_idx_i idx ?p i" 
      proof (intro conjI)
        show "fst (idx i) < length (?p ! i)" using idx_i i unfolding d by simp
      next
        show "snd (idx i) \<longrightarrow> fst (snd (?p ! i ! fst (idx i)))" using idx_i i unfolding d by simp
      next
        show "\<not> snd (idx i) \<longrightarrow> snd (snd (?p ! i ! fst (idx i)))" using idx_i i unfolding d by simp
      qed (insert cond, auto)
    } note bool_idx = this
    show ?r
    proof (rule exI[of _ idx], intro conjI impI, intro allI impI, rule bool_idx)
      assume stri
      with idx obtain j where j: "j < length bs" and neq: "\<And> i. i < length as \<Longrightarrow> idx i \<noteq> (j,False)" by blast
      show "\<exists> j < length bs. \<forall> i < length ?p. (fst (?p ! i ! fst (idx i)), snd (idx i)) \<noteq> (j, False)"
      proof (intro exI conjI allI impI, rule j)
        fix i
        assume i: "i < length ?p"
        note bool_i = bool_idx[OF i]
        from i[unfolded d] have i: "i < length as" by simp
        have "fst (?p ! i ! fst (idx i)) = fst (idx i)"
          using bool_i
          unfolding d nth_map[OF i]
          by simp
        then have "(fst (?p ! i ! fst (idx i)), snd (idx i)) = (fst (idx i), snd (idx i))" (is "?l = _") by simp
        also have "... = idx i" by simp
        also have "... \<noteq> (j, False)" by (rule neq[OF i])
        finally show "?l \<noteq> (j, False)" .
      qed
    qed
  next
    assume ?r
    then obtain idx where idx: "dms_bool_idx idx ?p stri (length bs)" by blast
    {
      fix i
      assume i: "i < length as"
      then have ip: "i < length ?p" unfolding d by simp
      from idx ip have idx_i: "dms_bool_idx_i idx ?p i" by simp
      {
        assume nsnd: "\<not> snd (idx i)"
        {
          fix i'
          assume i': "i' < length as" and eq: "fst (idx i) = fst (idx i')"
          from i'[unfolded d] have i': "i' < length as" by simp
          from i i' nsnd idx_i[THEN conjunct2] 
          have goal: "fst (?p ! i ! fst (idx i)) = fst (?p ! i' ! fst (idx i')) \<Longrightarrow> i = i'"
            unfolding d length_map
             by blast
          {
            fix i
            assume i: "i < length as"
            from i idx have idx_i: "fst (idx i) < length bs" unfolding d by auto            
            then have "fst (map (\<lambda>a. map (\<lambda>(j, b). (j, f a b)) (zip [0..<length bs] bs)) as ! i ! fst (idx i)) = fst (idx i)" using i by auto
          } note id = this
          have "i = i'" 
            by (rule goal, insert eq, unfold d id[OF i] id[OF i'], simp)
        }
      } note cond = this
      have "dms_order_idx_i ?S ?NS idx as bs i" 
      proof (intro conjI)
        show "fst (idx i) < length bs" using idx_i i unfolding d by simp
      next
        show "snd (idx i) \<longrightarrow> (as ! i, bs ! fst (idx i)) \<in> ?S" using idx_i i unfolding d by auto
      next
        show "\<not> snd (idx i) \<longrightarrow> (as ! i, bs ! fst (idx i)) \<in> ?NS" using idx_i i unfolding d by auto
      next
      qed (insert cond, auto)
    } note order_idx = this
    show ?l
    proof (rule exI[of _ idx], intro conjI impI, intro allI impI, rule order_idx)
      assume stri
      with idx obtain j where j: "j < length bs" and neq: "\<And> i. i < length as \<Longrightarrow> (fst (?p ! i ! fst (idx i)), snd (idx i)) \<noteq> (j,False)" 
        unfolding d length_map by blast
      show "\<exists> j < length bs. \<forall> i < length as. idx i \<noteq> (j, False)"
      proof (intro exI conjI allI impI, rule j)
        fix i
        assume i: "i < length as"
        note order_i = order_idx[OF i]
        have id: "fst (?p ! i ! fst (idx i)) = fst (idx i)"
          using order_i 
          unfolding d nth_map[OF i]
          by simp
        have "idx i = (fst (?p ! i ! fst (idx i)), snd (idx i))" unfolding id by simp
        also have "... \<noteq> (j, False)" by (rule neq[OF i])
        finally show "idx i \<noteq> (j, False)" .
      qed
    qed
  qed
qed

definition dms_bool_ex_idx :: "bool \<Rightarrow> nat \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> bool"
  where "dms_bool_ex_idx stri lts jsns \<equiv> (\<exists> idx. dms_bool_idx idx jsns stri lts)"

definition dms_bool :: "nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> bool"
  where "dms_bool n stri lts jsns \<equiv> (lts \<le> n \<or> length jsns = lts) 
  \<and> dms_bool_ex_idx stri lts jsns"

lemma dms_order_bool: "((as, bs) \<in> dms_order n stri {(a,b). fst (f a b)} {(a,b). snd (f a b)}) = dms_bool n stri (length bs) (dms_convert f as bs)" (is "?l = ?r")
proof -
  note d = dms_order_def dms_bool_def dms_bool_ex_idx_def
  note conv = dms_order_idx_bool
  let ?S = "{(a,b). fst (f a b)}"
  let ?NS = "{(a,b). snd (f a b)}"
  let ?p = "dms_convert f as bs"
  show ?thesis
  proof
    assume ?l
    from this[unfolded d]
    have len: "length bs \<le> n \<or> length as = length bs" and idx: "\<exists> idx. dms_order_idx ?S ?NS idx as bs stri" by blast+
    show ?r unfolding d 
      by (rule conjI[OF _ idx[unfolded conv]], insert len, unfold dms_convert_def, auto)
  next
    assume ?r
    from this[unfolded d]
    have len: "length bs \<le> n \<or> length as = length bs" and idx: "\<exists> idx. dms_bool_idx idx ?p stri (length bs)" unfolding dms_convert_def by auto
    show ?l unfolding d conv using len idx by auto
  qed
qed
  
lemma dms_order_ext_bool[code]: "dms_order_ext n f as bs = (
   let p = dms_convert f as bs; 
       lts = length bs;
       len = lts \<le> n \<or> length as = lts in
         (len \<and> dms_bool_ex_idx True lts p, len \<and> dms_bool_ex_idx False lts p))"
  unfolding dms_order_ext_def Let_def dms_order_bool 
  unfolding dms_bool_def by (auto simp: dms_convert_def)

(* at this point, it remains to write executable version of dms_bool_ex_idx *)

definition dms_size :: "(nat \<times> bool \<times> bool) list list \<Rightarrow> nat"
  where "dms_size \<equiv> size_list size"


lemma dms_bool_ex_idx_mono_idx: assumes subset: "\<And> i idx. i < length p' \<Longrightarrow> dms_bool_idx idx p stri n  \<Longrightarrow> dms_bool_idx_i idx p i \<Longrightarrow> p ! i ! fst (idx i) \<in> set (p ! i) \<Longrightarrow> p ! i ! fst (idx i) \<in> set (p' ! i)"
  and len: "length p = length p'"
  and idx: "dms_bool_ex_idx stri n p"
  shows "dms_bool_ex_idx stri n p'"
proof -
  note d = dms_bool_ex_idx_def 
  from idx[unfolded d] obtain idx where idx: "dms_bool_idx idx p stri n" ..
  {
    fix i
    assume i: "i < length p'"
    note idx_i = idx[THEN conjunct1, rule_format, OF i[unfolded len[symmetric]]]
    from idx_i have "p ! i ! fst (idx i) \<in> set (p ! i)" by auto
    from subset[OF i idx idx_i, OF this]
    have "p ! i ! fst (idx i) \<in> set (p' ! i)" by auto
    then have "\<exists> i'. i' < length (p' ! i) \<and> p ! i ! fst (idx i) = p' ! i ! i'" unfolding set_conv_nth by auto
  }
  then have "\<forall> i. \<exists> i'. i < length p' \<longrightarrow> (i' < length (p' ! i) \<and> p ! i ! fst (idx i) = p' ! i ! i')" by blast
  from choice[OF this]
  obtain ii where ii: "\<And> i. i < length p' \<Longrightarrow> ii i < length (p' ! i) \<and> p ! i ! fst (idx i) = p' ! i ! ii i" by auto
  let ?idx = "\<lambda> i. (ii i, snd (idx i))"
  show ?thesis unfolding d
  proof (rule exI, intro conjI impI, intro allI impI)
    fix i
    assume i: "i < length p'"
    note idx_i = idx[THEN conjunct1, rule_format, unfolded len, OF i]
    then show "dms_bool_idx_i ?idx p' i" using ii[OF i] ii by auto
  next
    assume stri
    from idx[THEN conjunct2, rule_format, OF this]
    obtain j where j: "j < n" and neq: "\<And> i. i < length p' \<Longrightarrow> (fst (p ! i ! fst (idx i)), snd (idx i)) \<noteq> (j,False)" unfolding len by auto
    show "\<exists> j < n. \<forall> i < length p'. (fst (p' ! i ! fst (?idx i)), snd (?idx i))
      \<noteq> (j,False)"
      by (intro exI conjI, rule j, insert neq ii, auto)
  qed
qed

lemma dms_bool_ex_idx_mono: assumes subset: "\<And> i. i < length p' \<Longrightarrow> set (p ! i) \<subseteq> set (p' ! i)"
  and len: "length p = length p'"
  and idx: "dms_bool_ex_idx stri n p"
  shows "dms_bool_ex_idx stri n p'"
  by (rule dms_bool_ex_idx_mono_idx[OF _ len idx], insert subset, blast)

(* simplifies a dms problem where the list of natural numbers are the number of those rows that have last been modified,
   TODO: extend to proper simplifier which deletes entries and makes deductions *)
definition dms_simplify :: "bool \<Rightarrow> nat list \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> (nat \<times> bool \<times> bool) list list"
  where "dms_simplify stri is p \<equiv> if (\<exists> i \<in> set is. p ! i = []) then [[]] else p"

lemma dms_simplify: assumes ix: "\<And> i. i \<in> set ix \<Longrightarrow> i < length p"
  shows "dms_bool_ex_idx stri n (dms_simplify stri ix p) = dms_bool_ex_idx stri n p" 
proof (cases "\<exists> i \<in> set ix. p ! i = []") 
  case False
  then show ?thesis unfolding dms_simplify_def by auto
next
  case True
  then obtain i where i: "i \<in> set ix" and empty: "p ! i = []" by auto
  have "dms_bool_ex_idx stri n (dms_simplify stri ix p) = dms_bool_ex_idx stri n [[]]"
    unfolding dms_simplify_def using True by simp
  also have "... = False" by (simp add: dms_bool_ex_idx_def)
  also have "... = dms_bool_ex_idx stri n p"
    unfolding dms_bool_ex_idx_def
  proof
    assume "\<exists> idx. dms_bool_idx idx p stri n" 
    then obtain idx where "dms_bool_idx idx p stri n" by auto
    from this[THEN conjunct1, rule_format, OF ix[OF i]] empty show False by auto
  qed auto
  finally show ?thesis .
qed

lemma dms_simplify_size: assumes ix: "\<And> i. i \<in> set ix \<Longrightarrow> i < length p"
  shows "dms_size (dms_simplify stri ix p) \<le> dms_size p" 
proof - 
  note d =  dms_simplify_def dms_size_def 
  show ?thesis 
  proof (cases "\<exists> i \<in> set ix. p ! i = []") 
    case False
    then show ?thesis unfolding d by auto
  next
    case True
    then obtain i where i: "i \<in> set ix" by auto
    from ix[OF i] obtain h t where p: "p = h # t" by (cases p, auto)
    from True have id: "dms_simplify stri ix p = [[]]" unfolding d by simp
    show ?thesis unfolding id unfolding p d by simp
  qed
qed
    

definition dms_decide_singletons :: "bool \<Rightarrow> nat \<Rightarrow> (nat \<times> bool \<times> bool) list \<Rightarrow> bool"
  where "dms_decide_singletons stri n p \<equiv> (\<forall> i < length p. case (p ! i) of
           (j,s,ns) \<Rightarrow> (s \<and> (j,False,True) \<notin> set (drop (Suc i) p)) \<or> (ns \<and> j \<notin> set (map fst (drop (Suc i) p)))) \<and> (stri \<longrightarrow> (\<exists> j \<in> set [0 ..< n] . (j,False,True) \<notin> set p))"

definition dms_singleton_idx :: "(nat \<times> bool \<times> bool) list \<Rightarrow> nat \<Rightarrow> nat \<times> bool"
  where "dms_singleton_idx p \<equiv> \<lambda> i. (let (idx,s,ns) = p ! i in (0,s))"

lemma dms_decide_singletons: "dms_decide_singletons stri n p =  
  dms_bool_ex_idx stri n (map (\<lambda> e. [e]) p)" (is "?l = ?r")
proof -
  note d = dms_bool_ex_idx_def dms_decide_singletons_def
    dms_singleton_idx_def[unfolded Let_def]
  let ?idx = "dms_singleton_idx p"
  let ?p = "(map (\<lambda> e. [e]) p)" 
  {
    assume ?l
    note l = this[unfolded d]
    have ?r unfolding d
    proof (rule exI[of _ ?idx])
      show "dms_bool_idx ?idx ?p stri n"
      proof(intro conjI impI, intro allI impI)
        fix i
        assume "i < length ?p"
        then have i: "i < length p" by auto
        obtain j s ns where pi: "p ! i = (j,s,ns)" by (cases "p ! i", auto)
        from l[THEN conjunct1, rule_format, OF i] pi  
        have disj: "s \<and> (j, False, True) \<notin> set (drop (Suc i) p) \<or>    
                       ns \<and> (j \<notin> set (map fst (drop (Suc i) p )))" by auto
        from pi  have idx: "?idx i = (0,s)" unfolding d by simp
        show "dms_bool_idx_i ?idx ?p i" 
        proof (intro conjI impI allI, unfold idx fst_conv snd_conv nth_map[OF i] pi nth_Cons_0 length_map) 
          assume "\<not> s" with disj show ns by blast
        next
          fix i'
          assume ns: "\<not> s" and i': "i' < length p" and j: "j = fst (?p ! i' ! fst (?idx i'))"
          obtain j' s' ns' where pi': "p ! i' = (j',s',ns')" by (cases "p ! i'", auto)
          have pi': "p ! i' = (j,s',ns')" unfolding j d pi' nth_map[OF i'] by simp
          from l[THEN conjunct1, rule_format, OF i'] pi' have disj': 
            "s' \<and> (j, False, True) \<notin> set (drop (Suc i') p) \<or>    
              ns' \<and> (j \<notin> set (map fst (drop (Suc i') p )))" by auto
          from ns disj pi have pi: "p ! i = (j, False, True)" by simp
          from ns disj have nmem: "j \<notin> set (map fst (drop (Suc i) p))" by auto
          show "i = i'"
          proof (rule ccontr)
            assume "i \<noteq> i'"
            then have "i < i' \<or> i > i'" by auto
            then show False
            proof
              assume "i < i'"
              then have "i' = Suc i + (i' - Suc i)" by auto
              then obtain k where ii': "i' = Suc i + k" by auto
              from i' ii' have len: "Suc i + k \<le> length p" by simp
              have "(j,s',ns') \<in> set (drop (Suc i) p)" unfolding pi'[symmetric] unfolding ii' set_conv_nth nth_drop[OF len, symmetric]
                by (rule, rule exI[of _ k], insert i' ii', auto)
              with nmem show False by force
            next
              assume "i' < i"
              then have "i = Suc i' + (i - Suc i')" by auto
              then obtain k where ii': "i = Suc i' + k" by auto
              from i ii' have len: "Suc i' + k \<le> length p" by simp
              have "(j,False,True) \<in> set (drop (Suc i') p)" unfolding pi[symmetric] unfolding ii' set_conv_nth nth_drop[OF len, symmetric]
                by (rule, rule exI[of _ k], insert i ii', auto)
              with disj' show False by force
            qed
          qed
        qed auto
      next
        assume stri
        from l[THEN conjunct2, rule_format, OF this]
        obtain k where k: "k < n" and nmem: "(k,False,True) \<notin> set p" by auto
        show "\<exists> j < n. \<forall> i < length ?p. (fst (?p ! i ! fst (?idx i)), snd (?idx i)) \<noteq> (j,False)"
        proof (intro exI conjI allI impI, rule k, unfold length_map)
          fix i
          assume i: "i < length p"
          obtain j s ns where pi: "p ! i = (j,s,ns)" by (cases "p ! i", auto)
          from l[THEN conjunct1, rule_format, OF i] pi  
          have disj: "s \<and> (j, False, True) \<notin> set (drop (Suc i) p) \<or>    
            ns \<and> (j \<notin> set (map fst (drop (Suc i) p )))" by auto
          from pi  have idx: "?idx i = (0,s)" unfolding d by simp
          show "(fst (?p ! i ! fst (?idx i)), snd (?idx i)) \<noteq> (k,False)"
            unfolding idx fst_conv snd_conv nth_map[OF i] pi nth_Cons_0
          proof
            assume "(j,s) = (k,False)"
            then have jk: "j = k" and s: "s = False" by auto
            from pi i have "(j,s,ns) \<in> set p" unfolding set_conv_nth by force
            with jk s have "(k,False,ns) \<in> set p" by simp
            with nmem have ns: "ns = False" by auto
            from disj s ns jk show False by simp
          qed
        qed
      qed
    qed
  }
  moreover
  {
    assume r: ?r
    from this[unfolded dms_bool_ex_idx_def]
    obtain idx where idx: "dms_bool_idx idx ?p stri n" ..
    have ?l unfolding dms_decide_singletons_def
    proof (intro impI conjI, intro allI impI)
      fix i
      assume i: "i < length p"
      note idx_i = idx[THEN conjunct1, rule_format, unfolded length_map, OF i, unfolded length_map nth_map[OF i]]
      from idx_i have fst: "fst (idx i) = 0" by simp
      note idx_i = idx_i[unfolded fst nth_Cons_0]
      obtain j s ns where pi: "p ! i = (j,s,ns)" by (cases "p ! i", auto)
      note idx_i = idx_i[unfolded pi fst_conv snd_conv]
      let ?d = "drop (Suc i) p"
      let ?md = "map fst ?d"
      show "case p ! i of (j,s,ns) \<Rightarrow> 
        s \<and> (j,False,True) \<notin> set (drop (Suc i) p) \<or>
        ns \<and> j \<notin> set (map fst (drop (Suc i) p))"
      proof (cases "snd (idx i)")
        case False        
        with idx_i have nsnd: "\<not> snd (idx i)" and ns: "ns" by auto
        from idx_i nsnd have j_id: "\<And> i'. i' < length p \<Longrightarrow> j = fst (?p ! i' ! fst (idx i')) \<Longrightarrow> i = i'" by auto
        have  "j \<notin> set ?md"
        proof
          assume "j \<in> set ?md"
          from this[unfolded set_conv_nth] obtain k where k: "k < length ?d"
            and j: "j = ?md ! k" by auto
          from j[unfolded nth_map[OF k]] have j: "j = fst (drop (Suc i) p ! k)"
            by simp
          let ?i = "Suc i + k"
          from k i have i': "?i < length p" unfolding length_drop by simp
          from idx[THEN conjunct1, rule_format, of ?i] i'
          have idx_i': "dms_bool_idx_i idx ?p ?i" by auto
          note idx_i' = idx_i'[unfolded nth_map[OF i']]
          note j_id = j_id[OF i', unfolded j]
          from idx_i' have "fst (idx ?i) = 0" by auto
          note j_id = j_id[unfolded this nth_map[OF i'], unfolded nth_Cons_0]
          with i' show False by auto
        qed
        then show ?thesis unfolding pi split using ns by simp
      next
        case True
        with idx_i have snd: "snd (idx i)" and s: s by auto
        have  "(j,False,True) \<notin> set ?d"
        proof
          assume "(j,False,True) \<in> set ?d"
          from this[unfolded set_conv_nth] obtain k where k: "k < length ?d"
            and j: "(j,False,True) = ?d ! k" by auto
          from j[unfolded nth_map[OF k]] have j: "(j,False,True) = drop (Suc i) p ! k"
            by simp
          let ?i = "Suc i + k"
          from k i have i': "?i < length p" unfolding length_drop by simp
          have "p ! ?i = drop (Suc i) p ! k" 
            using i' by simp
          then have pi': "p ! ?i = (j,False,True)" unfolding j .
          from idx[THEN conjunct1, rule_format, of ?i] i'
          have idx_i': "dms_bool_idx_i idx ?p ?i" by auto
          note idx_i' = idx_i'[unfolded nth_map[OF i']]
          from idx_i' have fst_0: "fst (idx ?i) = 0" by auto
          note idx_i' = idx_i'[unfolded fst_0 length_map nth_Cons_0 pi' fst_conv snd_conv] 
          then have j_id: "\<And> i'. i' < length p \<Longrightarrow> j = fst (?p ! i' ! fst (idx i')) \<Longrightarrow> ?i = i'" by auto
          note j_id = j_id[OF i, unfolded nth_map[OF i] fst nth_Cons_0 pi]
          then show False by simp
        qed      
        then show ?thesis unfolding pi split using s by simp        
      qed
    next
      assume stri
      from idx[THEN conjunct2, rule_format, OF this]
      obtain j where j: "j < n" and neq: "\<And> i. i < length p \<Longrightarrow> (fst (?p ! i ! fst (idx i)), snd (idx i)) \<noteq> (j, False)" by force
      show "\<exists> j \<in> set [0 ..< n]. (j, False, True) \<notin> set p"
      proof (intro bexI)
        show "j \<in> set [0 ..< n]" using j by simp
      next
        show "(j, False, True) \<notin> set p"
        proof
          assume "(j,False,True) \<in> set p"
          from this[unfolded set_conv_nth] obtain i where i: "i < length p"
            and jid: "p ! i = (j,False,True)" by auto
          from idx[THEN conjunct1, rule_format, of i] i
          have idx_i: "dms_bool_idx_i idx ?p i" by auto
          note idx_i = idx_i[unfolded nth_map[OF i]]
          then have "fst (idx i) = 0" by auto
          note neq = neq[OF i, unfolded this nth_map[OF i] nth_Cons_0]
          note neq = neq[unfolded jid fst_conv]
          then have "snd (idx i) = True" by simp
          with idx_i jid show False by auto
        qed
      qed
    qed
  }
  ultimately show ?thesis by blast
qed
    

definition dms_select :: "bool \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> nat"
  where "dms_select stri p \<equiv> snd (hd (sort_key fst (filter (\<lambda> (l,i). l > 1) (zip (map length p) [0 ..< length p]))))"

lemma dms_select: assumes "\<not> (\<forall> jsns \<in> set p. length jsns \<le> 1)"
  shows "dms_select stri p < length p \<and> length (p ! dms_select stri p) > 1"
proof -
  let ?z = "zip (map length p) [0 ..< length p]"
  let ?f = "filter (\<lambda> (l,i). l > 1) ?z"
  let ?s = "sort_key fst ?f"
  {
    from assms obtain as where mem: "as \<in> set p" and len: "\<not> length as <= 1" by blast
    then have len: "length as > 1" by auto
    from mem[unfolded set_conv_nth] obtain k where k: "k < length p" and as: "as = p ! k"
      by blast
    have "(length as, k) \<in> set ?z" unfolding set_zip 
      by (rule, rule exI[of _ k], insert k as, auto)
    with len have "(length as, k) \<in> set ?f" by auto
    then have "(length as, k) \<in> set ?s" unfolding set_sort .
    then have "?s \<noteq> []" by (cases ?s, auto)
  }
  then obtain h t where ht: "?s = h # t" by (cases ?s, auto)
  then obtain i idx where h: "h = (i,idx)" by force
  note ht = ht[unfolded h]
  from ht have res: "dms_select stri p = idx" (is "?res = _") unfolding dms_select_def by simp
  from ht have "(i,idx) \<in> set ?s" by simp
  then have iidx: "(i,idx) \<in> set ?f" unfolding set_sort .
  then have i1: "i > 1" by auto
  from iidx have iidx: "(i,idx) \<in> set ?z" by auto
  then obtain j where j: "j < length p" and zj: "?z ! j = (i,idx)"
    unfolding set_conv_nth by force
  then have jidx: "j = idx" and "i = length (p ! idx)" using nth_zip[of j] by force+
  then have "idx < length p" and "i = length (p ! idx)" using j by auto
  then show ?thesis unfolding res using i1 by auto
qed
  

definition dms_solve_or_select :: "bool \<Rightarrow> nat \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> bool + nat"
  where "dms_solve_or_select stri n p \<equiv> if (\<forall> jsns \<in> set p. length jsns \<le> 1) then Inl (
        if [] \<in> set p then False else dms_decide_singletons stri n (map hd p)) else 
        Inr (dms_select stri p)"

lemma dms_solve_or_select_solve: assumes res: "dms_solve_or_select stri n p = Inl res"
  shows "dms_bool_ex_idx stri n p = res"
proof - 
  let ?res = "dms_bool_ex_idx stri n p"
  note res = res[unfolded dms_solve_or_select_def]
  let ?less = "\<forall> jsns \<in> set p. length jsns \<le> 1"
  have less: ?less
  proof (cases ?less)
    case False 
    then have id: "?less = False" by simp 
    show ?thesis using res unfolding id by simp
  qed
  then have "?less = True" by simp
  note res = res[unfolded this if_True]
  show ?thesis 
  proof (cases "[] \<in> set p")
    case False
    with res have "res = dms_decide_singletons stri n (map hd p)" by simp
    also have "... = ?res" unfolding dms_decide_singletons
    proof (rule arg_cong[where f = "dms_bool_ex_idx stri n"])
      show "map (\<lambda> e. [e]) (map hd p) = p" unfolding map_map o_def
        unfolding map_nth_eq_conv[OF refl]
        unfolding all_set_conv_all_nth[of p "\<lambda> a. [hd a] = a", symmetric]
      proof (intro ballI)
        fix x
        assume x: "x \<in> set p"
        with less have less: "length x \<le> 1" by auto
        from x False have "x \<noteq> []" by auto
        with less show "[hd x] = x" by (cases x, auto)
      qed
    qed
    finally show ?thesis by simp
  next
    case True
    from this[unfolded set_conv_nth] obtain i where i: "i < length p" and empty: "p ! i = []" by auto
    from True res have res: "res = False" by simp
    {
      assume ?res
      from this[unfolded dms_bool_ex_idx_def] obtain idx where idx: "dms_bool_idx idx p stri n"
        by auto
      with i have "dms_bool_idx_i idx p i" by auto
      with empty have False by auto
    }
    then show ?thesis using res by auto
  qed
qed

lemma dms_solve_or_select_select: assumes res: "dms_solve_or_select stri n p = Inr k"
  shows "k < length p \<and> length (p ! k) > 1"
proof - 
  note res = res[unfolded dms_solve_or_select_def]
  let ?less = "\<forall> jsns \<in> set p. length jsns \<le> 1"
  have less: "\<not> ?less"
  proof (cases ?less)
    case True 
    then have id: "?less = True" by simp 
    show ?thesis using res unfolding id by simp
  qed 
  then have "?less = False" by simp
  note res = res[unfolded this if_False]
  then have k: "dms_select stri p = k" by auto
  from dms_select[OF less, of stri] show ?thesis unfolding k .
qed

function dms_solve :: "bool \<Rightarrow> nat \<Rightarrow> (nat \<times> bool \<times> bool) list list \<Rightarrow> bool"
  where "dms_solve stri n p = (case dms_solve_or_select stri n p of 
             Inl res \<Rightarrow> res
           | Inr k \<Rightarrow> (let ksns = p ! k
                       in dms_solve stri n (dms_simplify stri [k] (p [ k := [hd ksns]])) 
                        \<or> dms_solve stri n (dms_simplify stri [k] (p [ k := tl ksns]))))"
  by pat_completeness auto

termination
proof
  show "wf (measure (\<lambda> (stri,n,p). dms_size p))" by simp
next
  fix stri n p b x
  assume select: "dms_solve_or_select stri n p = Inr b" and x: "x = p ! b"
  from dms_solve_or_select_select[OF select] have b: "b < length p" and len: "1 < length (p ! b)" by auto
  from len have less: "length [hd x] < length (p ! b)" by simp
  from upd_conv_take_nth_drop[OF b] have idl: "p[b := [hd x]] = take b p @ [[hd x]] @ drop (Suc b) p" (is "?l' = ?l") by simp
  have "p = p[b := p ! b]" using b by auto
  also have "p[b := p ! b] = take b p @ [p ! b] @ drop (Suc b) p" (is "_ = ?r") 
    using upd_conv_take_nth_drop[OF b, of "p ! b"] by simp
  finally have idr: "dms_size p = dms_size ?r" by simp
  show "((stri,n,dms_simplify stri [b] (p[b := [hd x]])), stri, n, p) \<in> measure (\<lambda> (stri, n,p). dms_size p)" unfolding in_measure split 
  proof -
    have "dms_size (dms_simplify stri [b] ?l') \<le> dms_size ?l'" by (rule dms_simplify_size, insert b, auto)
    also have "... = dms_size (take b p) + dms_size [[hd x]] + dms_size (drop (Suc b) p)"
      unfolding idl unfolding dms_size_def by simp
    also have "... < dms_size (take b p) + dms_size [p ! b] + dms_size (drop (Suc b) p)"
      using less unfolding dms_size_def by simp
    also have "... = dms_size p" unfolding idr unfolding dms_size_def by simp
    finally show "dms_size (dms_simplify stri [b] ?l') < dms_size p" .
  qed
next
  fix stri n p b x
  assume select: "dms_solve_or_select stri n p = Inr b" and x: "x = p ! b"
  from dms_solve_or_select_select[OF select] have b: "b < length p" and len: "1 < length (p ! b)" by auto
  {
    from len obtain h t where pb: "p ! b = h # t" by (cases "p ! b", auto)
    from len[unfolded pb] obtain hh tt where t: "t = hh # tt" by (cases t, auto)
    have "length (tl x) < length (p ! b)" unfolding x pb t by simp
  } note less = this
  from upd_conv_take_nth_drop[OF b] have idl: "p[b := (tl x)] = take b p @ [(tl x)] @ drop (Suc b) p" (is "?l' = ?l") by simp
  have "p = p[b := p ! b]" using b by auto
  also have "p[b := p ! b] = take b p @ [p ! b] @ drop (Suc b) p" (is "_ = ?r") 
    using upd_conv_take_nth_drop[OF b, of "p ! b"] by simp
  finally have idr: "dms_size p = dms_size ?r" by simp
  show "((stri,n,dms_simplify stri [b] (p[b := (tl x)])), stri, n, p) \<in> measure (\<lambda> (stri, n,p). dms_size p)" unfolding in_measure split 
  proof -
    have "dms_size (dms_simplify stri [b] ?l') \<le> dms_size ?l'" by (rule dms_simplify_size, insert b, auto)
    also have "... = dms_size (take b p) + dms_size [(tl x)] + dms_size (drop (Suc b) p)"
      unfolding idl unfolding dms_size_def by simp
    also have "... < dms_size (take b p) + dms_size [p ! b] + dms_size (drop (Suc b) p)"
      using less unfolding dms_size_def by simp
    also have "... = dms_size p" unfolding idr unfolding dms_size_def by simp
    finally show "dms_size (dms_simplify stri [b] ?l') < dms_size p" .
  qed
qed

declare dms_solve.simps[simp del]

lemma dms_solve: "dms_solve stri n p = dms_bool_ex_idx stri n p"
proof (induct stri n p rule: dms_solve.induct)
  case (1 stri n p)
  note simp = dms_solve.simps[of stri n p, unfolded Let_def] 
  note simp[simp]
  show ?case
  proof (cases "dms_solve_or_select stri n p")
    case (Inl x)
    with dms_solve_or_select_solve[OF this]
    show ?thesis by simp
  next
    case (Inr k)
    from dms_solve_or_select_select[OF this]
    have k: "k < length p" and two: "1 < length (p ! k)" by auto
    note 1 = 1[OF Inr refl]
    from two have sub1: "set [hd (p ! k)] \<subseteq> set (p ! k)" by (cases "p ! k", auto)
    from two have sub2: "set (tl (p ! k)) \<subseteq> set (p ! k)" by (cases "p ! k", auto)
    {
      assume solve: "dms_solve stri n p"
      let ?P = "\<lambda> ks. dms_solve stri n (dms_simplify stri [k] (p[ k := ks]))"
      from solve Inr have "?P [hd (p ! k)] \<or> ?P (tl (p ! k))" by simp
      with sub1 sub2 1 obtain pk where sub: "set pk \<subseteq> set (p ! k)" and p: "?P pk"
        and mem: "pk = [hd (p ! k)] \<or> pk = tl (p ! k)" by blast
      let ?p = "p [k := pk]"
      from mem 1 p have "dms_bool_ex_idx stri n (dms_simplify stri [k] ?p)" 
        by blast
      then have bool_idx: "dms_bool_ex_idx stri n ?p" using dms_simplify[of "[k]" ?p] k
        by simp
      have "dms_bool_ex_idx stri n p"
      proof (rule dms_bool_ex_idx_mono[OF _ _ bool_idx])
        show "length ?p = length p" by simp
      next
        fix i
        assume i: "i < length p"
        show "set (?p ! i) \<subseteq> set (p ! i)"
        proof (cases "i = k")
          case False
          then show ?thesis by auto
        next
          case True
          have "set (?p ! i) = set pk" using nth_list_update_eq[OF i] unfolding True by simp
          also have "... \<subseteq> set (p ! k)" using mem two by (cases "p ! k", auto)
          also have "... = set (p ! i)" unfolding True ..
          finally show ?thesis .
        qed
      qed
    }
    moreover
    {
      assume solve: "dms_bool_ex_idx stri n p"
      from solve[unfolded dms_bool_ex_idx_def] obtain idx where idx: "dms_bool_idx idx p stri n" by auto
      from idx have idx_i: "\<And> i. i < length p \<Longrightarrow> dms_bool_idx_i idx p i" by blast
      note idx_k = idx_i[OF k] 
      let ?p = "\<lambda> pk. p [k := pk]"
      let ?Q = "\<lambda> idx' i pk. p ! i ! fst (idx i) = ?p pk ! i ! fst (idx' i) \<and> snd (idx i) = snd (idx' i) \<and> (fst (idx i) < length (p ! i)) = (fst (idx' i) < length (?p pk ! i))"
      have "\<exists> pk idx'. (pk = [hd (p ! k)] \<or> pk = tl (p ! k)) \<and> (\<forall> i. ?Q idx' i pk)" 
      proof (cases "fst (idx k)")
        case 0
        let ?pk = "?p [hd (p ! k)]"
        show ?thesis
        proof (rule exI[of _ "[hd (p ! k)]"], rule exI[of _ idx], intro conjI, simp, intro allI)
          fix i
          have "p ! i ! fst (idx i) = ?pk ! i ! fst (idx i) \<and> (fst (idx i) < length (p ! i)) = (fst (idx i) < length (?pk ! i))" 
          proof (cases "i = k")
            case False 
            then show ?thesis by simp
          next
            case True
            show ?thesis using idx_k 0 unfolding True nth_list_update[OF k] 
              by (cases "p ! k", auto)
          qed
          then show "?Q idx i [hd (p ! k)]" by simp
        qed
      next
        case (Suc l)
        let ?pk = "?p (tl (p ! k))"
        let ?idx = "\<lambda> i. (if i = k then l else fst (idx i), snd (idx i))"
        show ?thesis
        proof (rule exI[of _ "tl (p ! k)"], rule exI[of _ ?idx], intro conjI, simp, intro allI)
          fix i
          have "p ! i ! fst (idx i) = ?pk ! i ! fst (?idx i) \<and> (fst (idx i) < length (p ! i)) = (fst (?idx i) < length (?pk ! i))" 
          proof (cases "i = k")
            case False 
            then show ?thesis by simp
          next
            case True
            show ?thesis using idx_k Suc unfolding True nth_list_update[OF k] 
              by (cases "p ! k", auto)
          qed
          then show "?Q ?idx i (tl (p ! k))" by simp
        qed
      qed
      then obtain pk idx' where mem: "pk = [hd (p ! k)] \<or> pk = tl (p ! k)"
        and Q: "\<And> i. ?Q idx' i pk" by auto
      from Q have fst: "\<And> i. p ! i ! fst (idx i) = ?p pk ! i ! fst (idx' i)"
        and snd: "\<And> i. snd (idx i) = snd (idx' i)"
        and len: "\<And> i. (fst (idx i) < length (p ! i)) = (fst (idx' i) < length (?p pk ! i))" by auto
      let ?pk = "?p pk"
      have "dms_bool_idx idx' ?pk stri n" 
      proof(intro impI conjI, intro allI impI)
        fix i
        assume "i < length ?pk"
        then have i: "i < length p" by simp
        from idx_i[OF i]
        show "dms_bool_idx_i idx' ?pk i" using len snd fst by auto
      next
        assume stri
        from idx[THEN conjunct2, rule_format, OF this]
        obtain j where j: "j < n" and neq: "\<And> i. i < length p \<Longrightarrow> (fst (p ! i ! fst (idx i)), snd (idx i)) \<noteq> (j, False)" by auto
        show "\<exists> j < n. \<forall> i < length ?pk. (fst (?pk ! i ! fst (idx' i)), snd (idx' i)) \<noteq> (j, False)" 
          by (intro exI conjI, rule j, insert neq len fst snd, auto)
      qed
      then have "dms_bool_ex_idx stri n ?pk" unfolding dms_bool_ex_idx_def by blast
      with dms_simplify[of "[k]" ?pk] k have "dms_bool_ex_idx stri n (dms_simplify stri [k] ?pk)" by simp
      with 1 mem have "dms_solve stri n (dms_simplify stri [k] ?pk)" by blast
      with mem have "dms_solve stri n p" using Inr by auto
    }
    ultimately show ?thesis by blast
  qed
qed    
    
  
definition dms_preprocess :: "(nat \<times> bool \<times> bool) list list \<Rightarrow> (nat \<times> bool \<times> bool) list list"
  where "dms_preprocess p \<equiv> map (filter (\<lambda> (c,s,ns). s \<or> ns)) p"

lemma dms_preprocess[simp]: "dms_bool_ex_idx stri n (dms_preprocess p) = dms_bool_ex_idx stri n p" 
proof -
  note d = dms_preprocess_def
  let ?p = "dms_preprocess p"
  have len: "length ?p = length p" unfolding d by simp    
  let ?d = "dms_bool_ex_idx stri n"
  show ?thesis
  proof
    assume p': "?d ?p"
    show "?d p"
    proof (rule dms_bool_ex_idx_mono[OF _ len p'])
      fix i
      assume i: "i < length p"
      show "set (?p ! i) \<subseteq> set (p ! i)" unfolding d using i by auto
    qed
  next
    assume p: "?d p"
    show "?d ?p"
    proof (rule dms_bool_ex_idx_mono_idx[OF _ _ p])
      show "length p = length ?p" unfolding len by simp
    next
      fix i idx
      assume i: "i < length ?p" and idx: "dms_bool_idx_i idx p i"
        and mem: "p ! i ! fst (idx i) \<in> set (p ! i)"
      from i have i: "i < length p" unfolding len by simp
      let ?pif = "p ! i ! fst (idx i)"
      obtain j s ns where pif: "?pif  = (j,s,ns)" by (cases ?pif, auto)
      with idx have sns: "s \<or> ns" by auto
      show "?pif \<in> set (?p ! i)" unfolding d nth_map[OF i] using mem sns
        unfolding pif by auto
    qed
  qed
qed

definition dms_bool_ex_idx_impl where "dms_bool_ex_idx_impl stri n p \<equiv> 
    dms_solve stri n (dms_simplify stri [0 ..< length p] (dms_preprocess p))"

lemma dms_bool_ex_idx_impl[code]: "dms_bool_ex_idx = dms_bool_ex_idx_impl"
proof (intro ext)
  fix stri n p
  show "dms_bool_ex_idx stri n p = dms_bool_ex_idx_impl stri n p"
    unfolding dms_bool_ex_idx_impl_def dms_solve
    unfolding dms_preprocess[of stri n p, symmetric]
    by (rule dms_simplify[symmetric], simp add: dms_preprocess_def)
qed
  
end
