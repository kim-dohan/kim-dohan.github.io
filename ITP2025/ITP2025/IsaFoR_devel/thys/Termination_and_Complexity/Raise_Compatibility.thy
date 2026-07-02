(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Raise_Compatibility
imports
  TA.Tree_Automata
  Matchbounds
begin

context
fixes TA :: "('q,'f \<times> nat)ta"
  and bot :: 'q
  and k :: nat
begin

inductive_set same_base_wit :: "('q list \<times> 'q \<times> (('f \<times> nat,'q)term list))set" where
  same_base_wit: "\<forall> i < k. (((f,as ! i) (pis ! i) \<rightarrow> qs ! i) \<in> ta_rules TA) 
  \<Longrightarrow> \<forall> i < k. length (pis ! i) = n
  \<Longrightarrow> length ps = n
  \<Longrightarrow> length as = k
  \<Longrightarrow> length pis = k
  \<Longrightarrow> length qs = k
  \<Longrightarrow> k > 0
  \<Longrightarrow> \<forall> j < n. ((map (\<lambda> p_is. p_is ! j) pis), ps ! j, ts j) \<in> same_base_wit
  \<Longrightarrow> (((f,max_list as) ps \<rightarrow> q) \<in> ta_rules TA) \<or> (\<not> (\<exists> q. (((f,max_list as) ps \<rightarrow> q) \<in> ta_rules TA)) \<and> q = bot)
  \<Longrightarrow> (qs, q, map (\<lambda> i. Fun (f,as ! i) (map (\<lambda> j. ts j ! i) [0..< n])) [0..< k]) \<in> same_base_wit"

definition same_base :: "('q list \<times> 'q)set" where
  "same_base = {(qs,q) . \<exists> ss. (qs,q,ss) \<in> same_base_wit}"

context
assumes 
    bot: "bot \<notin> ta_states TA"
and det: "ta_det TA"
begin

lemma [simp]: "ta_eps TA = {}" using det[unfolded ta_det_def] by auto

lemma same_base_wit_imp_witness: 
  "(qs,q,ss) \<in> same_base_wit \<Longrightarrow>
  \<exists> s. length ss = length qs 
  \<and> (\<forall> i < length qs. qs ! i \<in> ta_res TA (ss ! i)) 
  \<and> max_raise_list ss = Some s
  \<and> (q \<noteq> bot \<and> q \<in> ta_res TA s \<or> q = bot \<and> ta_res TA s = {})
  \<and> Ball (insert s (set ss)) ground
  \<and> length qs = k"
  (is "_ \<Longrightarrow> \<exists> s. ?prop ss s qs q")
proof (induct rule: same_base_wit.induct)
  case (same_base_wit f as pis qs n ps ts q)
  define P where "P = ?prop"
  note rules = same_base_wit(1)[rule_format]
  note len = same_base_wit(2-7)
  have k: "k > 0" by (rule same_base_wit)
  note IH = same_base_wit(8)[rule_format]
  let ?ps = "\<lambda> j. map (\<lambda>p_is. p_is ! j) pis"
  let ?p = "\<lambda> j. ps ! j"
  {
    fix j
    assume j: "j < n"
    from IH[OF j] have "\<exists> t. ?prop (ts j) t (?ps j) (?p j)" ..
  }
  then have "\<forall> j. \<exists> t. j < n \<longrightarrow> ?prop (ts j) t (?ps j) (?p j)" by metis
  from choice[OF this] obtain t where IH: "\<And> j. j < n \<Longrightarrow> ?prop (ts j) (t j) (?ps j) (?p j)" by blast
  from IH len have ts: "\<And> j. j < n \<Longrightarrow> length (ts j) = k" 
    "\<And> j. j < n \<Longrightarrow> max_raise_list (ts j) = Some (t j)" by auto
  let ?n = "[0 ..< n]"
  let ?k = "[0 ..< k]"
  let ?si = "\<lambda> i. Fun (f,as ! i) (map (\<lambda> j. ts j ! i) ?n)"
  define si where "si = map ?si ?k"
  define s where "s = Fun (f, max_list as) (map t ?n)"
  have "length si = length qs" unfolding si_def len by simp
  moreover
  {
    fix i
    assume "i < length qs"
    with len have i: "i < k" by simp
    have "qs ! i \<in> ta_res TA (si ! i)"
      unfolding si_def
    by (simp add: i, intro exI conjI, 
      rule rules[OF i], insert len len(1)[rule_format, OF i] IH i, auto)
  }
  moreover
  from ts
  have "max_raise_list si = Some s" unfolding si_def s_def using len(3) k
    by (intro max_raise_list_Fun, auto)
  moreover
  {
    fix j
    assume "j < n"
    from IH[OF this]
    have "(ps ! j \<noteq> bot \<and> ps ! j \<in> ta_res TA (t j) \<or> ps ! j = bot \<and> ta_res TA (t j) = {})" by blast
  } note ps = this
  have "q \<noteq> bot \<and> q \<in> ta_res TA s \<or> q = bot \<and> ta_res TA s = {}"
  using same_base_wit(9)
  proof
    assume *: "(f, max_list as) ps \<rightarrow> q \<in> ta_rules TA"
    then have states: "insert q (set ps) \<subseteq> ta_states TA" unfolding ta_states_def r_states_def by fastforce
    with ps bot len(2)[symmetric] have ta_res: "\<And> j. j < n \<Longrightarrow> ps ! j \<in> ta_res TA (t j)"
      using nth_mem by fastforce
    with * len have "q \<in> ta_res TA s" unfolding s_def by auto
    with states bot show ?thesis by auto
  next
    assume *: "\<not> (\<exists>q. (f, max_list as) ps \<rightarrow> q \<in> ta_rules TA) \<and> q = bot"    
    have  "ta_res TA s = {}"
    proof (rule ccontr)
      assume "ta_res TA s \<noteq> {}"
      then obtain q where "q \<in> ta_res TA s" by auto
      from this[unfolded s_def, simplified] obtain ps'
      where rule: "(f, max_list as) ps' \<rightarrow> q \<in> ta_rules TA"
      and len3: "length ps' = n" and ta_res: "\<And> j. j < n \<Longrightarrow> ps' ! j \<in> ta_res TA (t j)" by auto
      from ps ta_res ta_detE[OF det ta_res] have "\<And> j. j < n \<Longrightarrow> ps' ! j = ps ! j" by blast
      with len3 len(2) have "ps' = ps" using nth_equalityI[of ps ps'] by auto
      with rule * show False by blast
    qed
    with * show ?thesis by auto
  qed
  moreover
  have "Ball (insert s (set si)) ground" unfolding s_def si_def
    by (insert IH, fastforce simp: set_conv_nth len)
  ultimately
  show ?case
    by (intro exI[of _ s], auto simp: si_def)
qed

lemma witness_imp_same_base_wit:
  "Ball (insert s (set ss)) ground
  \<Longrightarrow> length ss = length qs
  \<Longrightarrow> \<forall> i < length qs. qs ! i \<in> ta_res TA (ss ! i)
  \<Longrightarrow> max_raise_list ss = Some s
  \<Longrightarrow> q \<noteq> bot \<and> q \<in> ta_res TA s \<or> q = bot \<and> ta_res TA s = {}
  \<Longrightarrow> length qs = k
  \<Longrightarrow> (qs,q,ss) \<in> same_base_wit"
proof (induct ss arbitrary: q qs s rule: wf_induct[OF wf_measure[of "size_list size"]])
  case (1 ss q qs s)
  note IH = 1(1)[rule_format]
  note prems = 1(2-)
  from prems have mr: "max_raise_list ss = Some s" by blast
  from max_raise_list_Some_imp_eq_base[OF mr] have base: "base_term ` set ss = {base_term s}" by auto
  from prems have gs: "ground s" by auto
  then obtain fm SS where s: "s = Fun fm SS" by (cases s, auto)
  then obtain f m where fm: "fm = (f,m)" by (cases fm, auto)
  note s = s[unfolded fm]
  define n where "n = length SS"
  have len: "length qs = k" "length ss = k" "length SS = n" unfolding n_def using prems by auto
  from len(2) base have k: "k > 0" by (cases k, auto)
  let ?prop = "\<lambda> i ai psi tsi.    (f, ai) psi \<rightarrow> qs ! i \<in> ta_rules TA \<and>
    length psi = n \<and>
    (\<forall>j<n. psi ! j \<in> ta_res TA (tsi ! j)) \<and>
    Ball (set tsi) ground \<and>
    length tsi = n \<and>
    map base_term tsi = map base_term SS \<and>
    ss ! i = Fun (f, ai) tsi"
  {
    fix i
    assume i: "i < k"
    with len have mem: "ss ! i \<in> set ss" by auto
    with base s have id: "base_term (ss ! i) = Fun f (map base_term SS)" by auto
    then obtain fi tsi where ssi: "ss ! i = Fun fi tsi" by (cases "ss ! i", auto)
    with id obtain ai where fi: "fi = (f,ai)" and map: "map base_term tsi = map base_term SS"
      by (cases fi, auto simp: len)
    from arg_cong[OF map, of length] have len_n: "length tsi = n" by (simp add: len)
    from prems(1) mem ssi have ground: "Ball (set tsi) ground" by auto
    from prems(3) len i have "qs ! i \<in> ta_res TA (ss ! i)" by auto
    from this[unfolded ssi fi, simplified] len_n
    obtain ps where rule: "(f, ai) ps \<rightarrow> qs ! i \<in> ta_rules TA"
      and ps: "length ps = n" and args: "\<forall>j<n. ps ! j \<in> ta_res TA (tsi ! j)" by auto
    from rule ps args ground len_n ssi[unfolded fi] map
    have "\<exists> ai psi tsi. ?prop i ai psi tsi" by blast
  }
  then have "\<forall> i. \<exists> ai psi tsi. i < k \<longrightarrow> ?prop i ai psi tsi" by blast
  from choice[OF this] obtain ai where "\<forall> i. \<exists> psi tsi. i < k \<longrightarrow> ?prop i (ai i) psi tsi" by blast
  from choice[OF this] obtain psi where "\<forall> i. \<exists> tsi. i < k \<longrightarrow> ?prop i (ai i) (psi i) tsi" by blast
  from choice[OF this] obtain tsi where *: "\<And> i. i < k \<Longrightarrow> ?prop i (ai i) (psi i) (tsi i)" by blast
  from * have 1: "\<forall>i<k. (f, ai i) psi i \<rightarrow> qs ! i \<in> ta_rules TA" by auto
  from * have 2: "\<forall>i<k. length (psi i) = n" by auto
  let ?k = "[0 ..< k]"
  let ?n = "[0 ..< n]"
  let ?as = "map ai ?k"
  let ?m = "max_list ?as"
  let ?ps = "map psi ?k"
  let ?tsi = "\<lambda> j. map (\<lambda> i. tsi i ! j) ?k"
  {
    fix j
    assume j: "j < n"
    {
      fix i 
      assume i: "i < k"
      from *[OF i] have map: "map base_term (tsi i) = map base_term SS" and 
        len_tsi: "length (tsi i) = n" by auto
      from arg_cong[OF map, of "\<lambda> xs. xs ! j"]
      have "base_term (?tsi j ! i) = base_term (SS ! j)" using len i j len_tsi by auto
    } note base = this
    with k have "set (map base_term (?tsi j)) = {base_term (SS ! j)}"
      by (auto simp: set_conv_nth o_def intro: exI[of _ 0])
    then have "base_term ` (set (?tsi j)) = {base_term (SS ! j)}" by fastforce
    from max_raise_list_base_Some[OF this] have "\<exists> T. max_raise_list (?tsi j) = Some T \<and> base_term T = base_term (SS ! j)" by auto
  }
  then have "\<forall> j. \<exists> T. j < n \<longrightarrow> max_raise_list (?tsi j) = Some T \<and> base_term T = base_term (SS ! j)" by auto
  from choice[OF this] obtain T where T: "\<And> j. j < n \<Longrightarrow> max_raise_list (?tsi j) = Some (T j)"  and
    T_base: "\<And> j. j < n \<Longrightarrow> base_term (T j) = base_term (SS ! j)" by auto
  {
    fix j
    assume j: "j < n"
    from gs[unfolded s] j len have "ground (SS ! j)" by auto
    with T_base[OF j] ground_map_funs_term have "ground (T j)" by metis
  } note gT = this
  let ?reach = "\<lambda> j q. q \<in> ta_res TA (T j)"
  define pss where "pss = (\<lambda> j. if (\<exists> q. ?reach j q) then (SOME q. ?reach j q) else bot)"
  {
    fix j
    assume j: "j < n"
    have "pss j \<noteq> bot \<and> pss j \<in> ta_res TA (T j) \<or> pss j = bot \<and> ta_res TA (T j) = {}"
    proof (cases "\<exists> q. ?reach j q")
      case True
      then have "pss j = (SOME q. ?reach j q)" unfolding pss_def by auto
      with someI_ex[OF True] have r: "?reach j (pss j)" by simp
      with ta_res_states[OF gT[OF j], of TA] bot have "pss j \<noteq> bot" by auto
      with r show ?thesis by auto
    qed (auto simp: pss_def)
  } note pss = this
  let ?pss = "map pss ?n"
  let ?TS = "map T ?n"
  have ss: "ss = map (\<lambda>i. Fun (f, ?as ! i) (map (\<lambda>j. ?tsi j ! i) ?n)) ?k"
    by (intro nth_equalityI, auto simp: len * intro: nth_equalityI)
  show ?case unfolding ss
  proof (rule same_base_wit[of f ?as ?ps _ n ?pss], (auto simp: 1 2 k len)[7], intro allI impI)
    fix j
    assume j: "j < n"
    show "(map (\<lambda>p_is. p_is ! j) ?ps, ?pss ! j, ?tsi j) \<in> same_base_wit"
    proof (rule IH[of "?tsi j" "T j"], unfold length_map length_upt diff_zero)
      have "size_list size (?tsi j) < size_list size ss"
      proof (rule size_list_pointwise3, unfold length_map length_upt diff_zero len)
        show "?tsi j \<noteq> []" using k by auto
        fix i
        assume i: "i < k"
        show "size (?tsi j ! i) < size (ss ! i)"
          using *[OF i] i j by (simp add: size_simps)
      qed simp
      then show "(?tsi j, ss) \<in> measure (size_list size)" by simp
    next
      fix i
      assume i: "i < k"
      show "map (\<lambda>p_is. p_is ! j) ?ps ! i \<in> ta_res TA (?tsi j ! i)"
        using *[OF i] i j by (auto simp: len o_def)
    next
      fix t
      assume "t \<in> insert (T j) (set (?tsi j))"
      then have "t = T j \<or> t \<in> set (?tsi j)" by auto
      then show "ground t"
      proof
        assume "t \<in> set (?tsi j)"
        then obtain i where "t = tsi i ! j" and i: "i < k" by auto
        then show ?thesis using *[OF i] j by auto
      next
        assume "t = T j"
        with gT[OF j] show ?thesis by simp
      qed
    qed (auto simp: T[OF j] pss[OF j] j)
  next  
    have "max_raise_list ss = Some (Fun (f,?m) ?TS)" unfolding ss
      by (rule HOL.trans[OF _ max_raise_list_Fun[of n ?tsi, OF _ _ _ _ k]], auto simp: T)
    with prems(4) have s: "s = Fun (f, ?m) ?TS" by simp
    from prems(5)
    show "(f, ?m) ?pss \<rightarrow> q \<in> ta_rules TA \<or>
    \<not> (\<exists>q. (f, ?m) ?pss \<rightarrow> q \<in> ta_rules TA) \<and> q = bot"
    proof
      assume "q \<noteq> bot \<and> q \<in> ta_res TA s"
      from this[unfolded s, simplified]
      obtain qs where rule: "(f, ?m) qs \<rightarrow> q \<in> ta_rules TA"
        and len_qs: "length qs = n" and res: "\<And> j. j<n \<Longrightarrow> qs ! j \<in> ta_res TA (T j)" by auto
      {
        fix j
        assume j: "j < n"
        from res[OF j] pss[OF j] have "pss j \<in> ta_res TA (T j)" by auto
        from ta_detE[OF det res[OF j] this] have "qs ! j = pss j" by auto
      }
      then have "qs = ?pss"
        by (intro nth_equalityI, auto simp: len_qs)
      with rule show ?thesis by auto
    next
      assume "q = bot \<and> ta_res TA s = {}"
      then have qb: "q = bot" and res: "ta_res TA s = {}" by auto
      show ?thesis
      proof (rule disjI2, rule conjI[OF _ qb], rule)
        assume "\<exists>q. (f, ?m) ?pss \<rightarrow> q \<in> ta_rules TA"
        then obtain q' where rule: "(f, ?m) ?pss \<rightarrow> q' \<in> ta_rules TA" by auto
        then have "set ?pss \<subseteq> ta_states TA" unfolding ta_states_def r_states_def by auto
        with bot have bot: "bot \<notin> set ?pss" by auto
        {
          fix j
          assume j: "j < n"
          from pss[OF j] bot j have "pss j \<in> ta_res TA (T j)" by auto
        }
        then have "q' : ta_res TA s" unfolding s using rule
          by auto
        with res
        show False by auto
      qed
    qed
  qed 
qed

lemma same_base_wit_characterization: 
  shows "(qs,q,ss) \<in> same_base_wit \<longleftrightarrow> (\<exists> s. Ball (insert s (set ss)) ground
    \<and> length ss = length qs
    \<and> (\<forall> i < length qs. qs ! i \<in> ta_res TA (ss ! i))
    \<and> max_raise_list ss = Some s
    \<and> (q \<noteq> bot \<and> q \<in> ta_res TA s \<or> q = bot \<and> ta_res TA s = {})
    \<and> length qs = k)"
  using same_base_wit_imp_witness[of qs q ss] witness_imp_same_base_wit[of _ ss qs q]
  by blast

lemma same_base_characterization: 
  shows "(qs,q) \<in> same_base \<longleftrightarrow> (\<exists> s ss. Ball (insert s (set ss)) ground
    \<and> length ss = length qs
    \<and> (\<forall> i < length qs. qs ! i \<in> ta_res TA (ss ! i))
    \<and> max_raise_list ss = Some s
    \<and> (q \<noteq> bot \<and> q \<in> ta_res TA s \<or> q = bot \<and> ta_res TA s = {}))
    \<and> length qs = k"
  unfolding same_base_def same_base_wit_characterization by blast

lemma same_base_singleton: assumes trim: "ta_trim TA" and q: "q \<in> ta_states TA"
  shows "([q],p) \<in> same_base \<longleftrightarrow> (k = 1 \<and> p = q)"
proof
  assume *: "k = 1 \<and> p = q"  
  from trim[unfolded ta_trim_def] q have "q \<in> ta_reachable TA" by auto
  from this[unfolded ta_reachable_def] obtain s where s: "ground s" and res: "q \<in> ta_res TA s" by auto
  have "([q],q,[s]) \<in> same_base_wit"
    by (rule witness_imp_same_base_wit[of s "[s]"], insert q bot *, auto simp: s res)
  with *[THEN conjunct2]  show "([q],p) \<in> same_base" by (auto simp: same_base_def)
next
  assume "([q],p) \<in> same_base"
  from this[unfolded same_base_def] obtain ss
  where "([q],p,ss) \<in> same_base_wit" by auto
  from same_base_wit_imp_witness[OF this] obtain s
  where len: "length ss = Suc 0" and
        res: "(q \<in> ta_res TA (ss ! 0))" and
        mr: "max_raise_list ss = Some s" and
        res2: "(p \<noteq> bot \<and> p \<in> ta_res TA s \<or> p = bot \<and> ta_res TA s = {})" and
        k: "k = 1"
     by auto
  from len obtain s' where "ss = [s']" by (cases ss, auto)
  with mr have ss: "ss = [s]" by auto
  with res have res: "q \<in> ta_res TA s" by auto
  with res2 have res2: "p \<in> ta_res TA s" by auto
  from ta_detE[OF det res res2] k
  show "k = 1 \<and> p = q" by simp
qed

end

end

end
