(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Raise_Consistency
imports 
  TA.Tree_Automata
  Matchbounds
begin

definition state_raise_consistent :: "('q,'f \<times> nat)ta \<Rightarrow> 'q rel \<Rightarrow> bool" where
  "state_raise_consistent TA rel \<equiv> (\<forall> f qs q q' i j.  
  ((f,i) qs \<rightarrow> q) \<in> ta_rules TA \<longrightarrow>
  ((f,j) qs \<rightarrow> q') \<in> ta_rules TA \<longrightarrow> 
  i < j \<longrightarrow>
  (q,q') \<in> rel)"

context
  fixes TA :: "('q,'f \<times> nat)ta"
  and rel :: "'q rel"
  assumes det: "ta_det TA"
  and coh: "state_coherent TA rel"
  and raise: "state_raise_consistent TA rel"
begin

lemma [simp]: "ta_eps TA = {}" using det[unfolded ta_det_def] by simp

lemma state_raise_max_raise:
  assumes base: "base_term t1 = base_term t2"
  and 1: "q1 \<in> ta_res TA t1"
  and 2: "q2 \<in> ta_res TA t2"
  shows "\<exists> q. (q1,q) \<in> rel^* \<and> (q2,q) \<in> rel^* \<and> q \<in> ta_res TA (the (max_raise (t1,t2)))"
  using base 1 2
proof (induct t1 arbitrary: t2 q1 q2)
  case (Var x t2 q1 q2)
  then show ?case by (cases t2, auto)
next
  case (Fun fi ts1 t2 q1 q2)
  from Fun(2) obtain fj ts2 where t2: "t2 = Fun fj ts2" by (cases t2, auto)
  obtain f i where fi: "fi = (f,i)" by force
  from Fun(2) t2 fi obtain j where fj: "fj = (f,j)" by (cases fj, auto)
  let ?n = "length ts2"
  note Fun = Fun[unfolded t2 fj fi]
  from Fun(2) have "map base_term ts1 = map base_term ts2" by simp
  from map_nth_conv[OF this] arg_cong[OF this, of length] have len: "length ts1 = length ts2" and
    base: "\<And> i. i < ?n \<Longrightarrow> base_term (ts1 ! i) = base_term (ts2 ! i)" by auto
  let ?R = "ta_rules TA"
  let ?res = "ta_res TA"
  let ?rel = "rel^*"
  let ?t = "\<lambda> k. the (max_raise (ts1 ! k, ts2 ! k))"
  from Fun(3) len obtain qs1 where 
    r1: "((f, i) qs1 \<rightarrow> q1) \<in> ?R" and l1: "length qs1 = ?n" and rec1: "\<And> i. i < ?n \<Longrightarrow> qs1 ! i \<in> ?res (ts1 ! i)" by auto
  from Fun(4) obtain qs2 where 
    r2: "((f, j) qs2 \<rightarrow> q2) \<in> ?R" and l2: "length qs2 = ?n" and rec2: "\<And> i. i < ?n \<Longrightarrow> qs2 ! i \<in> ?res (ts2 ! i)" by auto
  {
    fix k
    assume k: "k < ?n"
    with len have mem: "ts1 ! k \<in> set ts1" by auto
    from base[OF k] have base: "base_term (ts1 ! k) = base_term (ts2 ! k)" .
    note Fun(1)[OF mem base rec1[OF k] rec2[OF k]]
  }
  then have "\<forall> k. \<exists> q. k < ?n \<longrightarrow> (qs1 ! k, q) \<in> ?rel \<and> (qs2 ! k, q) \<in> ?rel \<and> q \<in> ?res (?t k)" by blast
  from choice[OF this] obtain q where q: "\<And> k. k < ?n \<Longrightarrow> (qs1 ! k, q k) \<in> ?rel \<and> (qs2 ! k, q k) \<in> ?rel \<and> q k \<in> ?res (?t k)" by blast
  let ?qs = "map q [0 ..< ?n]"
  have "\<exists>q'. ((f, i) ?qs \<rightarrow> q') \<in> ?R \<and> (q1, q') \<in> ?rel"
    by (rule state_coherent_args[OF coh r1], insert l1 q, auto)
  then obtain q1' where r1: "((f, i) ?qs \<rightarrow> q1') \<in> ?R" and rel1: "(q1, q1') \<in> ?rel" by blast
  have "\<exists>q'. ((f, j) ?qs \<rightarrow> q') \<in> ?R \<and> (q2, q') \<in> ?rel"
    by (rule state_coherent_args[OF coh r2], insert l2 q, auto)
  then obtain q2' where r2: "((f, j) ?qs \<rightarrow> q2') \<in> ?R" and rel2: "(q2, q2') \<in> ?rel" by blast
  note raise = raise[unfolded state_raise_consistent_def, rule_format]
  have "\<exists> q'. ((f, max i j) ?qs \<rightarrow> q') \<in> ?R \<and> (q1',q') \<in> ?rel \<and> (q2',q') \<in> ?rel"
  proof (cases "i < j")
    case True
    with raise[OF r1 r2 True] rel1 rel2 r2
    show ?thesis 
      by (intro exI[of _ q2'], auto simp: max_def)
  next
    case False
    then have "j < i \<or> j = i" by arith
    then show ?thesis
    proof
      assume ji: "j < i"
      with raise[OF r2 r1 ji] rel1 rel2 r1
      show ?thesis 
        by (intro exI[of _ q1'], auto simp: max_def)
    next
      assume ji: "j = i"
      with det[unfolded ta_det_def] r1 r2 have "q1' = q2'" by simp
      with ji r1 rel1 rel2 
      show ?thesis 
        by (intro exI[of _ q1'], auto)
    qed
  qed
  then obtain q' where rule: "((f, max i j) ?qs \<rightarrow> q') \<in> ?R" and rel: "(q1',q') \<in> ?rel" "(q2',q') \<in> ?rel" by blast
  from rel rel1 rel2 have rel: "(q1,q') \<in> ?rel" "(q2,q') \<in> ?rel" by auto
  from max_raise_base_Some[OF Fun(2)] obtain u where "max_raise (Fun (f, i) ts1, Fun (f, j) ts2) = Some u" by blast
  then have "\<forall>x\<in>set (zip ts1 ts2). \<exists>y. max_raise x = Some y"
    by (simp add: len mapM_map split: if_splits)  
  then have id: "the (max_raise (Fun (f, i) ts1, Fun (f, j) ts2)) = Fun (f, max i j) (map ?t [0 ..< ?n])" using len
    by (auto simp: mapM_map, intro nth_equalityI, auto)
  show ?case unfolding t2 fi fj id
    by (intro conjI exI, rule rel(1), rule rel(2), insert q rule, auto)
qed 

(* Lemma 35 *)
lemma state_raise_max_raise_list: 
  assumes base: "base_term ` set ts = {b}"
  and len: "length qs = length ts"
  and res: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)"
  shows "\<exists> q. q \<in> ta_res TA (the (max_raise_list ts)) \<and> base_term (the (max_raise_list ts)) = b \<and> (\<forall> i < length ts. (qs ! i, q) \<in> rel^*)"
proof -
  from base obtain t tts where ts: "ts = t # tts" by (cases ts, auto)
  with max_raise_list_base_Some[OF base] obtain u where max: "max_raise_list (t # tts) = Some u" and bu: "base_term u = b" by auto
  show ?thesis unfolding ts max option.sel using len max base res unfolding ts length_Cons
  proof (induct tts arbitrary: t qs)
    case Nil
    then show ?case by (cases qs, auto)
  next
    case (Cons t2 ts t1 qqs)
    from Cons(2) obtain q1 qqs' where qqs: "qqs = q1 # qqs'" and len: "length qqs' = Suc (length ts)" by (cases qqs, auto)
    from len obtain q2 qs where qqs': "qqs' = q2 # qs" by (cases qqs', auto)
    note qqs = qqs[unfolded qqs']
    note IH = Cons(1)
    note Cons = Cons[unfolded qqs]
    note res = Cons(5)
    from Cons(4) have b1: "base_term t1 = b" and b2: "base_term t2 = b" and b: "base_term t1 = base_term t2" by auto
    from Cons(3) obtain t12 where mr: "max_raise (t1,t2) = Some t12" and rec: "max_raise_list (t12 # ts) = Some u" by (auto split: bind_splits)
    let ?ts = "t12 # ts"
    from max_raise_base_Some[OF b] mr have b12: "base_term t12 = b" using b2 by auto
    from res[of 0] res[of 1] have q1: "q1 \<in> ta_res TA t1" and q2: "q2 \<in> ta_res TA t2" by simp_all
    from state_raise_max_raise[OF b q1 q2, unfolded mr] 
    obtain q12 where q1: "(q1, q12) \<in> rel\<^sup>*" and q2: "(q2, q12) \<in> rel\<^sup>*" and res: "q12 \<in> ta_res TA t12" by auto
    let ?qs = "q12 # qs"
    from len[unfolded qqs'] have len: "length ?qs = Suc (length ts)" by simp
    from Cons(4) b12 have base: "base_term ` set ?ts = {b}" by auto
    have "\<exists>q. q \<in> ta_res TA u \<and> base_term u = b \<and> (\<forall>i<Suc (length ts). (?qs ! i, q) \<in> rel\<^sup>*)"
    proof (rule IH[OF len rec base])
      fix i
      assume "i < Suc (length ts)"
      then show "?qs ! i \<in> ta_res TA (?ts ! i)" using res Cons(5)[of "Suc i"] by (cases i, auto)
    qed
    then obtain q where qu: "q \<in> ta_res TA u" and b: "base_term u = b" and rel: "\<And> i. i < Suc (length ts) \<Longrightarrow> (?qs ! i, q) \<in> rel^*" by auto
    from rel[of 0] have "(q12, q) \<in> rel^*" by simp
    with q1 q2 have q12: "(q1, q) \<in> rel^*" "(q2, q) \<in> rel^*" by auto
    show ?case unfolding qqs
    proof (rule exI[of _ q], rule conjI[OF qu], unfold all_Suc_conv, intro allI conjI impI)
      fix i
      assume "i < length (t2 # ts)" then show "((q1 # q2 # qs) ! Suc i, q) \<in> rel\<^sup>*"
        using rel[of i] q12 by (cases i, auto)
    qed (insert q12 b, auto)
  qed
qed  

context
  fixes R :: "('f \<times> nat,'v)trs"
  assumes comp: "state_compatible TA rel R"
  and wf_trs: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin
(* Lemma 36 *)
lemma state_raise_compatible_res: 
  assumes step: "(s, t) \<in> raise_step R"
  and ground: "ground s"
  and "p \<in> ta_res TA (adapt_vars s)"
  shows "\<exists> p'. p' \<in> ta_res TA (adapt_vars t) \<and> (p,p') \<in> rel^*" 
  using assms
proof (induct)
  case (raise_step l r C xs ss \<sigma> D)
  note av = adapt_vars_def
  let ?D = "adapt_vars_ctxt D :: (('f\<times>nat,'q)ctxt)"
  let ?adapt_vars = "adapt_vars :: ('f\<times>nat,'v)term \<Rightarrow> ('f\<times>nat,'q)term"
  from ta_res_ctxt_decompose[OF raise_step(7)[unfolded av map_vars_term_ctxt_commute, folded av]]
  obtain q where q: "q \<in> ta_res TA (?adapt_vars (fill_holes C ss))" and p: "p \<in> ta_res TA ?D \<langle>Var q\<rangle>"
    by (auto simp add: adapt_vars_ctxt_def)
  note sigma = raise_step(5)
  let ?\<sigma> = "\<lambda> x. ?adapt_vars (\<sigma> x)"
  have lr: "(l,r) \<in> R" by fact
  have split: "split_vars l = (C, xs)" by fact
  from split_vars_ground[OF split] split_vars_num_holes[of l, unfolded split] 
  have g: "ground_mctxt C" and nh: "num_holes C = length xs" by auto
  from split_vars_vars_term[of l, unfolded split] have vl: "vars_term l = set xs" by auto
  let ?C = "map_vars_mctxt (\<lambda>_. undefined) C"
  let ?n = "length xs"
  have len2: "length ss = ?n" by fact
  from nh len2 have nh2: "num_holes C = length ss" by simp
  from q[unfolded av map_vars_term_fill_holes[OF nh2], folded av]
  have "q \<in> ta_res TA (fill_holes ?C (map ?adapt_vars ss))" by simp
  from ta_res_fill_holes[OF this, unfolded length_map num_holes_map_vars_mctxt, OF nh2, unfolded len2]
    obtain qs where len: "length qs = ?n"
    and ss: "\<And> i. i < ?n \<Longrightarrow> qs ! i \<in> ta_res TA (map ?adapt_vars ss ! i)"
    and res: "q \<in> ta_res TA (fill_holes ?C (map Var qs))" by auto
    define i_is where "i_is = (\<lambda> i. [j . j <- [0 ..< ?n], xs ! j = xs ! i])"
    define i_ss where "i_ss = (\<lambda> i. map (\<lambda> j. ss ! j) (i_is i))"
    define i_ts where "i_ts = (\<lambda> i. map ?adapt_vars (i_ss i))"
    define i_qs where "i_qs = (\<lambda> i. map (\<lambda> j. qs ! j) (i_is i))"
  from raise_step(6) have "ground (fill_holes C ss)" by simp
  from this[unfolded ground_fill_holes[OF nh2]] have gss: "\<And> s. s \<in> set ss \<Longrightarrow> ground s" by auto
  {
    fix i
    assume i: "i < ?n"
    define ii where "ii = hd (i_is i)"
    have "i \<in> set (i_is i)" using i unfolding i_is_def by auto
    then have ii: "ii \<in> set (i_is i)" unfolding ii_def by (cases "i_is i", auto)
    then have ii2: "ii < ?n" and iix: "xs ! ii = xs ! i" unfolding i_is_def by auto
    let ?ts = "map ?adapt_vars (i_ss i)"
    let ?qs = "i_qs i"
    let ?b = "base_term (?adapt_vars (ss ! ii))"
    have "length ?qs = length ?ts" unfolding i_qs_def i_ss_def by simp
    note merge = state_raise_max_raise_list[of ?ts ?b ?qs, OF _ this]
    have base: "base_term ` set ?ts = {?b}"
    proof
      show "{?b} \<subseteq> base_term ` set ?ts" using ii unfolding i_ss_def by auto 
      show "base_term ` set ?ts \<subseteq> {?b}"
      proof
        fix b
        assume "b \<in> base_term ` set ?ts"
        then obtain si where b: "b = base_term (?adapt_vars si)" 
        and si: "si \<in> set (i_ss i)" by auto
        from si[unfolded i_ss_def i_is_def] obtain j where 
          j: "j < ?n" and id: "xs ! j = xs ! i" and si: "si = ss ! j" by auto
        from raise_step(4)[OF j i id] have "base_term (ss ! j) = base_term (ss ! i)" by simp
        with raise_step(4)[OF ii2 i iix] have base: "base_term (ss ! j) = base_term (ss ! ii)" by simp
        then have "b = ?b" unfolding b si av
          by (rule map_funs_term_eq_imp_map_funs_term_map_vars_term_eq)
        then show "b \<in> {?b}" by simp
      qed
    qed
    note merge = merge[OF base]
    {
      fix j
      assume "j < length ?ts" 
      then have j: "i_is i ! j \<in> set (i_is i)" "j < length (i_is i)" unfolding i_ss_def by auto
      let ?i = "i_is i ! j"
      from j have i: "?i < ?n" unfolding i_is_def by simp
      have qid: "i_qs i ! j = qs ! ?i" unfolding i_qs_def using j by simp
      have sid: "?ts ! j = map ?adapt_vars ss ! ?i" unfolding i_ss_def using len2 i j by simp          
      have "i_qs i ! j \<in> ta_res TA (map ?adapt_vars (i_ss i) ! j)"
        unfolding sid qid by (rule ss[OF i])          
    }
    note merge = merge[OF this]
    from this obtain q where q: "q \<in> ta_res TA (the (max_raise_list (i_ts i)))"
      and b: "base_term (the (max_raise_list (i_ts i))) = base_term (?adapt_vars (ss ! ii))"
      and rel: "(\<forall> j <length (i_is i). (i_qs i ! j, q) \<in> rel\<^sup>*)" unfolding i_ts_def i_ss_def by simp blast
    have base: "\<exists> b. base_term ` set (map ?adapt_vars (i_ss i)) = {b}" unfolding base by blast
    from ii2 len2 have "ss ! ii \<in> set ss" by simp
    from gss[OF this] have "ground (base_term (?adapt_vars (ss ! ii)))" by simp
    then have "ground (the (max_raise_list (i_ts i)))" unfolding b[symmetric] by simp
    with q rel 
    have "\<exists>q. q \<in> ta_res TA (the (max_raise_list (i_ts i))) \<and>
      ground (the (max_raise_list (i_ts i))) \<and>
      (\<forall> j <length (i_is i). (i_qs i ! j, q) \<in> rel\<^sup>*)" by blast
    note this base
  } note * = this
  define qsf where "qsf = (\<lambda> i. SOME q. q \<in> ta_res TA (the (max_raise_list (i_ts i))) \<and>
      ground (the (max_raise_list (i_ts i))) \<and>
      (\<forall> j <length (i_is i). (i_qs i ! j, q) \<in> rel\<^sup>*))"
  have merge: "\<And> i. i < ?n \<Longrightarrow> (qsf i) \<in> ta_res TA (the (max_raise_list (i_ts i))) \<and>
      ground (the (max_raise_list (i_ts i))) \<and>
      (\<forall> j <length (i_is i). (i_qs i ! j, qsf i) \<in> rel\<^sup>*)"
    unfolding qsf_def by (rule someI_ex, rule *(1))      
  define qs' where "qs' = map qsf [0 ..< ?n]"
  {
    fix i j
    assume i: "i < ?n" and j: "j < ?n" and id: "xs ! i = xs ! j"
    then have [simp]: "i_is i = i_is j" unfolding i_is_def by auto
    then have [simp]: "i_ss i = i_ss j" "i_ts i = i_ts j" "i_qs i = i_qs j" unfolding i_ss_def i_ts_def i_qs_def by auto
    then have "qsf i = qsf j" unfolding qsf_def by simp
    with i j have "qs' ! i = qs' ! j" unfolding qs'_def by simp
  } note qs'_inject = this
  have len3: "length qs' = ?n" unfolding qs'_def by simp
  {
    fix i
    assume i: "i < ?n"        
    then have "i \<in> set (i_is i)" unfolding i_is_def by simp
    then obtain j where j: "j < length (i_is i)" and i': "i_is i ! j = i"
      unfolding set_conv_nth by auto
    from merge[OF i] i j have res: "qs' ! i \<in> ta_res TA (the (max_raise_list (i_ts i)))"
      and rel: "(i_qs i ! j, qs' ! i) \<in> rel\<^sup>*"
      and ground: "ground (the (max_raise_list (i_ts i)))" unfolding qs'_def by auto
    have "i_qs i ! j = qs ! i" unfolding i_qs_def using i j i' by simp
    note rel = rel[unfolded this]
    define x where "x = xs ! i"  
    have i_ss: "i_ss i = map fst [(si, xi)\<leftarrow>zip ss xs . xi = xs ! i]"
      unfolding i_ss_def i_is_def x_def[symmetric]
      using len2
    proof (induct ss xs rule: list_induct2)
      case (Cons s ss y ys)
      let ?lhs = "\<lambda> ss ys. map fst [a\<leftarrow>zip ss ys . case a of (si, xi) \<Rightarrow> xi = x]"
      let ?rhs = "\<lambda> ss ys. map ((!) ss) (concat (map (\<lambda>j. if ys ! j = x then [j] else []) [0..<length ys]))"
      define uys where "uys = [0..<length ys]"
      have "?lhs (s # ss) (y # ys)  
        = (if y = x then s # ?lhs ss ys else ?lhs ss ys)" by simp
      also have "?lhs ss ys = ?rhs ss ys" unfolding Cons ..
      also have "(if y = x then s # ?rhs ss ys else ?rhs ss ys) = ?rhs (s # ss) (y # ys)"
        unfolding length_Cons map_upt_Suc by (simp add: map_concat o_def uys_def[symmetric], induct uys, auto)
      finally show ?case by simp
    qed simp
    from i have xs: "(xs ! i \<in> vars_term l) = True" using vl by auto
    from *(2)[OF i] obtain b where base: "base_term ` set (map ?adapt_vars (i_ss i)) = {b}" by blast
    define sss where "sss = map fst [(si, xi)\<leftarrow>zip ss xs . xi = xs ! i]"
    {
      fix s
      assume s: "s \<in> set sss"
      from this[unfolded sss_def] obtain x where "(s,x) \<in> set (zip ss xs)" by auto
      from gss[OF zip_fst[OF this]] have "ground s" by simp
    } note gsss = this
    then have sssg: "Ball (set sss) ground" by auto
    from  base[unfolded i_ss, folded sss_def] have base: "base_term ` set (map ?adapt_vars sss) = {b}" .
    from max_raise_list_base_Some[OF this] obtain u where
      mr: "max_raise_list (map ?adapt_vars sss) = Some u" by blast        
    from base have "set sss \<noteq> {}" by auto
    from max_raise_list_map_vars[OF sssg mr[unfolded av] this] obtain v where
      mr': "max_raise_list sss = Some v" and u: "u = ?adapt_vars v" unfolding av by auto
    have "the (max_raise_list (i_ts i)) = adapt_vars (\<sigma> (xs ! i))"
      unfolding sigma i_ts_def xs if_True i_ss sss_def[symmetric]
      unfolding mr mr' u by simp
    note res[unfolded this] rel ground[unfolded this] i_ss
  } note merge = this
  note this ss res 
  from state_coherent_fill_holes_rel[OF coh res merge(2), unfolded len len3]
  obtain q' where rel: "(q, q') \<in> rel\<^sup>*" and res: "q' \<in> ta_res TA (fill_holes ?C (map Var qs'))"
    using nh by auto
  define \<delta> where "\<delta> = (\<lambda> x. qs' ! (SOME i. i < ?n \<and> xs ! i = x))"
  have "fill_holes ?C (map Var qs') = l \<cdot> (Var o \<delta>)"
  proof (rule eqfE(1)[OF split_vars_into_subst_map_vars_term [OF split], symmetric], unfold o_def)
    fix i
    assume i: "i < ?n" 
    define j where "j = (SOME j. j < ?n \<and> xs ! j = xs ! i)"
    have delta: "\<delta> (xs ! i) = qs' ! j" unfolding j_def \<delta>_def by simp
    from i have "\<exists> j. j < ?n \<and> xs ! j = xs ! i" by auto
    from someI_ex[OF this, folded j_def] have "j < ?n" and "xs ! i = xs ! j" by auto
    from qs'_inject[OF i this]
    have "\<delta> (xs ! i) = qs' ! i" unfolding delta by simp
    then show "Var (\<delta> (xs ! i)) = map Var qs' ! i" using len3 i by simp
  qed (simp add: len3)
  from res[unfolded this] have res: "q' \<in> ta_res TA (map_vars_term \<delta> l)"
    unfolding map_vars_term_as_subst o_def .
  have delta_states: "\<delta> ` vars_term l \<subseteq> ta_rhs_states TA" 
  proof 
    fix q
    assume "q \<in> \<delta> ` vars_term l"
    then obtain x where x: "x \<in> vars_term l" and q: "q = \<delta> x" by auto
    define i where "i = (SOME i. i < ?n \<and> xs ! i = x)"
    from x[unfolded vl set_conv_nth] have "\<exists> i. i < ?n \<and> xs ! i = x" by auto
    from someI_ex[OF this, folded i_def] have i: "i < ?n" and x: "xs ! i = x" by auto
    from q[unfolded \<delta>_def, folded i_def] have "q = qs' ! i" by auto
    with merge[OF i] have q: "q \<in> ta_res TA (?\<sigma> (xs ! i))" 
      and ground: "ground (?\<sigma> (xs ! i))" by simp_all
    then have "is_Fun (?\<sigma> (xs ! i))"
      by (metis ground.simps(1) is_VarE)
    from ta_rhs_states_res[OF this, of TA] q show "q \<in> ta_rhs_states TA" by auto
  qed
  from ta_syms_res[OF res] have "funas_term l \<subseteq> ta_syms TA" unfolding funas_term_subst by auto
  from comp[unfolded state_compatible_def, rule_format, OF lr this]
  have "rule_state_compatible TA rel (l,r)" .
  from this[unfolded rule_state_compatible_def] delta_states
  have "ta_res TA (map_vars_term \<delta> l) \<subseteq> rel\<inverse> `` ta_res TA (map_vars_term \<delta> r)" by auto
  with res obtain q'' where rel2: "(q',q'') \<in> rel" and res: "q'' \<in> ta_res TA (map_vars_term \<delta> r)" by auto
  from rel rel2 have rel: "(q,q'') \<in> rel^*" by auto
  have res: "q'' \<in> ta_res TA (r \<cdot> ?\<sigma>)"
  proof (rule ta_res_subst[OF _ res])
    fix x
    assume "x \<in> vars_term r"
    with wf_trs[OF lr] have x: "x \<in> vars_term l" by auto
    define i where "i = (SOME i. i < ?n \<and> xs ! i = x)"
    from x[unfolded vl set_conv_nth] have "\<exists> i. i < ?n \<and> xs ! i = x" by auto
    from someI_ex[OF this, folded i_def] have i: "i < ?n" and x: "xs ! i = x" by auto
    have "\<delta> x = qs' ! i" unfolding \<delta>_def i_def[symmetric] ..
    with merge[OF i] show "\<delta> x \<in> ta_res TA (?\<sigma> x)" unfolding x by simp
  qed
  from state_coherent_ctxt[OF state_coherent_rtrancl[OF coh] rel p] 
  obtain p' where rel: "(p, p') \<in> rel\<^sup>*" and p': "p' \<in> ta_res TA ?D\<langle>Var q''\<rangle>" by auto
  from ta_res_ctxt[OF res p'] rel show ?case unfolding av map_vars_term_ctxt_commute
    by (auto simp add: adapt_vars_ctxt_def)
qed

(* Corollary 37 *)
corollary state_raise_compatible_lang: "raise_step R `` ta_lang TA \<subseteq> ta_lang TA"
proof 
  fix t
  assume "t \<in> raise_step R `` ta_lang TA"
  then obtain s where s: "s \<in> ta_lang TA" and step: "(s,t) \<in> raise_step R" by auto
  from ta_langE2[OF s] obtain q where
    g: "ground s" and fin: "q \<in> ta_final TA" and res: "q \<in> ta_res TA (adapt_vars s)" .
  from step have "(s,t) \<in> sig_step UNIV (raise_step R)" by auto
  from sig_raise_step_imp_sig_steps[OF _ this]
  have "(s, t) \<in> (rstep Matchbounds.raise)\<^sup>* O rstep R" unfolding sig_step_def by simp
  then obtain u where su: "(s,u) \<in> (rstep Matchbounds.raise)\<^sup>*" and ut: "(u,t) \<in> rstep R" by auto
  have gu: "ground u" by (rule rsteps_ground[OF _ g su], auto simp: raise_def)
  have gt: "ground t" by (rule rstep_ground[OF wf_trs gu ut])
  from state_raise_compatible_res[OF step g res] obtain q' 
    where qq': "(q,q') \<in> rel^*" and res: "q' \<in> ta_res TA (adapt_vars t)" by auto
  from qq' state_coherentE2[OF coh] fin have fin: "q' \<in> ta_final TA"
    by (induct rule: rtrancl_induct, auto)
  from ta_langI2[OF gt fin res]
  show "t \<in> ta_lang TA" .
qed

lemma state_raise_compatible: 
  assumes L: "L \<subseteq> ta_lang TA"
  shows "{t | s. s \<in> L \<and> (s,t) \<in> (raise_step R)^*} \<subseteq> ta_lang TA"
  by (rule closed_imp_rtrancl_closed[OF L state_raise_compatible_lang])

end
end

end

