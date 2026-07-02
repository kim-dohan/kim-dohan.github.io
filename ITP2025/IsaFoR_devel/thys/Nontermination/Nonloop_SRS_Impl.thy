(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Nonloop_SRS_Impl
imports 
  Nonloop_SRS
  Framework.QDP_Framework_Impl
  Nontermination
  "HOL-Library.Simps_Case_Conv"
  Show.Shows_Literal
begin

lemma rotate_wp: "word_pat (l, (f, Suc c, ml @ mr), r) = word_pat (l @ ml, (f, c, mr @ ml), mr @ r)" (is "?l = ?r")
proof 
  fix n 
  define k where "k = f * n + c"
  show "?l n = ?r n" unfolding word_pat.simps
    by (simp add: k_def[symmetric], induct k, auto)
qed

lemma scale_wp: "word_pat (l, (f,c,(repl_list n m)), r) = word_pat (l, (n * f, n * c, m), r)" (is "?l = ?r")
proof 
  fix k
  define l where "l = f * k + c"
  have "repl_list (f * k + c) (repl_list n m)
    = repl_list l (repl_list n m)" unfolding l_def ..
  also have "\<dots> = repl_list (l * n) m"
    by (induct l, auto simp: replicate_add)
  also have "\<dots> = repl_list (n * f * k + n * c) m"
    unfolding l_def by (simp add: field_simps)
  finally have "repl_list (f * k + c) (repl_list n m) = repl_list (n * f * k + n * c) m" .
  then show "?l k = ?r k" by auto
qed

fun wp_nf :: "'f word_pat \<Rightarrow> bool" where 
  "wp_nf (l,(f,c,m),r) = (c = 0 \<and> (m = [] \<longrightarrow> f = 0 \<and> l = []) \<and> 
    (m \<noteq> [] \<longrightarrow> f = 1 \<and> (r = [] \<or> hd m \<noteq> hd r)))"

lemma wp_nf_range: assumes wp: "wp_nf (l,(f,0,m),r)" (is "wp_nf ?wp")
  shows "m = [] \<Longrightarrow> card (range (word_pat (l,(f,0,m),r))) = 1"
  "m \<noteq> [] \<Longrightarrow> card (range (word_pat (l,(f,0,m),r))) \<noteq> 1"
proof -
  assume "m = []"
  with wp have "range (word_pat ?wp) = {r}" by auto
  then show "card (range (word_pat (l,(f,0,m),r))) = 1" by simp
next
  assume m: "m \<noteq> []"
  show "card (range (word_pat (l,(f,0,m),r))) \<noteq> 1"
  proof
    assume "card (range (word_pat (l,(f,0,m),r))) = 1"
    then obtain e where ran: "range (word_pat (l,(f,0,m),r)) = {e}" 
      by (auto simp: card_Suc_eq)
    from m obtain a m' where m: "m = a # m'" by (cases m, auto)
    from wp m have f: "f = 1" by auto
    define u where "u = word_pat ?wp 0"
    define v where "v = word_pat ?wp (Suc 0)"
    define ran where "ran = range (word_pat ?wp)"
    have "{u,v} \<subseteq> range (word_pat ?wp)" unfolding u_def v_def by blast
    moreover have "u \<noteq> v" unfolding f m u_def v_def by auto
    ultimately show False using ran
    unfolding ran_def[symmetric] by blast
  qed
qed

lemma length_wp: "length (word_pat (l,(1,0,m),r) n) = length l + n * length m + length r"
  by (simp, induct n, auto)

lemma wp_nf: 
  assumes 1: "wp_nf wp1" and 2: "wp_nf wp2"
  shows "(word_pat wp1 = word_pat wp2) = (wp1 = wp2)"
proof
  assume id: "word_pat wp1 = word_pat wp2"
  then have idn: "\<And> n. word_pat wp1 n = word_pat wp2 n" by simp
  obtain l1 f1 m1 r1 where wp1: "wp1 = (l1,(f1,0,m1),r1)" using 1 by (cases wp1, force)
  obtain l2 f2 m2 r2 where wp2: "wp2 = (l2,(f2,0,m2),r2)" using 2 by (cases wp2, force)
  let ?card = "\<lambda> wp. card (range (word_pat wp))"
  show "wp1 = wp2"
  proof (cases m1)
    case Nil
    with 1 wp1 have wp1: "wp1 = oc r1" by auto
    note 1 = 1[unfolded wp1]
    from wp_nf_range[OF 1] have c1: "?card wp1 = 1" unfolding wp1 by auto    
    {
      assume "m2 \<noteq> []"
      with wp_nf_range[OF 2[unfolded wp2]] have "?card wp2 \<noteq> 1" unfolding wp2 by auto
      with c1 id have False by auto
    }
    then have m2: "m2 = []" by auto
    with 2 wp2 have wp2: "wp2 = oc r2" by auto
    from idn[of 0] wp1 wp2 show ?thesis by auto
  next
    case (Cons a1 k1)
    with 1 wp1 have wp1: "wp1 = (l1,(1,0,m1),r1)" and m1: "m1 = a1 # k1" by auto
    note 1 = 1[unfolded wp1]
    from wp_nf_range[OF 1] m1 have c1: "?card wp1 \<noteq> 1" unfolding wp1 by auto
    {
      assume "m2 = []"
      with wp_nf_range[OF 2[unfolded wp2]] have "?card wp2 = 1" unfolding wp2 by auto
      with c1 id have False by auto
    }
    then obtain a2 k2 where m2: "m2 = a2 # k2" by (cases m2) auto
    with wp2 2 have wp2: "wp2 = (l2,(1,0,m2),r2)" by auto
    note 2 = 2[unfolded wp2]
    from 1 m1 have 1: "r1 = [] \<or> a1 \<noteq> hd r1" by auto
    from 2 m2 have 2: "r2 = [] \<or> a2 \<noteq> hd r2" by auto
    note idn = idn[unfolded wp1 wp2]
    from 1 have r: "r1 = r2"
    proof 
      assume *: "r1 = []"
      from 2 show ?thesis
      proof 
        assume **: "a2 \<noteq> hd r2" 
        from * m1 m2 idn[of 1] idn[of 0] have "hd (r2 @ a1 # k1) = a2" by auto
        with ** * show ?thesis unfolding hd_append by metis
      qed (insert *, auto)
    next
      assume *: "a1 \<noteq> hd r1"
      from 2 show ?thesis
      proof 
        assume **: "r2 = []"
        with m1 m2 idn[of 1] idn[of 0] have "r1 @ a2 # k2 = a1 # k1 @ r1" by auto 
        then have "hd (r1 @ a2 # k2) = a1" by auto
        with ** * show ?thesis unfolding hd_append by metis
      next
        assume **: "a2 \<noteq> hd r2"
        {
          fix a1 l1 l2 r1 r2 m1 m2 and k1 :: "'f list"
          assume len: "length l1 \<le> length l2" 
            and *: "a1 \<noteq> hd r1" and m1: "m1 = a1 # k1" 
            and idn: "\<And> n. word_pat (l1, (1, 0, m1), r1) n = word_pat (l2, (1, 0, m2), r2) n"
          from len idn[of 0, simplified] append_eq_append_conv_if
          have r1r2: "r1 = drop (length l1) l2 @ r2" by metis
          moreover from len idn[of 1, simplified] append_eq_append_conv_if
          have "m1 @ r1 = drop (length l1) l2 @ m2 @ r2" by metis        
          moreover from * m1 have "hd (m1 @ r1) \<noteq> hd r1" by auto          
          ultimately have  "hd (drop (length l1) l2 @ m2 @ r2) \<noteq> hd (drop (length l1) l2 @ r2)" by metis
          with hd_append2 have "drop (length l1) l2 = []" by fastforce
          then have "r1 = r2" using r1r2 by auto
        } note main = this
        show ?thesis 
        proof (cases "length l1 \<le> length l2")
          case True
          show ?thesis using main[OF True * m1 idn] .
        next
          case False
          then have len: "length l2 \<le> length l1" by simp
          show ?thesis using main[OF len ** m2 idn[symmetric]] by simp
        qed
      qed
    qed
    with idn[of 0] have l: "l1 = l2" by auto
    from l r idn[of 1] have m: "m1 = m2" by simp
    from l r m show ?thesis unfolding wp1 wp2 by simp
  qed
qed auto

fun normalize_wp :: "'f word_pat \<Rightarrow> 'f word_pat" where
  "normalize_wp (l, (Suc 0,0,(a # m)), (b # r)) = (
    if a = b then normalize_wp (l @ [b], (Suc 0,0,m @ [b]), r)
      else (l, (Suc 0, 0, (a # m)), (b # r)))"
| "normalize_wp (l, (Suc 0,0,(a # m)), []) =  (l, (Suc 0,0,(a # m)), [])"
| "normalize_wp (l, (f,Suc c,m), r) = normalize_wp (l @ repl_list (Suc c) m, (f,0,m), r)"
| "normalize_wp (l, (0,0,m), r) = oc (l @ r)"
| "normalize_wp (l, (f,c,[]), r) = oc (l @ r)"
| "normalize_wp (l, (f,0,m), r) = normalize_wp (l, (Suc 0,0,repl_list f m), r)"

(* to work with efficient_nat, we require other code-equations *)
declare normalize_wp.simps[code del]
case_of_simps normalize_wp_cases: normalize_wp.simps
declare normalize_wp_cases [code]


lemma normalize_wp: "wp_nf (normalize_wp wp) \<and> word_pat (normalize_wp wp) = word_pat wp" (is "?P wp")
proof -
  {
    fix l f a m r
    assume "?P (l, (Suc 0, 0, repl_list (Suc (Suc f)) (a # m)), r)"
    then have "?P (l, (Suc (Suc f),0,(a # m)), r)" 
      unfolding normalize_wp.simps
      unfolding scale_wp by auto
  } note 6 = this
  show ?thesis
  proof (induct rule: normalize_wp.induct)
    case (1 l a m b r)
    show ?case
    proof (cases "a = b")
      case True
      {
        fix x
        have "b # repl_list x (m @ [b]) = repl_list x (b # m) @ [b]"
          by (induct x, auto)
      }
      with 1[OF True] True   
      show ?thesis by auto
    qed auto
  next
    case (2 l a m)
    show ?case by auto
  next
    case (3 l f c m r)
    have [simp]: "\<And> x. x + c = c + x" by auto
    from 3 show ?case by (auto simp: replicate_add)
  next
    case 4
    show ?case by auto
  next
    case 5
    show ?case by auto
  qed (insert 6, blast)
qed     


lemma word_pat_equiv_code[code]: "word_pat_equiv wp1 wp2 = 
  (wp1 = wp2 \<or> normalize_wp wp1 = normalize_wp wp2)" 
  unfolding word_pat_equiv_def using normalize_wp[of wp1] normalize_wp[of wp2] 
  wp_nf[of "normalize_wp wp1" "normalize_wp wp2"] by auto

datatype (dead 'f) dp_proof_step = 
  OC1 "'f srs_rule" bool
| OC2  "'f srs_rule" "'f srs_rule" "'f srs_rule" "'f list" "'f list" "'f list"
| OC2p  "'f srs_rule" "'f srs_rule" "'f srs_rule" "'f list" "'f list" "'f list"
| OC3  "'f srs_rule" "'f srs_rule" "'f srs_rule" "'f list" "'f list" 
| OC3p  "'f srs_rule" "'f srs_rule" "'f srs_rule" "'f list" "'f list" 
| OCDP1  "'f deriv_pat" "'f srs_rule"
| OCDP2  "'f deriv_pat" "'f srs_rule"
| WPEQ "'f deriv_pat" "'f deriv_pat"
| Lift "'f deriv_pat" "'f deriv_pat"
| DPOC1_1 "'f deriv_pat" "'f deriv_pat" "'f srs_rule" "'f list" "'f list" 
| DPOC1_2 "'f deriv_pat" "'f deriv_pat" "'f srs_rule" "'f list" "'f list" "'f list" 
| DPOC2 "'f deriv_pat" "'f deriv_pat" "'f srs_rule" "'f list" "'f list" 
| DPOC3_1 "'f deriv_pat" "'f deriv_pat" "'f srs_rule" "'f list" "'f list" 
| DPOC3_2 "'f deriv_pat" "'f deriv_pat" "'f srs_rule" "'f list" "'f list" "'f list" 
| DPDP1_1 "'f deriv_pat" "'f deriv_pat" "'f deriv_pat" "'f list" "'f list" 
| DPDP1_2 "'f deriv_pat" "'f deriv_pat" "'f deriv_pat" "'f list" "'f list" 
| DPDP2_1 "'f deriv_pat" "'f deriv_pat" "'f deriv_pat" "'f list" "'f list" 
| DPDP2_2 "'f deriv_pat" "'f deriv_pat" "'f deriv_pat" "'f list" "'f list"

abbreviation rule_to_pat :: "'f srs_rule \<Rightarrow> 'f deriv_pat" where "rule_to_pat rl \<equiv> (oc (fst rl), oc (snd rl))"

primrec pat_of :: "'f dp_proof_step \<Rightarrow> 'f deriv_pat" where
  "pat_of (OC1 rl _) = rule_to_pat rl"
| "pat_of (OC2 rl _ _ _ _ _) = rule_to_pat rl"
| "pat_of (OC2p rl _ _ _ _ _) = rule_to_pat rl"
| "pat_of (OC3 rl _ _ _ _) = rule_to_pat rl"
| "pat_of (OC3p rl _ _ _ _) = rule_to_pat rl"
| "pat_of (OCDP1 p _) = p"
| "pat_of (OCDP2 p _) = p"
| "pat_of (WPEQ p _) = p"
| "pat_of (Lift p _) = p"
| "pat_of (DPOC1_1 p _ _ _ _) = p"
| "pat_of (DPOC1_2 p _ _ _ _ _) = p"
| "pat_of (DPOC2 p _ _ _ _) = p"
| "pat_of (DPOC3_1 p _ _ _ _) = p"
| "pat_of (DPOC3_2 p _ _ _ _ _) = p"
| "pat_of (DPDP1_1 p _ _ _ _) = p"
| "pat_of (DPDP1_2 p _ _ _ _) = p"
| "pat_of (DPDP2_1 p _ _ _ _) = p"
| "pat_of (DPDP2_2 p _ _ _ _) = p"


definition prems_of :: "'f dp_proof_step \<Rightarrow> 'f deriv_pat list" where
  "prems_of step \<equiv> case step of 
  (OC1 _ _) \<Rightarrow> []
| (OC2 _ p p' _ _ _) \<Rightarrow> [rule_to_pat p, rule_to_pat p']
| (OC2p _ p p' _ _ _) \<Rightarrow> [rule_to_pat p, rule_to_pat p']
| (OC3 _ p p' _ _) \<Rightarrow> [rule_to_pat p, rule_to_pat p']
| (OC3p _ p p' _ _) \<Rightarrow> [rule_to_pat p, rule_to_pat p']
| (OCDP1 _ p) \<Rightarrow> [rule_to_pat p]
| (OCDP2 _ p) \<Rightarrow> [rule_to_pat p]
| (WPEQ _ p) \<Rightarrow> [p]
| (Lift _ p) \<Rightarrow> [p]
| (DPOC1_1 _ p rl _ _) \<Rightarrow> [p, rule_to_pat rl]
| (DPOC1_2 _ p rl _ _ _) \<Rightarrow> [p, rule_to_pat rl]
| (DPOC2 _ p rl _ _) \<Rightarrow> [p, rule_to_pat rl]
| (DPOC3_1 _ p rl _ _) \<Rightarrow> [p, rule_to_pat rl]
| (DPOC3_2 _ p rl _ _ _) \<Rightarrow> [p, rule_to_pat rl]
| (DPDP1_1 _ p1 p2 _ _) \<Rightarrow> [p1, p2]
| (DPDP1_2 _ p1 p2 _ _) \<Rightarrow> [p1, p2]
| (DPDP2_1 _ p1 p2 _ _) \<Rightarrow> [p1, p2]
| (DPDP2_2 _ p1 p2 _ _) \<Rightarrow> [p1, p2]"

fun showsl_srs_rule where "showsl_srs_rule (l,r) = (showsl l \<circ> showsl_lit (STR '' -> '') \<circ> showsl r)"
fun showsl_oc where "showsl_oc (l,r) = (showsl l \<circ> showsl_lit (STR '' ->+ '') \<circ> showsl r)"
fun showsl_exp where "showsl_exp (f,c) = (showsl f \<circ> showsl_lit (STR ''n+ '') \<circ> showsl c)"
fun showsl_p where "showsl_p (b,(f,c,m),a) = 
 (showsl b \<circ> showsl m \<circ> showsl_lit (STR '' ^ ('') \<circ> showsl_exp (f,c) \<circ> showsl_lit (STR '')'') \<circ> showsl a)"
fun showsl_pat where "showsl_pat (p1,p2) = (showsl_p p1 \<circ> showsl_lit (STR '' ->+ '') \<circ> showsl_p p2)"

locale fixed_show_srs = fixed_srs R for R :: "('f :: showl)srs"
begin
definition check_step :: "'f dp_proof_step \<Rightarrow> showsl check" where
  "check_step step \<equiv>  case step of 
    (OC1 uv isPair) \<Rightarrow> check (uv \<in> R) (showsl_srs_rule uv \<circ> showsl_lit (STR '' is not an original rule''))
  | (OC2 oc_new oc1 oc2 t x l) \<Rightarrow> (let (wl,tr) = oc_new; (w,tx) = oc1; (xl,r) = oc2 in do {(do {
      check (xl = x @ l) (showsl_lit (STR ''problem: xl != x l''));
      check (tx = t @ x) (showsl_lit (STR ''problem: tx != t x''));
      check (wl = w @ l) (showsl_lit (STR ''problem: wl != w l''));
      check (tr = t @ r) (showsl_lit (STR ''problem: tr != t r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OC2 of\<newline>'') 
      \<circ> showsl_oc oc1 \<circ> showsl_nl \<circ> showsl_oc oc2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_oc oc_new \<circ> showsl_nl \<circ> s
      ))
    })
 | (OC2p oc_new oc1 oc2 x t l) \<Rightarrow> (let (lw,rt) = oc_new; (w,xt) = oc1; (lx,r) = oc2 in do {(do {
      check (lx = l @ x) (showsl_lit (STR ''problem: lx != l x''));
      check (lw = l @ w) (showsl_lit (STR ''problem: lw != l w''));
      check (rt = r @ t) (showsl_lit (STR ''problem: rt != r t''));
      check (xt = x @ t) (showsl_lit (STR ''problem: xt != x t''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OC2' of\<newline>'') 
      \<circ> showsl_oc oc1 \<circ> showsl_nl \<circ> showsl_oc oc2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_oc oc_new \<circ> showsl_nl \<circ> s
      ))
    })
 | (OC3 oc_new oc1 oc2 t1 t2) \<Rightarrow> (let (w,t1rt2) = oc_new; (w',t1xt2) = oc1; (x,r) = oc2 in do {(do {
      check (t1rt2 = t1 @ r @ t2) (showsl_lit (STR ''problem: t1_r_t2 != t1 r t2''));
      check (t1xt2 = t1 @ x @ t2) (showsl_lit (STR ''problem: t1_x_t2 != t1 x t2''));
      check (w = w') (showsl_lit (STR ''problem: w differs''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OC3 of\<newline>'') 
      \<circ> showsl_oc oc1 \<circ> showsl_nl \<circ> showsl_oc oc2
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_oc oc_new \<circ> showsl_nl \<circ> s
      ))
    })
 | (OC3p oc_new oc1 oc2 t1 t2) \<Rightarrow> (let (t1wt2,r) = oc_new; (t1xt2,r') = oc1; (w,x) = oc2 in do {(do {
      check (t1wt2 = t1 @ w @ t2) (showsl_lit (STR ''problem: t1_w_t2 != t1 w t2''));
      check (t1xt2 = t1 @ x @ t2) (showsl_lit (STR ''problem: t1_x_t2 != t1 x t2''));
      check (r = r') (showsl_lit (STR ''problem: r differs''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OC3' of\<newline>'')
      \<circ> showsl_oc oc1 \<circ> showsl_nl \<circ> showsl_oc oc2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_oc oc_new \<circ> showsl_nl \<circ> s
      ))
    })
 | (OCDP1 p oc1) \<Rightarrow> (let (lc,cr) = oc1; ((e1,(f,d,l),c1),(c2,(f',d',r),e2)) = p in do {(do {
      check (e1 = []) (showsl_lit (STR ''problem: e1 not empty''));
      check (e2 = []) (showsl_lit (STR ''problem: e2 not empty''));
      check (c1 = c2) (showsl_lit (STR ''problem: c not equal''));
      check (f = 1 \<and> f' = 1 \<and> d = 0 \<and> d' = 0) (showsl_lit (STR ''problem: 0 and 1 conditions not met''));
      check (lc = l @ c1) (showsl_lit (STR ''problem: lc != l c''));
      check (cr = c1 @ r) (showsl_lit (STR ''problem: cr != c r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OCDP1 of\<newline>'') 
      \<circ> showsl_oc oc1  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p \<circ> showsl_nl \<circ> s
      ))})
 | (OCDP2 p oc1) \<Rightarrow> (let (cl,rc) = oc1; ((c1,(f,d,l),e1),(e2,(f',d',r),c2)) = p in do {(do {
      check (e1 = [] \<and> e2 = []) (showsl_lit (STR ''problem: e1 or e2 not empty''));
      check (c1 = c2) (showsl_lit (STR ''problem: c not equal''));
      check (f = 1 \<and> f' = 1 \<and> d = 0 \<and> d' = 0) (showsl_lit (STR ''problem: 0 and 1 conditions not met''));
      check (cl = c1 @ l) (showsl_lit (STR ''problem: lc != l c''));
      check (rc = r @ c1) (showsl_lit (STR ''problem: cr != c r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap OCDP1 of\<newline>'') 
      \<circ> showsl_oc oc1  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p \<circ> showsl_nl \<circ> s
      ))})
 | (WPEQ p_new p) \<Rightarrow> (let (left,right) = p; (left',right') = p_new  in do {( do {
      check (word_pat_equiv left left') (showsl_lit (STR ''problem: lhss are not equivalent''));
      check (word_pat_equiv right right') (showsl_lit (STR ''problem: rhss are not equivalent''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking equivalence of\<newline>'') 
      \<circ> showsl_pat p \<circ> showsl_lit (STR ''\<newline>and\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (Lift p_new p) \<Rightarrow> (let ((l1,(f1,c1,m1),r1),(l2,(f2,c2,m2),r2)) = p;
      ((l1',(f1',c1',m1'),r1'),(l2',(f2',c2',m2'),r2')) = p_new  in do {(do {
      check (l1 = l1' \<and> l2 = l2') (showsl_lit (STR ''problem: l and l' do not match''));
      check (r1 = r1' \<and> r2 = r2') (showsl_lit (STR ''problem: r and r' do not match''));
      check (f1 = f1' \<and> f2 = f2') (showsl_lit (STR ''problem: f and f' do not match''));
      check (m1 = m1' \<and> m2 = m2') (showsl_lit (STR ''problem: m and m' do not match''));
      check (c1' = c1+f1) (showsl_lit (STR ''problem: constant factor on the left not properly increased''));
      check (c2' = c2+f2) (showsl_lit (STR ''problem: constant factor on the right not properly increased''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking lifting of\<newline>'') 
      \<circ> showsl_pat p \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPOC1_1 p_new p1 oc1 l r) \<Rightarrow> (let (left,(lxr,m2,r2)) = p1;
      (x,v) = oc1; (left',(lvr,m2',r2')) = p_new  in do {(do {
      check (left = left') (showsl_lit (STR ''problem: lhss are not equal''));
      check (m2 = m2') (showsl_lit (STR ''problem: m2 and m2' do not match''));
      check (r2 = r2') (showsl_lit (STR ''problem: r2 and r2' do not match''));
      check (lxr = l @ x @ r) (showsl_lit (STR ''problem: l_x_r != l @ x @ r''));
      check (lvr = l @ v @ r) (showsl_lit (STR ''problem: l_v_r != l @ v @ r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPOC1_1 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_oc oc1 
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPOC1_2 p_new p1 oc1 l r x) \<Rightarrow> (let ((l1,m1,r1),(xr,m2,r2)) = p1;
      (lx,v) = oc1; ((ll1,m1',r1'),(vr,m2',r2')) = p_new  in do {(do {
      check (m1 = m1' \<and> m2 = m2') (showsl_lit (STR ''problem: m components modified''));
      check (r1 = r1' \<and> r2 = r2') (showsl_lit (STR ''problem: r components modified''));
      check (ll1 = l @ l1) (showsl_lit (STR ''problem: l_l1 != l @ ll1''));
      check (xr = x @ r) (showsl_lit (STR ''problem: x_r != x @ r''));
      check (lx = l @ x) (showsl_lit (STR ''problem: l_x != l @ x''));
      check (vr = v @ r) (showsl_lit (STR ''problem: v_r != v @ r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPOC1_2 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_oc oc1 
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPOC2 p_new p1 oc1 l r) \<Rightarrow> (let (left,(l2,(f2,c2,lxr),r2)) = p1;
      (x,v) = oc1; (left',(l2',(f2',c2',lvr),r2')) = p_new  in do {(do {
      check (left = left') (showsl_lit (STR ''problem: left components modified''));
      check (f2 = f2') (showsl_lit (STR ''problem: f components modified''));
      check (c2 = c2') (showsl_lit (STR ''problem: c components modified''));
      check (l2 = l2') (showsl_lit (STR ''problem: l components modified''));
      check (r2 = r2') (showsl_lit (STR ''problem: r components modified''));
      check (lxr = l @ x @ r) (showsl_lit (STR ''problem: l_x_r != l @ x @ r''));
      check (lvr = l @ v @ r) (showsl_lit (STR ''problem: l_v_r != l @ v @ r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPOC2 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_oc oc1  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPOC3_1 p_new p1 oc1 l r) \<Rightarrow> (let (left,(l2,m2,lxr)) = p1;
      (x,v) = oc1; (left',(l2',m2',lvr)) = p_new  in do {(do {
      check (left = left') (showsl_lit (STR ''problem: left components modified''));
      check (m2 = m2') (showsl_lit (STR ''problem: m components modified''));
      check (l2 = l2') (showsl_lit (STR ''problem: l components modified''));
      check (lxr = l @ x @ r) (showsl_lit (STR ''problem: l_x_r != l @ x @ r''));
      check (lvr = l @ v @ r) (showsl_lit (STR ''problem: l_v_r != l @ v @ r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPOC3_1 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_oc oc1 
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPOC3_2 p_new p1 oc1 l r x) \<Rightarrow> (let ((l1,m1,r1),(l2,m2,lx)) = p1;
      (xr,v) = oc1; ((l1',m1',r1r),(l2',m2',lv)) = p_new  in do {(do {
      check (m2 = m2' \<and> m1 = m1') (showsl_lit (STR ''problem: m components modified''));
      check (l1 = l1') (showsl_lit (STR ''problem: l components modified''));
      check (l2 = l2') (showsl_lit (STR ''problem: l2 components modified''));
      check (lx = l @ x) (showsl_lit (STR ''problem: l_x != l @ x''));
      check (xr = x @ r) (showsl_lit (STR ''problem: x_r != x @ r''));
      check (r1r = r1 @ r) (showsl_lit (STR ''problem: r1_r != r1 @ r''));
      check (lv = l @ v) (showsl_lit (STR ''problem: l_v != l @ v''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPOC3_2 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_oc oc1  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPDP1_1 p_new p1 p2 l r) \<Rightarrow> (let (left,(ll2,mm,r2r)) = p1;
      ((l2,mm',r2),(l2',mm2,r2')) = p2; (left',(ll2',mm2',r2pr)) = p_new  in do {(do {
      check (left = left') (showsl_lit (STR ''problem: left components modified''));
      check (mm = mm') (showsl_lit (STR ''problem: mm components modified''));
      check (mm2 = mm2') (showsl_lit (STR ''problem: mm2 components modified''));
      check (ll2 = l @ l2) (showsl_lit (STR ''problem: l_l2 != l @ l2''));
      check (r2r = r2 @ r) (showsl_lit (STR ''problem: r2_r != r2 @ r''));
      check (r2pr = r2' @ r) (showsl_lit (STR ''problem: r2pr != r2' @ r''));
      check (ll2' = l @ l2') (showsl_lit (STR ''problem: l_l2 != l @ l2 ''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPDP1_1 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_pat p2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPDP1_2 p_new p1 p2 l r) \<Rightarrow> (let ((l1',mm1',r1'),(ll2,mm,r1)) = p1;
      ((l2,mm2,r1r),(l2',mm2',r2')) = p2; ((l3,mm3,r1pr),(ll2',mm3',r3')) = p_new  in do {(do {
      check (l1' = l3) (showsl_lit (STR ''problem: l1' components modified''));
      check (mm1' = mm3) (showsl_lit (STR ''problem: mm1' components modified''));
      check (mm = mm2) (showsl_lit (STR ''problem: mm components modified''));
      check (mm2' = mm3') (showsl_lit (STR ''problem: mm2' components modified''));
      check (r2' = r3') (showsl_lit (STR ''problem: r2' components modified''));
      check (ll2 = l @ l2) (showsl_lit (STR ''problem: l_l2 != l @ l2''));
      check (r1pr = r1' @ r) (showsl_lit (STR ''problem: r1'r != r1' @ r''));
      check (r1r = r1 @ r) (showsl_lit (STR ''problem: r1r != r1 @ r''));
      check (ll2' = l @ l2') (showsl_lit (STR ''problem: l_l2 != l @ l2 ''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPDP1_2 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_pat p2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPDP2_1 p_new p1 p2 l r) \<Rightarrow> (let ((l1',mm1',r1'),(l1,mm,r2r)) = p1;
      ((ll1,mm2,r2),(l2',mm2',r2')) = p2; ((ll1',mm3,r3),(l3',mm3',r2pr)) = p_new  in do {(do {
      check (r2r = r2 @ r) (showsl_lit (STR ''problem: r2r != r2 @ r''));
      check (ll1 = l @ l1) (showsl_lit (STR ''problem: l_l1 != l @ l1''));
      check (ll1' = l @ l1') (showsl_lit (STR ''problem: l_l1' != l @ l1' ''));
      check (mm1' = mm3) (showsl_lit (STR ''problem: mm1' component modified''));
      check (r1' = r3) (showsl_lit (STR ''problem: r1' component modified''));
      check (l2' = l3') (showsl_lit (STR ''problem: l2' component modified''));
      check (mm2' = mm3') (showsl_lit (STR ''problem: mm2' components modified''));
      check (mm = mm2) (showsl_lit (STR ''problem: mm components modified''));
      check (r2pr = r2' @ r) (showsl_lit (STR ''problem: r2'r != r2' @ r''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPDP2_1 of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_pat p2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})
 | (DPDP2_2 p_new p1 p2 l r) \<Rightarrow> (let ((l1',mm1',r1'),(l1,mm1,r1)) = p1;
      ((ll1,mm2,r1r),right) = p2; ((ll1',mm3,r1pr),right') = p_new  in do {(do {
      check (r1r = r1 @ r) (showsl_lit (STR ''problem: r1r != r1 @ r''));
      check (ll1 = l @ l1) (showsl_lit (STR ''problem: l_l1 != l @ l1''));
      check (ll1' = l @ l1') (showsl_lit (STR ''problem: l_l1' != l @ l1' ''));
      check (r1pr = r1' @ r) (showsl_lit (STR ''problem: r1'_r != r1' @ r ''));
      check (mm1' = mm3) (showsl_lit (STR ''problem: mm1' component modified''));
      check (mm1 = mm2) (showsl_lit (STR ''problem: mm components modified''));
      check (right = right') (showsl_lit (STR ''problem: right components modified''))
    } <+? (\<lambda> s. showsl_lit (STR ''problem in checking overlap DPDP2_ of\<newline>'') 
      \<circ> showsl_pat p1 \<circ> showsl_nl \<circ> showsl_pat p2  
      \<circ> showsl_lit (STR ''\<newline>to yield\<newline>'') \<circ> showsl_pat p_new \<circ> showsl_nl \<circ> s
      ))})"

abbreviation prems_ok :: "'f dp_proof_step \<Rightarrow> bool" where "prems_ok p \<equiv> (\<forall> p' \<in> set (prems_of p). deriv_pat p')"

lemma check_step: 
 assumes ok:"isOK(check_step p)" and prems_ok:"prems_ok p"  
 shows "deriv_pat (fst (pat_of p), snd (pat_of p))" 
proof-      
  note check_step_def[simp]
  let ?P = "\<lambda> p :: 'f deriv_pat. deriv_pat p"
  {fix u v and p :: "'f deriv_pat"
    assume "deriv_pat (u,v)" "fst p = u" "snd p = v" 
    then have "deriv_pat p" by auto
  } note subst = this
  have subst2: "\<And> p q. ?P p \<Longrightarrow> p = q \<Longrightarrow> ?P q" by auto
  let ?ocdp = "\<lambda>oc. deriv_pat (rule_to_pat oc)"
  show "deriv_pat (fst (pat_of p), snd (pat_of p))" proof (cases p)
 case (OC1 lr isp)
  show ?thesis using ok unfolding OC1 using deriv_pat.OC1 by auto
next
 case (OC2 oc oc1 oc2 t x l)
  from prems_ok[unfolded this] have p:"?ocdp oc1" "?ocdp oc2" unfolding prems_of_def by auto
  show ?thesis 
    by (rule subst[OF deriv_pat.OC2, OF subst2[OF p(1)] subst2[OF p(2)]],
      insert ok, auto simp: OC2 split_beta) 
 next
 case (OC2p oc oc1 oc2 t x l)
  from prems_ok[unfolded this] have p:"?ocdp oc1" "?ocdp oc2" unfolding prems_of_def by auto
  show ?thesis 
    by (rule subst[OF deriv_pat.OC2', OF subst2[OF p(1)] subst2[OF p(2)]],
      insert ok, auto simp: OC2p split_beta) 
 next
 case (OC3 oc oc1 oc2 t1)
  from prems_ok[unfolded this] have p:"?ocdp oc1" "?ocdp oc2" unfolding prems_of_def by auto
  show ?thesis by (rule subst[OF deriv_pat.OC3, OF subst2[OF p(1)] subst2[OF p(2)]],
      insert ok, auto simp: OC3 split_beta) 
 next
 case (OC3p oc oc1 oc2 t1)
  from prems_ok[unfolded this] have p:"?ocdp oc1" "?ocdp oc2" unfolding prems_of_def by auto
    show ?thesis by (rule subst[OF deriv_pat.OC3', OF subst2[OF p(1)]  subst2[OF p(2)]], 
     insert ok, auto simp:OC3p split_beta)
 next
 case (OCDP1 p_new oc1)
  from prems_ok[unfolded this] have p:"?ocdp oc1" unfolding prems_of_def by auto
  show ?thesis by (cases p_new, cases oc1, rule subst[OF deriv_pat.oc_into_dp_1, OF subst2[OF p]], insert ok, 
   unfold check_step_def OCDP1, auto simp:OCDP1 split_beta)
 next
 case (OCDP2 p_new oc1)
  from prems_ok[unfolded this] have p:"?ocdp oc1" unfolding prems_of_def by auto
  show ?thesis by (cases p_new, cases oc1, 
   rule subst[OF deriv_pat.oc_into_dp_2, OF subst2[OF p]], insert ok, 
   auto simp:OCDP2 split_beta)
 next
 case (Lift p_new p)
  from prems_ok[unfolded this] have dp:"deriv_pat p" unfolding prems_of_def by auto
  show ?thesis by (cases p_new, rule subst[OF deriv_pat.lift, OF subst2[OF dp]], insert ok, auto simp: Lift split_beta)
 next
 case (DPOC1_1 p_new p oc1)
  from prems_ok[unfolded this] have dp: "deriv_pat p" "?ocdp oc1" unfolding prems_of_def by auto
  obtain x v where oc1:"oc1 = (x,v)" by force
  show ?thesis by (cases p_new, cases p, 
   rule subst[OF deriv_pat.dp_oc_1_1, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:oc1 DPOC1_1 split_beta)
 next
 case (DPOC1_2 p_new p oc1)
  from prems_ok[unfolded this] have dp: "deriv_pat p" "?ocdp oc1" unfolding prems_of_def by auto
  obtain l1 m1 r1 f1 c1 l2 m2 r2 f2 c2 where p':"p_new=((l1,(f1,c1,m1),r1),(l2,(f2,c2,m2),r2))" by (cases p_new, force)
  show ?thesis by (cases p, rule subst[OF deriv_pat.dp_oc_1_2, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:p' DPOC1_2 split_beta)
 next
 case (DPOC2 p_new p oc1)
  from prems_ok[unfolded this] have dp: "deriv_pat p" "?ocdp oc1" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p, rule subst[OF deriv_pat.dp_oc_2, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:p' DPOC2 split_beta)
 next
 case (DPOC3_1 p_new p oc1 l r)
  from prems_ok[unfolded this] have dp: "deriv_pat p" "?ocdp oc1" unfolding prems_of_def by auto
  show ?thesis by (cases p, cases p_new, rule subst[OF deriv_pat.dp_oc_3_1, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:DPOC3_1 split_beta)
 next
 case (DPOC3_2 p_new p oc1 l r x)
  from prems_ok[unfolded this] have dp: "deriv_pat p" "?ocdp oc1" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p, rule subst[OF deriv_pat.dp_oc_3_2, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:p' DPOC3_2 split_beta)
 next
 case (DPDP1_1 p_new p1 p2 l r)
  from prems_ok[unfolded this] have dp: "deriv_pat p1" "deriv_pat p2" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p1, cases p2, rule subst[OF deriv_pat.dp_dp_1_1, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:DPDP1_1 p' split_beta)
 next
 case (DPDP1_2 p_new p1 p2 l r)
  from prems_ok[unfolded this] have dp: "deriv_pat p1" "deriv_pat p2" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p1, cases p2, rule subst[OF deriv_pat.dp_dp_1_2, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:DPDP1_2 p' split_beta)
 next
 case (DPDP2_1 p_new p1 p2 l r)
  from prems_ok[unfolded this] have dp: "deriv_pat p1" "deriv_pat p2" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p1, cases p2, rule subst[OF deriv_pat.dp_dp_2_1, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:DPDP2_1 p' split_beta)
 next
 case (DPDP2_2 p_new p1 p2 l r)
  from prems_ok[unfolded this] have dp: "deriv_pat p1" "deriv_pat p2" unfolding prems_of_def by auto
  obtain l3 m3 r3 f3 c3 l4 m4 r4 f4 c4 where p':"p_new=((l3,(f3,c3,m3),r3),(l4,(f4,c4,m4),r4))" by (cases p_new, force)
  show ?thesis by (cases p1, cases p2, rule subst[OF deriv_pat.dp_dp_2_2, OF subst2[OF dp(1)]  subst2[OF dp(2)]], insert ok, 
   auto simp:DPDP2_2 p' split_beta)
 next
 case (WPEQ p_new p)
  from prems_ok[unfolded this] have dp:"deriv_pat p" unfolding prems_of_def by auto
  obtain left right where p:"p = (left, right)" by (cases p)
  obtain left' right' where p':"p_new = (left', right')" by (cases p_new)
  from ok[unfolded WPEQ] p p' have eq:"word_pat_equiv left left'" "word_pat_equiv right right'" by auto
  from subst[OF deriv_pat.wp_equiv[OF eq(1) eq(2)], OF dp[unfolded p]]  p'
   show ?thesis unfolding WPEQ by auto
 qed
qed

primrec check_proof::"'f deriv_pat set \<Rightarrow> 'f dp_proof_step list \<Rightarrow> showsl check" where
   "check_proof \<Delta> [] = succeed"
 | "check_proof \<Delta> (p # ps) = do {
     check_step p; 
     check_allm (\<lambda> p. 
      check (p \<in> \<Delta>) (showsl_lit (STR ''problem: nothing known about premise '') \<circ> showsl_pat p)) (prems_of p);
     check_proof (\<Delta> \<union> {pat_of p}) ps
  }"

lemma check_proof:
 assumes ok:"isOK(check_proof {} ps)" 
 and mem: "p \<in> set ps"
 shows "deriv_pat_valid (fst (pat_of p), snd (pat_of p))" 
proof-
 {fix \<Delta> 
  have aux:"\<forall>p \<in> \<Delta>. deriv_pat p  \<Longrightarrow> 
  isOK(check_proof \<Delta> ps) \<Longrightarrow> \<forall>p \<in> set ps. deriv_pat (fst (pat_of p), snd (pat_of p))" 
 proof(induct ps arbitrary:\<Delta>)
  case Nil show ?case by auto
  next
  case (Cons x xs)
   from Cons(3) Cons(2) have step:"isOK(check_step x)" "prems_ok x" by auto
   from check_step[OF step(1) step(2)] Cons(3) have x:"deriv_pat (fst (pat_of x), snd (pat_of x))" by force
   with Cons(2) have 2:"\<forall>p \<in> (\<Delta> \<union> {pat_of x}). deriv_pat p" by auto
   from Cons(3) have 3:"isOK(check_proof (\<Delta> \<union> {pat_of x}) xs)" by auto
   from Cons(1)[OF 2 3] x show ?case by force
 qed
 } note aux = this
 from aux[OF _ ok] mem deriv_pat_valid show ?thesis by blast
qed
end


declare fixed_show_srs.check_proof.simps[code]
declare fixed_show_srs.check_step_def[code] 

datatype ('f) non_loop_srs_proof = 
  SE_OC "'f srs_rule" "'f list" "'f list" "'f dp_proof_step list"
| SE_DP "'f deriv_pat" "'f list" "'f list" "'f dp_proof_step list"

fun check_non_loop_srs_proof :: "('f :: showl)srs \<Rightarrow> 'f non_loop_srs_proof \<Rightarrow> showsl check" where
  "check_non_loop_srs_proof R (SE_OC (m,lmr) l r steps) = do {
    check ((oc m,oc lmr) \<in> set (map pat_of steps)) (showsl_lit (STR ''overlap closure not derived within proof''));
    check (lmr = l @ m @ r) (showsl_lit (STR ''no selfoverlap''));
    fixed_show_srs.check_proof R {} steps
  }"
| "check_non_loop_srs_proof R (SE_DP (left,right) l r steps) = do {
    check ((left, right) \<in> set (map pat_of steps)) (showsl_lit (STR ''overlap closure not derived within proof''));
    let (l1,(f1,c1,m1),r1) = left;
    let (l2,(f2,c2,m2),r2) = right;
    check (m1 = m2 \<and> l2 = l @ l1 \<and> r2 = r1 @ r) (showsl_lit (STR ''problem with selfoverlap''));
    check (f1 \<le> f2 \<and> max (c2 - c1) (c1 - c2) mod f1 = 0 \<and> (f1 < f2 \<longrightarrow> f2 mod f1 = 0) \<and> (f1 = f2 \<longrightarrow> c1 \<le> c2))
      (showsl_lit (STR ''could not ensure fitting condition for selfoverlap''));
    fixed_show_srs.check_proof R {} steps
  }"

lemma check_non_loop_srs_proof: assumes ok: "isOK(check_non_loop_srs_proof R prf)"
  shows "\<not> SN (srs_step R)"
proof -
  interpret fixed_show_srs R .
  show ?thesis
  proof (cases "prf")
    case (SE_OC mlmr l r steps)
    obtain m lmr where mlmr: "mlmr = (m,lmr)" by force
    from ok[unfolded SE_OC mlmr] have
      mem: "(oc m, oc lmr) \<in> pat_of ` set steps" and lmr: "lmr = l @ m @ r" 
      and ok: "isOK (check_proof {} steps)"
    by auto
    show ?thesis
      by (rule fixed_srs.self_embed_oc[of _ m l r], insert check_proof[OF ok] mem, auto simp: lmr)
  next
    case (SE_DP lr l r steps)
    obtain left right where lr: "lr = (left,right)" by (cases lr)
    obtain l1 f1 c1 m1 r1 where left: "left = (l1,(f1,c1,m1),r1)" by (cases left, force)
    obtain l2 f2 c2 m2 r2 where right: "right = (l2,(f2,c2,m2),r2)" by (cases right, force)
    note ok = ok[unfolded SE_DP lr left right, simplified]
    from ok have ok': "isOK (check_proof {} steps)" by auto
    have fit: "fittable f1 c1 f2 c2"
      by (rule fittableI, insert ok, auto)
    show ?thesis
      by (rule fixed_srs.self_embed_dp[OF _ fit, of _ l1 m2 r1 l r],
        insert check_proof[OF ok'] ok, auto simp: lr)
  qed
qed

definition srs_of_trs_impl :: "('f,'v)rule list \<Rightarrow> 'f srs_rule list" where 
  "srs_of_trs_impl R = [ (term_to_string l, term_to_string r) . (l,r) \<leftarrow> R, unary_term l, unary_term r]"

lemma srs_of_trs_impl[simp]: "set (srs_of_trs_impl R) = srs_of_trs (set R)" 
  unfolding srs_of_trs_impl_def srs_of_trs_def by auto

definition "check_non_loop_srs_prf I tp prf \<equiv> do {
  let R    = tp_ops.rules I tp;
  let S    = set (srs_of_trs_impl R);
  check (tp_ops.Q I tp = []) (showsl_lit (STR ''strategy for non-loops unsupported''));
  check_non_loop_srs_proof S prf}"

lemma check_non_loop_srs_prf:
  assumes ok: "isOK (check_non_loop_srs_prf I tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  let ?R = "tp_ops.rules I tp"
  let ?Q = "tp_ops.Q I tp"
  let ?S = "srs_of_trs (set ?R)"
  note ok = ok[unfolded check_non_loop_srs_prf_def Let_def]
  from ok have Q: "?Q = []" by auto
  from ok have "isOK(check_non_loop_srs_proof ?S prf)" by auto
  from check_non_loop_srs_proof[OF this] srs_of_trs_SN[of "set ?R"] Q
  show ?thesis by auto
qed

hide_const (open) oc

end
