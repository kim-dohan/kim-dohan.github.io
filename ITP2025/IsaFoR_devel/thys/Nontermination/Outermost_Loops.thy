(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Outermost_Loops
imports
  Innermost_Loops_Impl
  TRS.Outermost_Rewriting
  First_Order_Terms.Option_Monad
begin

type_synonym ('f,'v)oloop = "('f,'v)ctxt \<times> ('f,'v)subst \<times> nat \<times> (nat \<Rightarrow> ('f,'v)term) \<times> (nat \<Rightarrow> pos)"

definition oloop :: "('f,'v)terms \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)oloop \<Rightarrow> bool"
  where "oloop Q R ol \<equiv> case ol of (C,\<mu>,len,ts,ps) \<Rightarrow>
  (\<forall> i \<le> len. (\<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>)) \<and>
  (\<forall> i \<le> len. \<forall> n. ostep_cond Q (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))) \<and>
  (ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>)"

lemma oloop_cond: assumes loop: "oloop Q R (C,\<mu>,len,ts,ps)"
  and i: "i \<le> len"
  shows "ostep_cond Q (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))"
  using assms unfolding oloop_def by blast

lemma oloop_ostep_p: assumes oloop: "oloop Q R (C,\<mu>,len,ts,ps)"
  and i: "i \<le> len"
  shows "(ctxt_subst C \<mu> n (ts i), ctxt_subst C \<mu> n (ts (Suc i))) \<in> ostep_p Q R (hole_pos C ^ n @ ps i)"
proof -
  note loop = oloop[unfolded oloop_def]
  from loop i obtain \<sigma> lr where step: "(ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>" by auto
  show ?thesis
    by (rule ostep_pI[OF ctxt_subst_step[OF step]], rule oloop_cond[OF oloop], insert i, auto)
qed

lemma oloop_end: assumes oloop: "oloop Q R (C,\<mu>,len,ts,ps)"
  shows "ctxt_subst C \<mu> n (ts (Suc len)) = ctxt_subst C \<mu> (Suc n) (ts 0)"
proof -
  note loop = oloop[unfolded oloop_def]
  from loop have ts: "ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>" by auto
  show ?thesis unfolding ts unfolding ctxt_subst_Suc ..
qed

lemma oloop_iterate: assumes oloop: "oloop Q R (C,\<mu>,len,ts,ps)"
  shows "(ctxt_subst C \<mu> n (ts 0), ctxt_subst C \<mu> (Suc n) (ts 0)) \<in> (ostep Q R)^+"
proof -
  let ?t = "\<lambda> i. ctxt_subst C \<mu> n (ts i)"
  from oloop_ostep_p[OF oloop] have steps_i: "\<And> i. i \<le> len \<Longrightarrow> (?t i, ?t (Suc i)) \<in> ostep Q R" unfolding ostep_def by blast
  have steps: "(?t 0, ?t len) \<in> (ostep Q R)^*"
    unfolding rtrancl_fun_conv
    by (rule exI[of _ ?t], rule exI[of _ len], insert steps_i, auto)
  have step: "(?t len, ctxt_subst C \<mu> (Suc n) (ts 0)) \<in> ostep Q R"
    using steps_i[of len]
    unfolding oloop_end[OF oloop, of n] by simp
  from steps step show ?thesis by auto
qed

lemma oloop_imp_not_SN: assumes oloop: "oloop Q R (C,\<mu>,len,ts,ps)"
  shows "\<not> SN_on (ostep Q R) {ts 0}"
proof
  assume SN: "SN_on (ostep Q R) {ts 0}"
  let ?O = "(ostep Q R)^+"
  from SN have SN: "SN_on ?O {ts 0}" by (rule SN_on_trancl)
  let ?t = "\<lambda> i. ctxt_subst C \<mu> i (ts 0)"
  from oloop_iterate[OF oloop] have steps: "\<And> i. (?t i, ?t (Suc i)) \<in> ?O" .
  have steps: "\<exists> f. f 0 \<in> {ts 0} \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?O)" 
    by (rule exI[of _ ?t], insert steps, auto)
  with SN show False unfolding SN_defs by blast
qed

definition ostep_ctxt_subst_cond :: "('f,'v)term \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)subst \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "ostep_ctxt_subst_cond l C \<mu> p t \<equiv> (\<forall> n. ostep_cond_single l (hole_pos C ^ n @ p) (ctxt_subst C \<mu> n t))"

lemma oloopI: assumes steps: "\<And> i. i \<le> len \<Longrightarrow> \<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>"
  and len: "ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>"
  and ocond: "\<And> l i. i \<le> len \<Longrightarrow> ps i \<in> poss (ts i) \<Longrightarrow> l \<in> Q \<Longrightarrow> ostep_ctxt_subst_cond l C \<mu> (ps i) (ts i)"
  shows "oloop Q R (C,\<mu>,len,ts,ps)"
  unfolding oloop_def split_def fst_conv snd_conv
proof (intro conjI allI impI)
  fix i n
  assume i: "i \<le> len"
  from steps[OF i]
  show "\<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>" by blast
  from steps[OF i] have "ps i \<in> poss (ts i)" unfolding rstep_r_p_s_def' by auto
  from ocond[OF i this, unfolded ostep_ctxt_subst_cond_def]
  show "ostep_cond Q (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))" 
    unfolding ostep_cond_def by blast
qed (simp add: len)

text \<open>by lemma oloopI, for deciding outermost loops it remains
  to provide a decision procedure for ostep_ctxt_subst_cond 
  (we did however not prove that oloopI is also a necessary requirement)
  (assuming that \<mu> is a finite substitution)\<close>

section \<open>decision procedures for outermost loops\<close>
(* extended matching and identity problem as defined in "Loops under strategies"-paper (Def. 3 and 6),
   both in general form (egmatch_prob), or in simplified form without matching problems (ematch_prob) *)
type_synonym ('f, 'v) ematch_prob = "('f, 'v) ctxt \<times> ('f, 'v) term \<times> ('f, 'v) ctxt \<times> ('f, 'v) term"
type_synonym ('f, 'v) egmatch_prob = "('f, 'v) ctxt \<times> ('f, 'v) term \<times> ('f, 'v) ctxt \<times> ('f, 'v) term \<times> ('f, 'v) gmatch_prob"
type_synonym ('f, 'v) eident_prob = "('f, 'v) ctxt \<times> ('f, 'v) term \<times> ('f, 'v) ctxt \<times> ('f, 'v) term"
type_synonym ('f, 'v) ematch_solution = "nat \<times> nat \<times> ('f, 'v) subst"

(* being in solved form (Def. 5) *)
definition egmatch_solved_form :: "('f, 'v) egmatch_prob \<Rightarrow> bool" where
  "egmatch_solved_form mp \<equiv> case mp of (_, l, _, _, M) \<Rightarrow> is_Var l \<and> gmatch_solved_form M"

context fixed_subst 
begin
(* solutions extended matching and idendity problems (Def. 3 and 6) *)
definition egmatch_solution :: "('f, 'v) egmatch_prob \<Rightarrow> ('f, 'v) ematch_solution \<Rightarrow> bool" where
  "egmatch_solution mp sol \<equiv> case (mp, sol) of ((D, l, C, t, M), (n, k, \<sigma>)) \<Rightarrow> 
    gmatch_solution M (k, \<sigma>) \<and> D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> (\<mu> ^^ k) = l \<cdot> \<sigma>"

definition eident_solution :: "('f, 'v) eident_prob \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "eident_solution eip sol \<equiv> case (eip, sol) of ((D, s, C, t), (n, k)) \<Rightarrow> D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> (\<mu> ^^ k) = s \<cdot> (\<mu> ^^ k)"

definition ematch_solution :: "('f, 'v) ematch_prob \<Rightarrow> ('f, 'v) ematch_solution \<Rightarrow> bool" where
  "ematch_solution emp sol \<equiv> case (emp, sol) of ((D, l, C, t), (n, k, \<sigma>)) \<Rightarrow> D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> (\<mu> ^^ k) = l \<cdot> \<sigma>"

subsection \<open>From outermost loops to extended matching problems\<close>
(* the matching problems for an outermost loop (Def. 4) *)
definition o_match_probs :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" where
  "o_match_probs l q t \<equiv> {(t |_ q', l) | q'. q' <\<^sub>p q}"

definition o_ematch_probs :: "('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ematch_prob set" where
  "o_ematch_probs C l q t \<equiv> {(C |_c p', l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>) | p'. p' <\<^sub>p hole_pos C}"

(* part of Thm 2, that loop is outermost loop iff none of the matching problems are solvable *)  
lemma o_match_probs_sound:
  assumes qt: "q \<in> poss t" 
    and sol: "match_solution mp (n, \<sigma>)"
    and mp: "mp \<in> o_match_probs l q t"
  shows "\<not> ostep_ctxt_subst_cond l C \<mu> q t"
proof -
  from mp[unfolded o_match_probs_def] obtain q' where 
    q': "q' <\<^sub>p q" and mp: "mp = (t |_ q',l)" by auto
  from q'[unfolded less_pos_def'] obtain q'' where q: "q = q' @ q''"
    and q'': "q'' \<noteq> []" by auto
  let ?cmu = "ctxt_subst C \<mu>"
  let ?p = "hole_pos C"
  let ?q = "?p ^ n @ q'"
  have less: "?q <\<^sub>p ?p ^ n @ q" unfolding q less_pos_def'
    by (rule exI[of _ q''], insert q'', auto)
  from sol[unfolded mp match_solution_def split] have l\<sigma>: "l \<cdot> \<sigma> = t |_ q' \<cdot> \<mu> ^^ n" by simp
  from qt q have q': "q' \<in> poss t" by auto
  have sol: "(?cmu n t) |_ ?q = l \<cdot> \<sigma>" unfolding l\<sigma> 
    unfolding  subt_at_append[OF ctxt_subst_hole_pos]
    unfolding ctxt_subst_subt_at
    unfolding subt_at_subst[OF q'] ..
  have "\<not> ostep_cond_single l (?p ^ n @ q) (?cmu n t)"
    unfolding  ostep_cond_single_def using less sol by blast
  then show ?thesis unfolding ostep_ctxt_subst_cond_def by auto
qed

(* another part of Thm 2 *)  
lemma o_ematch_probs_sound:
  assumes sol: "ematch_solution mp (n, k, \<sigma>)"
    and mp: "mp \<in> o_ematch_probs C l q t"
  shows "\<not> ostep_ctxt_subst_cond l C \<mu> q t"
proof -
  let ?cmu = "ctxt_subst C \<mu>"
  let ?cmu' = "ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu>"
  let ?p = "hole_pos C"
  from mp[unfolded o_ematch_probs_def] obtain p' where 
    p': "p' <\<^sub>p ?p" and mp: "mp = (C |_c p', l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>)" by auto
  from p'[unfolded less_pos_def'] obtain p'' where p: "?p = p' @ p''"
    and p'': "p'' \<noteq> []" by auto
  let ?q = "?p ^ k @ p'"
  let ?n = "k + Suc 0 + n"
  let ?q' = "p'' @ ?p ^ n @ q"
  have less: "?q <\<^sub>p ?p ^ ?n @ q" unfolding less_pos_def'
  proof (rule exI[of _ ?q'], rule conjI)
    have "?p ^ ?n @ q = ?p ^ k @ ?p @ ?p ^ n @ q" unfolding power_append_distr
      by simp
    also have "... = ?q @ ?q'" unfolding p by simp
    finally show "?p ^ ?n @ q = ?q @ ?q'" .
  qed (insert p'', auto)    
  from sol[unfolded mp ematch_solution_def split] have l\<sigma>: "l \<cdot> \<sigma> = (C |_c p') \<langle>?cmu' n (t \<cdot> \<mu>)\<rangle> \<cdot> \<mu> ^^ k" by simp
  from split_ctxt[OF p] obtain D E where C: "C = D \<circ>\<^sub>c E"
    and p': "hole_pos D = p'" and p'': "hole_pos E = p''" and E: "E = C |_c p'" by blast  
  from C p' hole_pos_poss have p': "\<And> t. p' \<in> poss (C\<langle>t\<rangle>)" by auto
  have sol: "(?cmu ?n t) |_ ?q = l \<cdot> \<sigma>" unfolding l\<sigma> 
    unfolding ctxt_subst_add
    unfolding subt_at_append[OF ctxt_subst_hole_pos]
    unfolding ctxt_subst_subt_at
    unfolding ctxt_subst.simps
    unfolding ctxt_subst_subst
    unfolding subt_at_subst[OF p']
    unfolding subt_at_subt_at_ctxt[OF p] ..
  have "\<not> ostep_cond_single l (?p ^ ?n @ q) (?cmu ?n t)"
    unfolding  ostep_cond_single_def using less sol by blast
  then show ?thesis unfolding ostep_ctxt_subst_cond_def by blast
qed

(* final part of Thm 2 *)  
lemma o_match_probs_complete:
  assumes qt: "q \<in> poss t" 
    and ncond: "\<not> ostep_ctxt_subst_cond l C \<mu> q t"
  shows "(\<exists>mp sol. mp \<in> o_match_probs l q t \<and> match_solution mp sol)
  \<or> (\<exists>mp sol. mp \<in> o_ematch_probs C l q t \<and> ematch_solution mp sol)"
proof -
  let ?cmu = "ctxt_subst C \<mu>"
  let ?cmu' = "ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu>"
  let ?p = "hole_pos C"
  note ncond = ncond[unfolded ostep_ctxt_subst_cond_def ostep_cond_single_def]
  from ncond obtain m q' \<sigma> where q': "q' <\<^sub>p ?p ^ m @ q"
    and l\<sigma>: "(?cmu m t) |_ q' = l \<cdot> \<sigma>" by blast
  let ?pq = "?p ^ m @ q"
  from q'[unfolded less_pos_def'] obtain q'' where pq: "?pq = q' @ q''"
    and q'': "q'' \<noteq> []" by auto
  show ?thesis
  proof (cases "\<exists> p'. q' = ?p ^ m @ p'")
    case True
    then obtain p' where q': "q' = ?p ^ m @ p'" by blast
    with pq have q: "q = p' @ q''" by auto    
    with q'' have less: "p' <\<^sub>p q" unfolding less_pos_def' by auto
    from q qt have p't: "p' \<in> poss t" by simp
    let ?mp = "(t |_ p',l)"
    let ?sol = "(m,\<sigma>)"
    from less have mp: "?mp \<in> o_match_probs l q t" unfolding o_match_probs_def by auto
    have sol: "t |_ p' \<cdot> \<mu> ^^ m = l \<cdot> \<sigma>" 
      unfolding l\<sigma>[symmetric] q'
      unfolding subt_at_append[OF ctxt_subst_hole_pos]
      unfolding ctxt_subst_subt_at
      unfolding subt_at_subst[OF p't] ..
    then have sol: "match_solution ?mp ?sol" 
      unfolding match_solution_def by simp
    show ?thesis using mp sol by blast
  next
    case False
    with pos_append_cases[OF pq] obtain q3 where pm: "?p ^ m = q' @ q3" and q''q3: "q'' = q3 @ q" by auto 
    have less: "q' <\<^sub>p ?p ^ m" using pm False pq by (cases q3, auto)
    from less_pos_power_split[OF this]
    obtain p' k where q'k: "q' = ?p^k @ p'" and less: "p' <\<^sub>p ?p" and k: "k < m"
      by blast
    from less[unfolded less_pos_def'] obtain p'' where p': "?p = p' @ p''" by auto
    from hole_pos_poss[of C, unfolded p'] have p't: "\<And> t. p' \<in> poss (C\<langle>t\<rangle>)" by auto
    from k have "m = k + Suc 0 + (m - k - Suc 0)" by auto
    then obtain n where m: "m = k + Suc 0 + n" by blast
    let ?mp = "(C |_c p', l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>)"
    let ?sol = "(n,k,\<sigma>)"
    from less have mp: "?mp \<in> o_ematch_probs C l q t" unfolding o_ematch_probs_def by auto
    have "(C |_c p') \<langle>?cmu' n (t \<cdot> \<mu>)\<rangle> \<cdot> (\<mu> ^^ k) = l \<cdot> \<sigma>"
      unfolding ctxt_subst_subst [symmetric] l\<sigma>[symmetric] m 
      unfolding ctxt_subst_add ctxt_subst.simps q'k
      unfolding subt_at_append[OF ctxt_subst_hole_pos]
      unfolding ctxt_subst_subt_at
      unfolding subt_at_subst[OF p't]
      unfolding subt_at_subt_at_ctxt[OF p'] ..
    then have sol: "ematch_solution ?mp ?sol" 
      unfolding ematch_solution_def by simp
    from mp sol
    show ?thesis by blast
  qed
qed

(* Thm 2: outermost loop iff matching problems are not solvable *)
lemma o_match_probs: assumes q: "q \<in> poss t" 
  shows "ostep_ctxt_subst_cond l C \<mu> q t = (\<not> ( 
    (\<exists> mp sol. mp \<in> o_match_probs l q t \<and> match_solution mp sol) \<or>
    (\<exists> mp sol. mp \<in> o_ematch_probs C l q t \<and> ematch_solution mp sol)))" (is "?l = (\<not> (?r1 \<or> ?r2))")
proof (cases "ostep_ctxt_subst_cond l C \<mu> q t")
  case False
  from o_match_probs_complete[OF q False] False show ?thesis by simp
next
  case True
  {
    assume "?r1 \<or> ?r2"
    then have False
    proof
      assume ?r1
      then obtain mp sol where mp: "mp \<in> o_match_probs l q t" and sol: "match_solution mp sol" by auto
      obtain n \<sigma> where id: "sol = (n,\<sigma>)" by force
      from o_match_probs_sound[OF q sol[unfolded id] mp] True show False ..
    next
      assume ?r2
      then obtain mp sol where mp: "mp \<in> o_ematch_probs C l q t" and sol: "ematch_solution mp sol" by auto
      obtain n k \<sigma> where id: "sol = (n,k,\<sigma>)" by (cases sol, auto)
      from o_ematch_probs_sound[OF sol[unfolded id] mp] True show False ..
    qed
  }
  with True show ?thesis by blast
qed
end

subsection \<open>Solving extended matching problems\<close>

context fixed_subst_incr
begin

(* Simplifying extended matching problems (Def. 5), 
   second argument are already solved matching problems,
   None as return value is \<bottom>,
   Some None as return value is \<top>, and 
   Some Some emp as return value means that emp is equisolvable matching problem in solved form *)
function
  simplify_emp_main ::
    "('f, 'v) egmatch_prob \<Rightarrow> ('f, 'v) gmatch_prob \<Rightarrow> (('f, 'v) egmatch_prob option) option"
where
  "simplify_emp_main (D,l,C,t,(s, Var x) # mp) solved = simplify_emp_main (D,l,C,t,mp) ((s,Var x) # solved)" 
| "simplify_emp_main (D,l,C,t,(Fun g ts, Fun f ls) # mp) solved = do {
    guard (f = g);
    pairs \<leftarrow> zip_option ts ls;
    simplify_emp_main (D,l,C,t,(pairs @ mp)) solved
  }" 
| "simplify_emp_main (D,l,C,t,(Var x, Fun f ls) # mp) solved = do {
    guard (x \<in> V_sincr);
    let m = map (\<lambda>(s, l). (s \<cdot> \<mu>, l));
    simplify_emp_main (D \<cdot>\<^sub>c \<mu>,l,C \<cdot>\<^sub>c \<mu>,t \<cdot> \<mu>,m ((Var x, Fun f ls) # mp)) (m solved)
  }"
| "simplify_emp_main (D,Var x,C,t,[]) solved = Some (Some (D,Var x,C,t,solved))" 
| "simplify_emp_main (More f bef D aft,Fun g ls,C,t,[]) solved = do {
    guard (f = g);
    guard (length ls = Suc (length bef + length aft));
    let pairs_bef = zip bef (take (length bef) ls);
    let pairs_aft = zip aft (drop (Suc (length bef)) ls);
    simplify_emp_main (D,ls ! length bef,C,t,(pairs_bef @ pairs_aft)) solved
  }" 
| "simplify_emp_main (\<box>,Fun g ls,C,t,[]) solved = do {
       if gmatch_decision \<mu>_incr ((t,Fun g ls) # solved)
          then Some None
          else if C = \<box> then None 
          else simplify_emp_main (C,Fun g ls,C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, []) solved
    }"  
  by pat_completeness auto

(* Thm 3, (iv) *)
termination
proof -
  let ?f = "\<lambda> (t,l). v_incr_measure \<mu> t"
  let ?R = "measures [\<lambda> ((D,l,C,t,mp),sp). size l + size_list size (map snd mp), 
                      \<lambda>((D,l,C,t,mp),sp). size_list ?f mp,
                      \<lambda>((D,l,C,t,mp),sp). if D = \<box> then 1 else 0]"
  show ?thesis
  proof 
    fix s x D C l t mp solved
    show "(((D,l,C,t,mp),(s,Var x) # solved), (D,l,C,t,(s, Var x) # mp), solved) \<in> ?R"
      by (rule measures_less, simp_all add: o_def)
  next
    fix f g ls ts mp solved pairs D C l t
    show "f = g \<Longrightarrow> zip_option ts ls = Some pairs \<Longrightarrow> ( ((D,l,C,t,pairs @ mp), solved), ((D,l,C,t,(Fun g ts, Fun f ls) # mp), solved)) \<in> ?R"
      by (intro measures_less) (insert zip_size_aux[of ts ls], auto simp: o_def)
  next
    fix x f and ls :: "('f,'v)term list" and mp solved :: "('f,'v)gmatch_prob"
      and mu :: "('f,'v)gmatch_prob \<Rightarrow> ('f,'v)gmatch_prob"
      and l :: "('f,'v)term"
      and D C t
    assume x: "x \<in> V_sincr" and mu: "mu = map (\<lambda>(s,y). (s \<cdot> \<mu>, y))"
    from x have x: "x \<in> V_incr" by simp
    let ?mu = "(\<lambda>(s,y). (s \<cdot> \<mu>, y))"
    have id: "size o snd o ?mu = size o snd"
      by (intro ext, auto)
    from v_incr_measure_less[OF x]
    have one: "?f (?mu (Var x, Fun f ls)) < ?f ((Var x, Fun f ls))" by simp
    have two: "size_list ?f (map ?mu mp) \<le> size_list ?f mp"
      unfolding size_list_map
      by (rule size_list_pointwise, force)
    from one two 
    have main: "size_list ?f (map ?mu ((Var x, Fun f ls) # mp)) < size_list ?f ((Var x, Fun f ls) # mp)" 
      by auto
    have [simp]: "\<And> x. snd (case x of (s, x) \<Rightarrow> (s \<cdot> \<mu>, x)) = snd x" by (case_tac x, auto)
    show "(((D \<cdot>\<^sub>c \<mu>,l,C \<cdot>\<^sub>c \<mu>,t \<cdot> \<mu>,(mu ((Var x, Fun f ls) # mp))), mu solved), ((D,l,C,t,(Var x, Fun f ls) # mp), solved)) \<in> ?R" unfolding mu
      by (rule measures_lesseq[OF _ measures_less], simp add: id, insert main, auto simp: o_def)
  next
    fix f and bef aft :: "('f,'v)term list" and mp1 mp2 solved :: "('f,'v)gmatch_prob"
      and ls :: "('f,'v)term list" and g
      and D C :: "('f,'v)ctxt"
      and t :: "('f,'v)term"
    let ?n = "length bef"
    let ?bef = "take ?n ls"
    let ?aft = "drop (Suc ?n) ls"
    assume len: "length ls = Suc (length bef + length aft)"
      and mp1: "mp1 = zip bef ?bef"
      and mp2: "mp2 = zip aft (drop (Suc (length bef)) ls)"
    from len have len1: "length bef = length ?bef" by auto
    from len have len2: "length aft = length ?aft" by auto
    have n: "?n < length ls" unfolding len by simp
    let ?l = "size (ls ! length bef) + size_list (size o snd) mp1 + size_list (size o snd) mp2"
    have "?l < size_list size (?bef @ ls ! length bef # ?aft)" 
      unfolding mp1 mp2 size_list_map[symmetric] 
      unfolding map_snd_zip[OF len1]
      unfolding map_snd_zip[OF len2]
      by simp
    also have "... = size_list size ls" 
      unfolding id_take_nth_drop[symmetric, OF n] ..
    finally have less: "?l < size_list size ls" .
    show "(((D, ls ! length bef, C, t, mp1 @ mp2),solved), 
           (More f bef D aft, Fun g ls, C, t, []), solved) \<in> ?R"
      by (rule measures_less, insert less, simp) 
  next
    fix g ls C t solved 
    show "C \<noteq> \<box> \<Longrightarrow> (((C, Fun g ls, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, []),solved), 
           (\<box>, Fun g ls, C, t, []),solved) \<in> ?R"
      by (intro measures_lesseq[OF _ measures_lesseq[OF _ measures_less]], auto)
  qed simp
qed

lemma simplify_emp_main_solved_form:
  assumes res: "simplify_emp_main mp1 mp2 = Some (Some mp3)" 
    and sf: "gmatch_solved_form mp2"
  shows "egmatch_solved_form mp3"
proof -
  let ?P = "\<lambda> mp1 mp2. \<forall> mp3. simplify_emp_main mp1 mp2 = Some (Some mp3) \<longrightarrow> gmatch_solved_form mp2 \<longrightarrow> egmatch_solved_form mp3"
  note g = gmatch_solved_form_def
  show ?thesis
  proof (induct rule: simplify_emp_main.induct[of ?P,rule_format, OF _ _ _ _ _ _ res sf])
    case (1 D l C t s x mp solved mp3)
    show ?case 
      by (rule 1(1), insert 1(2) 1(3), auto simp: g)
  next
    case (2 D l C t g ts f ls mp solved mp3)
    note res = 2(2)[simplified, unfolded guard_simps Let_def] 
    from res have fg: "f = g" by (auto simp: bind_eq_Some_conv)
    from res obtain z where z: "zip_option ts ls = Some z" by (auto simp: bind_eq_Some_conv)
    note IH = 2(1)[OF fg this _ 2(3)]
    show ?case
      by (rule IH, insert res z, auto simp: bind_eq_Some_conv)
  next
    case (3 D C t x f ls mp solved mp2 mp3)
    note res = 3(2)[simplified, unfolded Let_def] 
    from res have f: "f \<in> V_sincr" by (simp add: guard_simps bind_eq_Some_conv)
    note IH = 3(1)[OF f refl]
    show ?case
      by (rule IH, insert res 3(3), auto simp: g bind_eq_Some_conv)
  next
    case (4 D x C t solved mp3)
    then show ?case unfolding egmatch_solved_form_def by auto
  next
    case (5 f bef D aft g ls C t solved mp3)
    note res = 5(2)[simplified, unfolded Let_def guard_simps] 
    from res have f: "f = g" "length ls = Suc (length bef + length aft)" by (auto simp: bind_eq_Some_conv)
    note IH = 5(1)[OF this _ _ _ 5(3)]
    show ?case
      by (rule IH, insert res, auto simp: bind_eq_Some_conv)
  next
    case (6 g ls C t solved mp3)
    note res = 6(2)[unfolded simplify_emp_main.simps Let_def]
    let ?sol = "gmatch_decision \<mu>_incr ((t, Fun g ls) # solved)"
    from res have nsol: "\<not> ?sol" by (cases ?sol, auto)
    from res nsol have C: "C \<noteq> \<box>" by (cases C, auto)
    show ?case
      by (rule 6(1)[OF nsol C _ 6(3)], insert res nsol C, auto)
  qed
qed

(* Thm 3: simplifying extended matching problems does not change satisfiability *)
lemma simplify_emp_main_solution:
  assumes C: "(C::('f, 'v) ctxt) \<noteq> \<box>"
    and res: "simplify_emp_main (D,l,C,t,mp1) mp2 = mp3"
  shows "(mp3 = None \<longrightarrow> \<not> (\<exists> sol. egmatch_solution (D,l,C,t,mp1 @ mp2) sol)) 
       \<and> (mp3 = Some None \<longrightarrow> (\<exists> sol. egmatch_solution (D,l,C,t,mp1 @ mp2) sol)) 
       \<and> (\<forall> mp3'. mp3 = Some (Some mp3') \<longrightarrow> 
         (\<lambda> (_,_,C,_,_). C) mp3' \<noteq> \<box> \<and> (\<exists> sol. egmatch_solution (D,l,C,t,mp1 @ mp2) sol) = (\<exists> sol. egmatch_solution mp3' sol))"
proof -
  note d = egmatch_solution_def gmatch_solution_def match_solution_def
  let ?cmu = "\<lambda> C. ctxt_subst C \<mu>"
  let ?sole = "\<lambda> (D,l,C,t,mp) n k \<sigma>. D\<langle>?cmu C n t\<rangle> \<cdot> (\<mu> ^^ k) = l \<cdot> \<sigma>"
  let ?solm = "\<lambda> mp k (\<sigma> :: ('f,'v)subst). (\<forall> (s,l) \<in> mp. s \<cdot> \<mu> ^^ k = l \<cdot> \<sigma>)"
  {
    fix k g and ts ls :: "('f,'v)term list" and \<sigma> :: "('f,'v)subst"
    assume len: "length ts = length ls"
    then have len: "length ts = length (map (\<lambda> t. t \<cdot> \<sigma>) ls)" by simp
    let ?l = "?solm {(Fun g ts, Fun g ls)} k \<sigma>"
    let ?r = "?solm (set (zip ts ls)) k \<sigma>"
    have "?l = (Fun g ts \<cdot> (\<mu> ^^ k) = Fun g ls \<cdot> \<sigma>)" by auto
    also have "... = ?r"
      unfolding set_zip eval_term.simps term.simps
      unfolding map_nth_eq_conv[OF len]
      by (insert len, auto)
    finally have "?r = ?l" by simp
  } note solm_zip = this
  obtain solm where solm: "solm \<equiv> ?solm" by blast
  let ?solem = "\<lambda> (D,l,C,t,mp1) mp2 k \<sigma>. solm (set mp1 \<union> set mp2) k \<sigma>"
  let ?sol = "\<lambda> emp mp n k \<sigma>. ?sole emp n k \<sigma> \<and> ?solem emp mp k \<sigma>"
  let ?C = "\<lambda> (_,_,C,_,_). C \<noteq> \<box>"
  let ?esol = "\<lambda> emp mp. \<exists> n k \<sigma>. ?sol emp mp n k (\<sigma> :: ('f,'v)subst)"
  obtain esol where esol: "esol \<equiv> ?esol" by blast
  let ?esolm = "\<lambda> mp. \<exists> n \<sigma>. ?solm mp n \<sigma>"
  let ?fail = "\<lambda> emp mp res. res = None \<longrightarrow> \<not> esol emp mp"
  let ?succ = "\<lambda> emp mp res. res = Some None \<longrightarrow> esol emp mp"
  let ?maybe = "\<lambda> emp mp res. (\<forall> emp'. res = Some (Some emp') \<longrightarrow> ?C emp' \<and> esol emp mp = esol emp' [])"
  let ?all = "\<lambda> emp mp res. ?fail emp mp res \<and> ?succ emp mp res \<and> ?maybe emp mp res"
  let ?res = "\<lambda> emp mp res. simplify_emp_main emp mp = res \<and> ?C emp"
  let ?P = "\<lambda> emp mp. (\<forall> res. ?res emp mp res \<longrightarrow> ?all emp mp res)"
  {
    fix emp mp res
    assume res: "?res emp mp res"
    have "?all emp mp res" 
    proof (induct rule: simplify_emp_main.induct[of ?P, rule_format, OF _ _ _ _ _ _ res])
      case (1 D l C t s x mp solved res)
      from 1(2) have res: "simplify_emp_main (D,l,C,t,mp) ((s,Var x) # solved) = res \<and> C \<noteq> \<box>" by simp
      show ?case using 1(1)[unfolded split, OF res] unfolding esol by auto
    next
      case (2 D l C t g ts f ls mp solved res)
      note res = 2(2)[simplified]
      let ?mp = "(D,l,C,t,(Fun g ts, Fun f ls) # mp)"
      show ?case
      proof (cases "f = g \<and> length ts = length ls")
        case False 
        {
          fix n k \<sigma>
          assume "?sol ?mp solved n k \<sigma>"
          then have fg: "f = g" and len: "map (\<lambda> t. t \<cdot> \<mu> ^^ k) ts = map (\<lambda> t. t \<cdot> \<sigma>) ls"
            unfolding solm by auto
          from arg_cong[OF len, of length] fg False have False by simp
        }
        then have esol: "\<not> esol ?mp solved" unfolding esol by blast
        have res: "res = None"
        proof (cases "f = g")
          case False
          with res show ?thesis by (simp add: guard_simps) 
        next
          case True
          with False have "length ls \<noteq> length ts" by simp
          with zip_option_zip_conv[of ts ls] res 
          show ?thesis by (cases "zip_option ts ls", auto)
        qed          
        with esol show ?thesis by simp
      next
        case True
        then have id: "f = g" and len: "length ts = length ls" by auto
        have zip: "zip_option ts ls = Some (zip ts ls)" using len by auto
        let ?res = "(D,l,C,t,zip ts ls @ mp)"
        from res have res: "res = simplify_emp_main ?res solved" unfolding id zip by simp
        from 2(2) have C: "C \<noteq> \<box>" by simp
        note IH = 2(1)[OF id zip, unfolded split, OF conjI[OF res[symmetric] C]]
        {
          fix n k \<sigma>
          have "solm (set (zip ts ls)) k \<sigma> = solm {(Fun g ts, Fun f ls)} k \<sigma>"
            unfolding solm id using solm_zip[OF len] by simp
          then have "?sol ?mp solved n k \<sigma> = ?sol ?res solved n k \<sigma>" unfolding split
            unfolding id solm by auto
        }
        then have id: "esol ?mp solved = esol ?res solved" unfolding esol split by blast
        show ?thesis using IH unfolding id .
      qed                
    next
      case (3 D l C t x f ls mp solved res)
      note res = 3(2)[simplified, unfolded Let_def]
      let ?mp = "(D,l,C,t,(Var x, Fun f ls) # mp)"
      show ?case 
      proof (cases "x \<in> V_incr")
        case False
        with res have res: "res = None" by (simp add: guard_simps)
        have "\<not> esol ?mp solved" 
        proof
          assume "esol ?mp solved"
          from this[unfolded esol solm split] obtain k \<sigma> where "Var x \<cdot> \<mu> ^^ k = (Fun f ls) \<cdot> \<sigma>" by auto
          then have "is_Fun (Var x \<cdot> \<mu> ^^ k)" by simp
          with False show False by blast
        qed          
        with res show ?thesis by simp
      next
        case True
        then have x: "x \<in> V_sincr" by simp
        let ?mu = "(\<lambda>(s,y). (s \<cdot> \<mu>, y))"
        from res True have res: "res = simplify_emp_main (D \<cdot>\<^sub>c \<mu>, l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, map ?mu ((Var x, Fun f ls) # mp)) (map ?mu solved)" (is "_ = simplify_emp_main ?res ?solved") by (simp add: guard_simps)
        from 3(2) have C: "C \<cdot>\<^sub>c \<mu> \<noteq> \<box>" by (cases C, auto)
        note IH = 3(1)[OF x refl, unfolded split, OF conjI[OF res[symmetric] C]]
        {
          fix n k \<sigma>
          have "?sol ?res ?solved n k \<sigma> = ?sol ?mp solved n (Suc k) \<sigma>"
            unfolding split solm
            by (auto simp: ctxt_subst_subst)
        } note id = this
        have id: "esol ?mp solved = esol ?res ?solved"           
        proof
          assume "esol ?mp solved"
          then obtain n k \<sigma> where sol: "?sol ?mp solved n k \<sigma>" unfolding esol by blast
          {
            assume "k = 0"
            with sol have False unfolding solm by auto
          }
          then obtain kk where k: "k = Suc kk" by (cases k, auto)
          from sol have "?sol ?res ?solved n kk \<sigma>" unfolding id k .
          then show "esol ?res ?solved" unfolding esol by blast
        next
          assume "esol ?res ?solved"
          then obtain n k \<sigma> where sol: "?sol ?res ?solved n k \<sigma>" unfolding esol by blast
          then have "?sol ?mp solved n (Suc k) \<sigma>" unfolding id .
          then show "esol ?mp solved" unfolding esol by blast
        qed
        show ?thesis unfolding id by (rule IH)
      qed
    next
      case (4 D x C t solved res)
      then have res: "res = Some (Some (D,Var x,C,t,solved))" by simp
      show ?case unfolding res esol using 4 by force
    next
      case (5 f bef D aft g ls C t solved res)      
      let ?mp = "(More f bef D aft, Fun g ls, C, t, [])"
      let ?n = "length bef"
      let ?m = "Suc (?n + length aft)"
      note res = 5(2)[simplified]
      show ?case
      proof (cases "f = g \<and> length ls = ?m")
        case False 
        {
          fix n k \<sigma>
          assume sol: "?sol ?mp solved n k \<sigma>"
          then
          obtain h1 h2 and h3 :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
            where fg: "f = g" and len: "map h1 bef @ h2 # map h1 aft = map h3 ls" by force
          from arg_cong[OF len, of length] fg False have False by simp
        }
        then have esol: "\<not> esol ?mp solved" unfolding esol by blast
        have res: "res = None"
        proof (cases "f = g")
          case False
          with res show ?thesis by (simp add: guard_simps) 
        next
          case True
          with False have "length ls \<noteq> ?m" by simp
          with True res show ?thesis by simp
        qed          
        with esol show ?thesis by simp
      next
        case True
        then have id: "f = g" and len: "length ls = ?m" by auto
        note res = res[unfolded id len, simplified]
        let ?bef = "take ?n ls"
        let ?aft = "drop (Suc ?n) ls"
        let ?zbef = "zip bef ?bef"
        let ?zaft = "zip aft ?aft"
        let ?res = "(D,ls ! ?n,C,t,?zbef @ ?zaft)"
        from res have res: "res = simplify_emp_main ?res solved" unfolding id  by simp
        from 5(2) have C: "C \<noteq> \<box>" by simp
        note IH = 5(1)[OF id len refl refl, unfolded split, OF conjI[OF res[symmetric] C]]
        {
          fix n k and \<sigma> :: "('f,'v)subst"
          have "?n < length ls" using len by simp
          from id_take_nth_drop[OF this]
          have ls: "Fun g ls = Fun g (?bef @ ls ! ?n # ?aft)" by simp          
          let ?befm = "map (\<lambda> t. t \<cdot> \<mu> ^^ k) bef"
          let ?aftm = "map (\<lambda> t. t \<cdot> \<mu> ^^ k) aft"
          let ?befs = "map (\<lambda> t. t \<cdot> \<sigma>) ?bef"
          let ?afts = "map (\<lambda> t. t \<cdot> \<sigma>) ?aft"
          have lenb: "length ?befm = length ?befs" "length bef = length ?befs"
            using len by auto
          have lena: "length aft = length ?afts"
            using len by auto
          note app_conv = List.append_eq_append_conv[OF disjI1[OF lenb(1)]]
          have left: "?sole ?mp n k \<sigma> = (?befm = ?befs \<and> ?sole ?res n k \<sigma> \<and> ?aftm = ?afts)"
            unfolding split 
            unfolding id ls 
            by (simp add: app_conv) 
          have right: "?sol ?res [] n k \<sigma> = (?solm (set ?zbef) k \<sigma> \<and> ?sole ?res n k \<sigma> \<and> ?solm (set ?zaft) k \<sigma>)" unfolding split solm
            by auto
          have bef: "(?befm = ?befs) = (?solm (set ?zbef) k \<sigma>)"
            unfolding set_zip map_nth_eq_conv[OF lenb(2)]
            using lenb by force
          have aft: "(?aftm = ?afts) = (?solm (set ?zaft) k \<sigma>)"
            unfolding set_zip map_nth_eq_conv[OF lena]
            using lena by force
          have "?sole ?mp n k \<sigma> = ?sol ?res [] n k \<sigma>" unfolding left right bef aft ..
          then have "?sol ?mp solved n k \<sigma> = ?sol ?res solved n k \<sigma>" unfolding split
            unfolding id solm by auto
        }
        then have id: "esol ?mp solved = esol ?res solved" unfolding esol split by blast
        show ?thesis using IH unfolding id .
      qed                
    next
      case (6 g ls C t solved res)
      note res = 6(2)[unfolded simplify_emp_main.simps]        
      let ?mp = "(\<box>, Fun g ls, C, t, [])"
      let ?pair = "(t, Fun g ls)"
      let ?M = "?pair # solved"
      let ?res = "(C,Fun g ls, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, [])"
      {
        fix k \<sigma>
        have "gmatch_solution ?M (k,\<sigma>) = ?sol ?mp solved 0 k \<sigma>"
          unfolding d solm split
          by auto
      } note 0 = this
      {
        fix n k \<sigma>
        have "?sol ?res solved n k \<sigma> = ?sol ?mp solved (Suc n) k \<sigma>"
          unfolding split by (simp add: ctxt_subst_subst)
      } note Suc = this
      show ?case
      proof (cases "gmatch_decision \<mu>_incr (?pair # solved)")
        case True
        then obtain k \<sigma> where sol: "gmatch_solution ?M (k,\<sigma>)" by force
        with 0 have "?sol ?mp solved 0 k \<sigma>" by simp
        then have sol: "esol ?mp solved" unfolding esol by blast
        from res True have res: "res = Some None" by simp
        from res sol show ?thesis by simp
      next
        case False
        from 6(2) have C: "C \<noteq> \<box>" by simp
        from False res C have res: "res = simplify_emp_main ?res solved" by simp
        from C have Cmu: "C \<cdot>\<^sub>c \<mu> \<noteq> \<box>" by (cases C, auto)
        note IH = 6(1)[OF False C, unfolded split, OF conjI[OF res[symmetric] Cmu]]
        have id: "esol ?mp solved = esol ?res solved" 
        proof
          assume "esol ?mp solved"
          then obtain n k \<sigma> where sol: "?sol ?mp solved n k \<sigma>" unfolding esol by blast
          {
            assume n: "n = 0"
            have "gmatch_solution ?M (k,\<sigma>)" unfolding 0 
              using sol n by simp
            with False have False by simp
          }
          then obtain nn where n: "n = Suc nn" by (cases n, auto)
          from sol have "?sol ?res solved nn k \<sigma>" unfolding Suc n .
          then show "esol ?res solved" unfolding esol by blast
        next
          assume "esol ?res solved"
          then obtain n k \<sigma> where sol: "?sol ?res solved n k \<sigma>" unfolding esol by blast
          then have "?sol ?mp solved (Suc n) k \<sigma>" unfolding Suc .
          then show "esol ?mp solved" unfolding esol by blast
        qed
        show ?thesis using IH unfolding id .
      qed
    qed
  }
  note main = this
  note d = egmatch_solution_def gmatch_solution_def match_solution_def esol solm
  have id: "(\<exists> sol. egmatch_solution (D,l,C,t,mp1 @ mp2) sol) = (esol (D,l,C,t,mp1) mp2)"
    unfolding d by force
  {
    fix emp'      
    have "(\<exists> sol. egmatch_solution emp' sol) = esol emp' []"
      unfolding d by (cases emp', auto)
  } note id2 = this
  from main[of "(D,l,C,t,mp1)" mp2 mp3, unfolded split, rule_format, OF conjI[OF res C]]
  show ?thesis unfolding id id2 
    unfolding esol by force
qed

(* wrapper which calls main simplification method with right starting values *)
definition simplify_emp :: "('f, 'v) ematch_prob \<Rightarrow> ('f, 'v) egmatch_prob + bool" where
  "simplify_emp emp \<equiv> case emp of (D, l, C, t) \<Rightarrow>
    (case simplify_emp_main (D, l, C, t, []) [] of 
      None \<Rightarrow> Inr False
    | Some None \<Rightarrow> Inr True
    | Some (Some emp) \<Rightarrow> Inl emp)"

(* main soundness result for simplification of extended matching problems:
   either we get already an answer, or we get a equisatisfiable problem which
   is in solved form *)
lemma simplify_emp: 
  assumes C: "C \<noteq> \<box>"
    and res: "simplify_emp (D, l, C, t) = res"
  shows "(res = Inr b \<longrightarrow> (\<exists>sol. ematch_solution (D, l, C, t) sol) = b) \<and> 
         (res = Inl emp' \<longrightarrow> 
              (\<exists>sol. ematch_solution (D, l, C, t) sol) = (\<exists>sol. egmatch_solution emp' sol)
            \<and> (\<lambda> (_,_,C',_,_). C') emp' \<noteq> \<box>
            \<and> egmatch_solved_form emp'
)" 
proof -
  let ?mp = "(D,l,C,t,[])"
  let ?s = "simplify_emp_main ?mp []"
  from res[unfolded simplify_emp_def split]
  have res: "res = (case ?s of None \<Rightarrow> Inr False | Some None \<Rightarrow> Inr True | Some (Some emp') \<Rightarrow> Inl emp')" by simp
  have id: "(\<exists> sol. ematch_solution (D,l,C,t) sol) = (\<exists> sol. egmatch_solution ?mp sol)"
    unfolding ematch_solution_def egmatch_solution_def gmatch_solution_def by auto
  note main = simplify_emp_main_solution[OF C, of D l t Nil Nil]
  show ?thesis
  proof (cases ?s)
    case None
    from main[OF None] res[unfolded None] show ?thesis unfolding id by auto
  next
    case (Some empo) note oSome = this
    note main = main[OF Some]
    note res = res[unfolded Some]
    show ?thesis 
    proof (cases empo)
      case None
      from main[unfolded None] res[unfolded None] show ?thesis unfolding id by auto
    next
      case (Some emp)
      from Some res have res: "res = Inl emp" by simp
      note main = main[unfolded Some]
      show ?thesis 
      proof (cases "emp = emp'")
        case False with res show ?thesis by simp
      next
        case True
        note res = res[unfolded True]
        note main = main[unfolded True]
        from simplify_emp_main_solved_form[OF oSome[unfolded Some True]]
        have "egmatch_solved_form emp'" unfolding gmatch_solved_form_def by simp
        with main show ?thesis unfolding res id by simp
      qed
    qed
  qed
qed

(* result for getting rid of extended identity problems: 
  if we start with a large context C, such that C = E \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu> ^^ i), 
  then we will get a large context C' afterwards (in comparison to the terms in mp') *)
lemma simplify_emp_main_large_C: 
  defines largeCs: "largeCs \<equiv> \<lambda>(C::('f, 'v) ctxt) (s::('f, 'v) term). \<exists>i. C \<rhd>c s \<cdot> \<mu> ^^ i"
  defines largeCD: "largeCD \<equiv> \<lambda>(C::('f, 'v) ctxt) D. \<exists>i E. C = E \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu> ^^ i)"
  assumes large: "largeCD C D"
    and res: "simplify_emp_main (D,l,C,t,[]) [] = Some (Some (D',l',C',t',mp'))"
  shows "\<forall>s' \<in> fst ` set mp'. largeCs C' s'"
proof -
  {
    fix C s
    assume "largeCs C s"    
    from this[unfolded largeCs] obtain i 
      where large: "C \<rhd>c s \<cdot> \<mu> ^^ i" by auto
    note large = suptc_subst[OF large, of \<mu>]
    have "largeCs (C \<cdot>\<^sub>c \<mu>) (s \<cdot> \<mu>)" unfolding largeCs
    proof (rule exI[of _ i])
      have id: "s \<cdot> \<mu> ^^ i \<cdot> \<mu> = s \<cdot> \<mu> ^^ Suc i" unfolding subst_power_Suc by simp
      show "C \<cdot>\<^sub>c \<mu> \<rhd>c s \<cdot> \<mu> \<cdot> \<mu> ^^ i" using large unfolding id by simp
    qed
  } note largeCs_subst = this
  {
    fix C s
    assume "largeCs C s"  
    then obtain i where supt: "C \<rhd>c s \<cdot> \<mu> ^^ i" unfolding largeCs by auto
    have id: "s \<cdot> \<mu> ^^ (Suc i) = s \<cdot> \<mu> ^^ i \<cdot> \<mu>" unfolding subst_power_Suc by simp
    have "largeCs (C \<cdot>\<^sub>c \<mu>) s" unfolding largeCs
      by (rule exI[of _ "Suc i"], unfold id, rule suptc_subst[OF supt])
  } note largeCs_left_subst = this
  {
    fix C D
    assume "largeCD C D"
    from this[unfolded largeCD]
    obtain i E where C: "C = E \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu> ^^ i)" by auto
    have id: "\<mu> \<circ>\<^sub>s \<mu> ^^ i = \<mu> ^^ i \<circ>\<^sub>s \<mu>"
      unfolding subst_power_Suc[symmetric] by simp
    have "largeCD (C \<cdot>\<^sub>c \<mu>) (D \<cdot>\<^sub>c \<mu>)" unfolding largeCD      
      apply (rule exI[of _ i], rule exI[of _ "E \<cdot>\<^sub>c \<mu>"], unfold C
        ctxt_compose_subst_compose_distrib[symmetric] id)
      by (simp add: eval_subst_ctxt)
  } note largeCD_subst = this
  {
    fix C
    have "largeCD (C \<cdot>\<^sub>c \<mu>) C" unfolding largeCD
      by (rule exI[of _ "Suc 0"], rule exI[of _ \<box>], auto)
  } note largeCD_left_subst = this
  let ?lCD = "\<lambda> emp. case emp of (D,l,C,t,mp) \<Rightarrow> largeCD C D"
  let ?lCms = "\<lambda> C ms. \<forall> s \<in> fst ` ms. largeCs C s"
  let ?lCmp = "\<lambda> (emp :: ('f,'v)egmatch_prob) (solved :: ('f,'v)gmatch_prob). case emp of (D,l,C,t,mp) \<Rightarrow> ?lCms C (set mp \<union> set solved)"
  let ?P = "\<lambda> emp solved. ?lCD emp \<and> ?lCmp emp solved \<longrightarrow> (\<forall> (emp' :: ('f,'v)egmatch_prob). simplify_emp_main emp solved = Some (Some emp') \<longrightarrow> ?lCmp emp' [])"
  let ?emp = "(D,l,C,t,[]) :: ('f,'v)egmatch_prob" 
  let ?res = "(D',l',C',t',mp') :: ('f,'v)egmatch_prob"
  have large: "?lCD ?emp \<and> ?lCmp ?emp []" using large unfolding split largeCD
    by simp
  have "?lCmp ?res []"
  proof (induct rule: simplify_emp_main.induct[of ?P, rule_format, OF _ _ _ _ _ _ large res])
    case (1 D l C t s x mp solved mp3)
    show ?case 
      by (rule 1(1), insert 1(2) 1(3), auto)
  next
    case (2 D l C t g ts f ls mp solved mp3)
    from 2(2) have lCD: "largeCD C D" and lCm: "?lCms C (set mp \<union> set solved)" and lCs: "largeCs C (Fun g ts)" by auto
    note res = 2(3)[simplified, unfolded guard_simps Let_def] 
    from res have fg: "f = g" by (auto simp add: bind_eq_Some_conv)
    from res obtain z where z: "zip_option ts ls = Some z" by (auto simp: bind_eq_Some_conv)
    note IH = 2(1)[OF fg this, unfolded split]
    from res[unfolded z] have "simplify_emp_main (D,l,C,t,z @ mp) solved = Some (Some mp3)" by (simp add: bind_eq_Some_conv)
    note IH = IH[OF _ this]
    show ?case
    proof (rule IH, rule conjI[OF lCD], intro ballI)
      fix s
      assume s: "s \<in> fst ` (set (z @ mp) \<union> set solved)"
      then have "s \<in> fst ` set z \<or> s \<in> fst ` (set mp \<union> set solved)" by auto
      then show "largeCs C s"
      proof 
        assume "s \<in> fst ` (set mp \<union> set solved)"
        then show ?thesis using lCm by auto
      next
        assume mem: "s \<in> fst ` (set z)"
        from zip_option_zip_conv[of ts ls z, unfolded z]
        have len: "length ls = length ts" and z: "z = zip ts ls" by auto
        from mem[unfolded z set_zip len] obtain i where "i < length ts"
          and "s = ts ! i" by auto
        then have "s \<in> set ts" by auto
        then have supteq: "Fun g ts \<unrhd> s" by auto        
        from lCs[unfolded largeCs] obtain i where supt: "C \<rhd>c Fun g ts \<cdot> \<mu> ^^ i" by auto
        show ?thesis unfolding largeCs
          by (rule exI[of _ i], rule suptc_supteq_trans[OF supt supteq_subst[OF supteq]])
      qed
    qed
  next
    case (3 D l C t x f ls mp solved mp3)
    note res = 3(3)[simplified, unfolded Let_def guard_simps]
    let ?pairs = "(Var x, Fun f ls) # mp"
    let ?mp = "(D,l,C,t,?pairs)"
    let ?mu = "(\<lambda>(s,y). (s \<cdot> \<mu>, y))"
    let ?mp' = "(D \<cdot>\<^sub>c \<mu>, l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, map ?mu ?pairs)"
    let ?solved = "map ?mu solved"
    from res have x: "x \<in> V_sincr" and res: "simplify_emp_main ?mp' ?solved = Some (Some mp3)"
      by (auto simp: bind_eq_Some_conv)
    note large = 3(2)[unfolded split]
    note IH = 3(1)[OF x refl _ res, unfolded split]
    obtain list where list: "list = ?pairs @ solved" by auto
    show ?case
    proof (rule IH, intro conjI ballI)
      show "largeCD (C \<cdot>\<^sub>c \<mu>) (D \<cdot>\<^sub>c \<mu>)"
        by (rule largeCD_subst, insert large, simp)
    next
      fix s
      assume "s \<in> fst ` (set (map ?mu ?pairs) \<union> set (map ?mu solved))"
      then have "s \<in> fst ` (set (map ?mu list))" unfolding list by auto
      then obtain ss where s: "s = ss \<cdot> \<mu>" and ss: "ss \<in> fst ` (set list)" by force
      from large ss have large: "largeCs C ss" unfolding list by auto
      show "largeCs (C \<cdot>\<^sub>c \<mu>) s" unfolding s
        by (rule largeCs_subst[OF large])
    qed
  next
    case (4 D x C t solved mp3)
    then have "mp3 = (D, Var x, C, t, solved)" by simp
    with 4 show ?case by simp
  next
    case (5 f bef D aft g ls C t solved mp3)
    note res = 5(3)[simplified, unfolded Let_def guard_simps] 
    let ?n = "length bef"
    let ?bef = "take ?n ls"
    let ?aft = "drop (Suc ?n) ls"
    let ?zbef = "zip bef ?bef"
    let ?zaft = "zip aft ?aft"
    let ?z = "?zbef @ ?zaft"
    from res have result: "simplify_emp_main (D, ls ! length bef, C, t, ?z) solved =
    Some (Some mp3)" by (simp split: bind_splits)
    from res have f: "f = g" and len: "length ls = Suc (length bef + length aft)"
      by (auto split: bind_splits)
    note IH = 5(1)[OF this refl refl]
    note large = 5(2)[unfolded split]
    let ?C = "More f bef D aft"
    from large have "largeCD C ?C" by simp
    then obtain i E where C: "C = E \<circ>\<^sub>c (?C \<cdot>\<^sub>c \<mu> ^^ i)" unfolding largeCD by auto
    let ?m = "map (\<lambda> t. t \<cdot> \<mu> ^^ i)"
    have largeCD: "largeCD C D" unfolding largeCD C
      by (rule exI[of _ i], rule exI[of _ "E \<circ>\<^sub>c (More f (?m bef) \<box> (?m aft))"], auto simp: ac_simps)
    {
      fix s
      assume "s \<in> fst ` set ?z"
      then have s: "s \<in> set (map fst ?zbef) \<union> set (map fst ?zaft)" by auto
      from len have lbef: "length bef = length ?bef" by simp
      from len have laft: "length aft = length ?aft" by simp
      from s[unfolded map_fst_zip[OF lbef] map_fst_zip[OF laft]]
      have s: "s \<in> set bef \<union> set aft" .
      have "largeCs C s" unfolding largeCs
      proof (rule exI[of _ i])    
        let ?m = "map (\<lambda> t. t \<cdot> \<mu> ^^ i)"
        from s have mem: "s \<cdot> \<mu> ^^ i \<in> set (?m bef) \<union> set (?m aft)" by auto
        have id: "?C \<cdot>\<^sub>c \<mu> ^^ i = More f (?m bef) (D \<cdot>\<^sub>c \<mu> ^^ i) (?m aft)" by auto
        have supt: "?C \<cdot>\<^sub>c \<mu> ^^ i \<rhd>c s \<cdot> \<mu> ^^ i" unfolding id
          by (rule suptc.arg[OF mem], auto)
        show "C \<rhd>c s \<cdot> \<mu> ^^ i" unfolding C using supt
          by (rule supteq_suptc_trans[OF refl])
      qed
    } note main = this
    show ?case
      by (rule IH, unfold split, rule conjI[OF largeCD],
        insert main res large, auto split: bind_splits)
  next
    case (6 g ls C t solved mp3)
    note res = 6(3)[unfolded simplify_emp_main.simps Let_def]
    let ?sol = "gmatch_decision \<mu>_incr ((t, Fun g ls) # solved)"
    from res have nsol: "\<not> ?sol" by (cases ?sol, auto)
    from res nsol have C: "C \<noteq> \<box>" by (cases C, auto)
    from res nsol C have res: "simplify_emp_main (C, Fun g ls, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>, []) solved = Some (Some mp3)" by simp
    note large =  6(2)[unfolded split]
    from large have large: "\<And> s. s \<in> fst ` set solved \<Longrightarrow> largeCs C s" by auto
    note IH = 6(1)[OF nsol C _ res]
    show ?case
    proof (rule IH, unfold split, intro conjI ballI)
      show "largeCD (C \<cdot>\<^sub>c \<mu>) C" by (rule largeCD_left_subst)
    next
      fix s
      assume "s \<in> fst ` (set [] \<union> set solved)"
      then have "s \<in> fst ` (set solved)" by auto
      from large[OF this] have "largeCs C s" .
      then show "largeCs (C \<cdot>\<^sub>c \<mu>) s" by (rule largeCs_left_subst)
    qed 
  qed
  then show ?thesis by auto
qed
end

declare fixed_subst_incr.simplify_emp_main.simps[code]
declare fixed_subst_incr.simplify_emp_def[code]

subsection \<open>From extended matching problems in solved form to (extended) identity problems\<close>

(* Reading of identity problems as in Thm 4 *)
fun ident_prob_of_semp :: "('f, 'v) egmatch_prob \<Rightarrow> ('f, 'v) ident_prob list" where
  "ident_prob_of_semp (D, l, C, t, mp) = ident_prob_of_smp mp"

fun eident_prob_of_semp :: "('f, 'v) egmatch_prob \<Rightarrow> ('f, 'v) eident_prob option" where
  "eident_prob_of_semp (D, l, C, t, mp) = do {
    si \<leftarrow> map_of (reverse_rules mp) l;
    Some (D, si, C, t)
  }"

(* Transforming extended identity problem into non-extended identity problem by fixing n = 0 *)
fun eident_prob_to_ident_prob :: "('f, 'v) eident_prob \<Rightarrow> ('f, 'v) ident_prob" where
  "eident_prob_to_ident_prob (D, si, C, t) = (D\<langle>t\<rangle>, si)"

context fixed_subst
begin

(* part of Thm 5 that extended matching problem in solved is solvable iff all resulting
  identity problems are solvable *)  
lemma ident_prob_of_semp_complete:
  assumes sol: "egmatch_solution semp (n,k,\<sigma>)"
    and mem: "idp \<in> set (ident_prob_of_semp semp)"
  shows "ident_solution idp k"
proof -
  obtain D l C t mp where semp: "semp = (D,l,C,t,mp)" by (cases semp, force)
  obtain a b where idp: "idp = (a,b)" by force
  show ?thesis unfolding idp
    by (rule ident_prob_of_smp_complete, insert mem sol semp, 
      unfold egmatch_solution_def idp, auto)
qed

(* another part of Thm 5 *)
lemma eident_prob_of_semp_complete:
  assumes sol: "egmatch_solution semp (n,k,\<sigma>)"
    and some: "eident_prob_of_semp semp = Some eidp"
  shows "eident_solution eidp (n,k)"
proof -
  obtain D l C t mp where semp: "semp = (D,l,C,t,mp)" by (cases semp, force)
  let ?m = "reverse_rules mp"
  from some[unfolded semp, simplified]
  obtain si where map_of: "map_of ?m l = Some si" and eidp: "eidp = (D,si,C,t)"
    by (cases "map_of ?m l", auto)
  from map_of_SomeD[OF map_of] have mem: "(si, l) \<in> set mp" by auto
  from sol[unfolded semp egmatch_solution_def split] 
  have l: "l \<cdot> \<sigma> = D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> \<mu> ^^ k" and sol: "gmatch_solution mp (k,\<sigma>)"
    by auto
  from sol[unfolded gmatch_solution_def match_solution_def] mem
  have l': "l \<cdot> \<sigma> = si \<cdot> \<mu> ^^ k" by auto
  show ?thesis unfolding eidp eident_solution_def split l[unfolded l'] ..
qed

(* another part of Thm 5 *)
lemma e_ident_prob_of_semp_sound: 
  assumes smp: "egmatch_solved_form semp"
    and sol: "\<And>idp. idp \<in> set (ident_prob_of_semp semp) \<Longrightarrow> \<exists>m\<le>k. ident_solution idp m"
    and esol: "\<And>eidp. eident_prob_of_semp semp = Some eidp \<Longrightarrow> \<exists>k'\<le>k. eident_solution eidp (n, k')" 
  shows "\<exists>\<sigma>. egmatch_solution semp (n, k, \<sigma>)"
proof -
  note d = gmatch_solution_def match_solution_def split
  obtain D l C t mp where semp: "semp = (D,l,C,t,mp)" by (cases semp, force)
  note smp = smp[unfolded semp egmatch_solved_form_def split]
  from smp obtain x where l: "l = Var x" and smp: "gmatch_solved_form mp" by auto
  from ident_prob_of_smp_sound[OF smp sol, unfolded semp]  
  obtain \<sigma> where sol: "gmatch_solution mp (k,\<sigma>)" by auto  
  note smp = smp[unfolded gmatch_solved_form_def]
  let ?m = "reverse_rules mp"
  show ?thesis
  proof (cases "map_of ?m l")
    case None
    let ?\<sigma> = "\<lambda> y. if x = y then D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> (\<mu> ^^ k) else \<sigma> y"
    show ?thesis unfolding semp egmatch_solution_def split
    proof (intro exI conjI)
      show "D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> \<mu> ^^ k = l \<cdot> ?\<sigma>" unfolding l by simp
    next
      {
        fix si l'
        assume mem: "(si,l') \<in> set mp"
        from smp[rule_format, OF mem] obtain y where l': "l' = Var y" by auto
        from None[unfolded map_of_eq_None_iff] and mem have neq: "y \<noteq> x" unfolding l l' by force
        have "si \<cdot> \<mu> ^^ k = l' \<cdot> \<sigma>" using mem sol unfolding d by auto
        also have "... = l' \<cdot> ?\<sigma>" unfolding l' using neq by simp
        finally have "si \<cdot> \<mu> ^^ k = l' \<cdot> ?\<sigma>" .
      }
      then show "gmatch_solution mp (k, ?\<sigma>)" unfolding d by auto
    qed
  next
    case (Some si)
    from esol[unfolded semp eident_prob_of_semp.simps Some]
    have "\<exists> k' \<le> k. eident_solution (D,si,C,t) (n,k')" by auto
    then obtain k' where k': "k' \<le> k" and esol: "eident_solution (D,si,C,t) (n,k')" 
      by auto
    note esol =  esol[unfolded eident_solution_def split]
    from k' have "k = k' + (k - k')" by simp
    then obtain k'' where k: "k = k' + k''" by auto
    from esol have esol: "D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> \<mu> ^^ k = si \<cdot> \<mu> ^^ k"
      unfolding k subst_power_compose_distrib by auto
    from map_of_SomeD[OF Some] have mem: "(si, Var x) \<in> set mp" unfolding l by auto
    with sol[unfolded d] have "si \<cdot> \<mu> ^^ k = \<sigma> x" by auto
    note esol = esol[unfolded this]
    show ?thesis
      unfolding semp egmatch_solution_def split
      by (intro exI conjI, rule sol, unfold esol l, simp)
  qed
qed

(* Thm 5: extended matching problem in solved is solvable 
  iff all resulting identity problems are solvable *)
lemma e_ident_prob_of_semp: 
  assumes smp: "egmatch_solved_form semp"
  shows "(\<exists>sol. egmatch_solution semp sol) = 
  ((\<forall>idp\<in>set (ident_prob_of_semp semp). (\<exists>sol. ident_solution idp sol)) \<and>
   (\<forall>eidp. eident_prob_of_semp semp = Some eidp \<longrightarrow> (\<exists>sol. eident_solution eidp sol)))"
  (is "?l = (?r1 \<and> ?r2)")
proof 
  assume ?l
  then obtain n k \<sigma> where sol: "egmatch_solution semp (n,k,\<sigma>)" by force
  from ident_prob_of_semp_complete[OF sol] have r1: ?r1 by blast
  from eident_prob_of_semp_complete[OF sol] have r2: ?r2 
    by (cases "eident_prob_of_semp semp", force+)
  from r1 r2 show "?r1 \<and> ?r2" ..
next
  assume "?r1 \<and> ?r2"        
  then have r1: ?r1 and r2: ?r2 by auto
  note sound = e_ident_prob_of_semp_sound[OF smp]
  let ?idps = "ident_prob_of_semp semp"
  let ?ks = "max_list (map (\<lambda> idp. SOME k. ident_solution idp k) ?idps)"
  {
    fix k
    let ?k = "max k ?ks"
    {
      fix idp
      assume idp: "idp \<in> set ?idps"
      have "\<exists> m \<le> ?k. ident_solution idp m"
      proof(rule, intro conjI)
        have "(SOME k. ident_solution idp k) \<le> ?ks"
          by (rule max_list, insert idp, auto)
        then show "(SOME k. ident_solution idp k) \<le> ?k" by simp
      next
        show "ident_solution idp (SOME k. ident_solution idp k)"
          by (rule someI_ex, insert r1 idp, auto)
      qed
    } 
  } note r1 = this
  note sound = sound[OF r1]
  show ?l
  proof (cases "eident_prob_of_semp semp") 
    case None
    from sound[unfolded None]
    show ?l by blast
  next
    case (Some eidp)
    with r2 obtain n k where r2: "eident_solution eidp (n,k)" by auto
    have "k \<le> max k ?ks" by simp
    with r2 have r2: "\<exists> k' \<le> max k ?ks. eident_solution eidp (n,k')" by blast
    have "\<exists> \<sigma>. egmatch_solution semp (n,max k ?ks,\<sigma>)"
    proof (rule sound)
      fix eidp'
      assume "eident_prob_of_semp semp = Some eidp'"
      with Some have "eidp = eidp'" by simp
      from r2[unfolded this] show "\<exists> k' \<le> max k ?ks. eident_solution eidp' (n,k')" .
    qed
    then show ?l by blast
  qed
qed

(* new result for getting rid of extended identity problems: 
   if C is large, then one can drop the extended-part in the identity-problem,
   or to be more precise, if (n,k) is a solution, then n must be 0 *)
lemma eident_prob_to_ident_prob:
  fixes D s C t
  defines eip: "eip \<equiv> (D, s, C, t)"
  assumes Cs: "\<exists>i. C \<rhd>c s \<cdot> \<mu> ^^ i"
  shows  "(\<exists>sol. eident_solution eip sol) = (\<exists> sol. ident_solution (eident_prob_to_ident_prob eip) sol)"
  unfolding eip eident_prob_to_ident_prob.simps
  unfolding ident_solution_def split
proof -
  note d = split eident_solution_def
  show "(\<exists> sol. eident_solution (D, s, C, t) sol) = (\<exists> k. D\<langle>t\<rangle> \<cdot> \<mu> ^^ k = s \<cdot> \<mu> ^^ k)" (is "?l = ?r")
  proof
    assume ?r
    then obtain k where id: "D\<langle>t\<rangle> \<cdot> \<mu> ^^ k = s \<cdot> \<mu> ^^ k" by auto
    show ?l
      by (rule exI[of _ "(0,k)"], unfold d, simp add: id[symmetric])
  next
    assume ?l
    then obtain n k where "eident_solution (D,s,C,t) (n,k)" by auto
    then have id: "s \<cdot> \<mu> ^^ k = D\<langle>ctxt_subst C \<mu> n t\<rangle> \<cdot> \<mu> ^^ k" unfolding d by simp
    show ?r
    proof (rule exI[of _ k], cases n)
      case 0
      show "D\<langle>t\<rangle> \<cdot> \<mu> ^^ k = s \<cdot> \<mu> ^^ k" using id 0 by simp
    next
      case (Suc m)
      from id[unfolded Suc] obtain u where id: "s \<cdot> \<mu> ^^ k = D\<langle>C\<langle>u\<rangle>\<rangle> \<cdot> \<mu> ^^ k" by simp
      from Cs obtain i where "C \<rhd>c s \<cdot> \<mu> ^^ i" by blast
      from suptc_imp_supt[OF this, of u] have supt: "C\<langle>u\<rangle> \<rhd> s \<cdot> \<mu> ^^ i" by blast
      let ?sk = "s \<cdot> \<mu> ^^ k"
      let ?Ck = "C\<langle>u\<rangle> \<cdot> \<mu> ^^ k"
      let ?sik = "s \<cdot> (\<mu> ^^ i) \<cdot> (\<mu> ^^ k)"
      let ?ski = "s \<cdot> (\<mu> ^^ k) \<cdot> (\<mu> ^^ i)"
      have supteq: "?sk \<unrhd> ?Ck" unfolding id by simp
      have supt: "?Ck \<rhd> ?sik"
        by (rule supt_subst[OF supt])
      from supteq supt have "?sk \<rhd> ?sik" by (rule supteq_supt_trans)
      then have "?sk \<rhd> ?ski" 
        unfolding subst_subst
        unfolding subst_power_compose_distrib[symmetric] 
        by (simp add: ac_simps)
      from supt_size[OF this]
      have "size ?ski < size ?sk" .
      also have "... \<le> size ?ski"
        by (rule size_subst)
      finally have False by simp
      then show "D\<langle>t\<rangle> \<cdot> \<mu> ^^ k = s \<cdot> \<mu> ^^ k" by simp
    qed
  qed
qed
end

subsection \<open>Combining all the results\<close>
context fixed_subst_incr
begin

(* plugging everything together:
   - first simplifiying extended matching problem to solved form 
   - then collect all extended and non-extended identity problems
   - immediately transform extended to non-extended identity problems *)
definition ident_prob_of_emp :: "('f, 'v) ematch_prob \<Rightarrow> ('f, 'v) ident_prob list option" where
  "ident_prob_of_emp emp \<equiv>
    (case simplify_emp emp of
      Inr b \<Rightarrow> if b then Some [] else None
    | Inl semp \<Rightarrow> Some (map eident_prob_to_ident_prob (option_to_list (eident_prob_of_semp semp)) @ ident_prob_of_semp semp))"


(* this following lemma shows how to solve extended matching problems that arise
   from outermost loops or, more generally, from forbidden pattern loops.
   Here the condition on large context Cs has been concretized to a condition
   which occurs in loops: D must be a proper subcontext of C *)
lemma ident_prob_of_emp:
  fixes C D :: "('f, 'v) ctxt" and l t :: "('f, 'v) term"
  defines emp: "emp \<equiv> (D,l,C \<cdot>\<^sub>c \<mu>,t)"
  assumes D: "D = C |_c p"
  and p: "p <\<^sub>p hole_pos C"
  shows  "(\<exists>sol. ematch_solution emp sol) = 
  (\<exists>idps. ident_prob_of_emp emp = Some idps \<and> (\<forall>idp\<in>set idps. (\<exists>sol. ident_solution idp sol)))" (is "?l = ?r")
proof -
  let ?C = "C \<cdot>\<^sub>c \<mu>"
  note d = ident_prob_of_emp_def emp split
  from p have C: "C \<noteq> \<box>" by auto
  then have C: "?C \<noteq> \<box>" by (cases C, auto)
  note simp = simplify_emp[OF C refl, of D l t, unfolded emp[symmetric]]
  let ?semp = "simplify_emp (D,l,?C,t)"
  let ?idps = "\<lambda> idps. set (map eident_prob_to_ident_prob (option_to_list (eident_prob_of_semp idps)) @ ident_prob_of_semp idps)"
  show ?thesis
  proof (cases ?semp)
    case (Inr b)
    with simp[of b] have id: "(\<exists> sol. ematch_solution emp sol) = b" unfolding d by simp
    show ?thesis 
      unfolding id
      unfolding d Inr by (cases b, auto)
  next
    case (Inl semp)
    from simp[of _ semp] have id: "(\<exists> sol. ematch_solution emp sol) = 
      (\<exists> sol. egmatch_solution semp sol)"
      and solved: "egmatch_solved_form semp" using Inl d by auto
    let ?idp1 = "ident_prob_of_semp semp"
    let ?eidp = "eident_prob_of_semp semp"
    let ?idp2 = "map eident_prob_to_ident_prob (option_to_list ?eidp)"
    let ?sol = "\<lambda> idp. \<exists> sol. ident_solution idp sol"
    have id2: "(\<exists> idps. ?idp2 @ ?idp1 = idps \<and> (\<forall> idp \<in> set idps. ?sol idp)) = 
      ((\<forall> idp \<in> set ?idp1. ?sol idp) \<and> (\<forall> idp \<in> set ?idp2. ?sol idp))" by auto
    have id3: "(\<forall> eidp. ?eidp = Some eidp \<longrightarrow> Ex (eident_solution eidp))
            =  (\<forall> idp \<in> set ?idp2. ?sol idp)" (is "?l = ?r")
    proof (cases ?eidp)
      case None then show ?thesis by simp
    next
      case (Some eidp)
      have "?l = Ex (eident_solution eidp)" unfolding Some by simp
      also have "... = ?sol (eident_prob_to_ident_prob eidp)" 
      proof -
        let ?call = "simplify_emp_main (D,l,?C,t,[]) []"
        from Inl[unfolded simplify_emp_def split]
        have call: "?call = Some (Some semp)"
          by (cases ?call, simp, cases "the ?call", auto)
        obtain D' l' C' t' mp' where semp: "semp = (D',l',C',t',mp')" by (cases semp, force)
        from p[unfolded less_pos_def'] obtain q where p: "hole_pos C = p @ q" by auto
        from split_ctxt[OF p] obtain E DD where C: "C = E \<circ>\<^sub>c DD"
          and DD: "DD = C |_c p" by auto
        have "\<exists> i E. ?C = E \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu> ^^ i)" 
          by (rule exI[of _ "Suc 0"], 
            insert DD[unfolded D[symmetric]] C, auto)
        from simplify_emp_main_large_C[OF this call[unfolded semp]]
        have large: "\<And> s l. (s,l) \<in> set mp' \<Longrightarrow> \<exists> i. C' \<rhd>c s \<cdot> \<mu> ^^ i" by force
        note semp = Some[unfolded semp eident_prob_of_semp.simps]
        from semp obtain s' where look: "map_of (reverse_rules mp') l' = Some s'" 
          by (auto split: option.splits bind_splits)
        from semp[unfolded look] have eidp: "eidp = (D',s',C',t')" by simp
        from map_of_SomeD[OF look] have mem: "(s',l') \<in> set mp'" by auto
        show ?thesis unfolding eidp 
          by (rule eident_prob_to_ident_prob[OF large[OF mem]])
      qed
      also have "... = ?r" unfolding Some by simp
      finally show ?thesis by simp
    qed      
    show ?thesis unfolding id
      unfolding e_ident_prob_of_semp[OF solved] 
      unfolding d Inl sum.simps option.simps
      unfolding id2 
      unfolding id3 ..
  qed
qed

(* the previous lemma applied to outermost loops: it shows how to convert the outermost-step 
   ctxt_substitition condition (which characterizes outermost loops) into a set of non-extended matching and 
   identity problems. All of these problems can then be solved using the decision procedures known from
   innermost loops *)
lemma ostep_ctxt_subst_cond_to_match_idents: 
  assumes q: "q \<in> poss t"
  shows "ostep_ctxt_subst_cond l C \<mu> q t = (\<not> ((\<exists> mp. mp \<in> o_match_probs l q t \<and> (\<exists> sol. match_solution mp sol)) \<or>
        (\<exists> mp idps. mp \<in> o_ematch_probs C l q t \<and> ident_prob_of_emp mp = Some idps \<and> (\<forall> idp \<in> set idps. \<exists> sol. ident_solution idp sol))))"
proof -
  let ?l = "(\<exists> mp sol. mp \<in> o_match_probs l q t \<and> match_solution mp sol)"
  have "ostep_ctxt_subst_cond l C \<mu> q t = (\<not> ((\<exists> mp sol. mp \<in> o_match_probs l q t \<and> match_solution mp sol) \<or>
        (\<exists> mp idps. mp \<in> o_ematch_probs C l q t \<and> ident_prob_of_emp mp = Some idps \<and> (\<forall> idp \<in> set idps. \<exists> sol. ident_solution idp sol))))"
    unfolding o_match_probs[OF q]
  proof (rule arg_cong[where f = "\<lambda> x. \<not> (?l \<or> (\<exists> mp. x mp))"], rule ext)
    fix mp
    {
      assume mem: "mp \<in> o_ematch_probs C l q t"
      obtain D' l' C' t' where mp: "mp = (D',l',C',t')" by (cases mp, auto)
      from mem[unfolded o_ematch_probs_def mp] 
      obtain p where p: "p <\<^sub>p hole_pos C" and D': "D' = C |_c p" and C': "C' = C \<cdot>\<^sub>c \<mu>" 
        by auto
      have "(\<exists> sol. ematch_solution mp sol) =
        (\<exists>idps. ident_prob_of_emp mp = Some idps \<and> (\<forall>idp\<in>set idps. \<exists>sol. ident_solution idp sol))"
        unfolding mp C'
        by (rule ident_prob_of_emp[OF D' p])
    }
    then show "(\<exists>sol. mp \<in> o_ematch_probs C l q t \<and> ematch_solution mp sol) = 
      ((\<exists>idps. mp \<in> o_ematch_probs C l q t \<and>
                 ident_prob_of_emp mp = Some idps \<and> (\<forall>idp\<in>set idps. \<exists>sol. ident_solution idp sol)))" by blast
  qed
  then show ?thesis by blast
qed
end

declare fixed_subst_incr.ident_prob_of_emp_def[code]

end

