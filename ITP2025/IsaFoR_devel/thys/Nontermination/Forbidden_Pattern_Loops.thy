(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013, 2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Forbidden_Pattern_Loops
  imports
    "HOL-Library.Monad_Syntax"
    First_Order_Rewriting.Trs
    TRS.Forbidden_Patterns
    Outermost_Loops
begin

(* from AFP/Automatic_Refinement/Lib/Misc *)
no_notation comp2 (infixl "oo" 55)

definition fploop :: "('f, 'v) forb_patterns \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) oloop \<Rightarrow> bool"
  where
    "fploop Pi R fpl =
    (case fpl of
      (C, \<mu>, len, ts, ps) \<Rightarrow>
        (\<forall> i \<le> len. (\<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>)) \<and> 
        (\<forall> i \<le> len. \<forall> n. fpstep_cond Pi (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))) \<and>
        ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>)"

lemma fploop_cond:
  assumes loop: "fploop Pi R (C, \<mu>, len, ts, ps)"
    and i: "i \<le> len"
  shows "fpstep_cond Pi (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))"
  using assms unfolding fploop_def by blast

lemma fploop_fpstep_p:
  assumes fploop: "fploop Pi R (C, \<mu>, len, ts, ps)"
    and i: "i \<le> len"
  shows "(ctxt_subst C \<mu> n (ts i), ctxt_subst C \<mu> n (ts (Suc i))) \<in> fpstep_p Pi R (hole_pos C ^ n @ ps i)"
proof -
  note loop = fploop[unfolded fploop_def]
  from loop i obtain \<sigma> lr where step: "(ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>" by auto
  show ?thesis
    by (rule fpstep_pI[OF ctxt_subst_step[OF step]], rule fploop_cond[OF fploop], insert i, auto)
qed

lemma fploop_end:
  assumes fploop: "fploop Pi R (C, \<mu>, len, ts, ps)"
  shows "ctxt_subst C \<mu> n (ts (Suc len)) = ctxt_subst C \<mu> (Suc n) (ts 0)"
proof -
  note loop = fploop[unfolded fploop_def]
  from loop have ts: "ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>" by auto
  show ?thesis unfolding ts unfolding ctxt_subst_Suc ..
qed

lemma fploop_iterate:
  assumes fploop: "fploop Pi R (C, \<mu>, len, ts, ps)"
  shows "(ctxt_subst C \<mu> n (ts 0), ctxt_subst C \<mu> (Suc n) (ts 0)) \<in> (fpstep Pi R)^+"
proof -
  let ?t = "\<lambda> i. ctxt_subst C \<mu> n (ts i)"
  from fploop_fpstep_p[OF fploop] have 
    steps_i: "\<And> i. i \<le> len \<Longrightarrow> (?t i, ?t (Suc i)) \<in> fpstep Pi R" unfolding fpstep_def by blast
  have steps: "(?t 0, ?t len) \<in> (fpstep Pi R)^*"
    unfolding rtrancl_fun_conv
    by (rule exI[of _ ?t], rule exI[of _ len], insert steps_i, auto)
  have step: "(?t len, ctxt_subst C \<mu> (Suc n) (ts 0)) \<in> fpstep Pi R"
    using steps_i[of len]
    unfolding fploop_end[OF fploop, of n] by simp
  from steps step show ?thesis by auto
qed

lemma fploop_imp_not_SN:
  assumes fploop: "fploop Pi R (C, \<mu>, len, ts, ps)"
  shows "\<not> SN_on (fpstep Pi R) {ts 0}"
proof
  assume SN: "SN_on (fpstep Pi R) {ts 0}"
  let ?O = "(fpstep Pi R)^+"
  from SN have SN: "SN_on ?O {ts 0}" by (rule SN_on_trancl)
  let ?t = "\<lambda> i. ctxt_subst C \<mu> i (ts 0)"
  from fploop_iterate[OF fploop] have steps: "\<And> i. (?t i, ?t (Suc i)) \<in> ?O" .
  have steps: "\<exists> f. f 0 \<in> {ts 0} \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?O)" 
    by (rule exI[of _ ?t], insert steps, auto)
  with SN show False unfolding SN_defs by blast
qed

definition fpstep_ctxt_subst_cond :: "('f,'v)forb_pattern \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)subst \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "fpstep_ctxt_subst_cond pt C \<mu> p t \<equiv> (\<forall> n. fpstep_cond_single pt (hole_pos C ^ n @ p) (ctxt_subst C \<mu> n t))"

lemma fploopI:
  assumes steps: "\<And> i. i \<le> len \<Longrightarrow> \<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>"
    and len: "ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>"
    and fpcond: "\<And> pt i. i \<le> len \<Longrightarrow> ps i \<in> poss (ts i) \<Longrightarrow> pt \<in> Pi \<Longrightarrow> fpstep_ctxt_subst_cond pt C \<mu> (ps i) (ts i)"
  shows "fploop Pi R (C, \<mu>, len, ts, ps)"
  unfolding fploop_def split_def fst_conv snd_conv
proof (intro conjI allI impI)
  fix i
  assume "i \<le> len"
  from steps[OF this]
  show "\<exists> \<sigma> lr. (ts i, ts (Suc i)) \<in> rstep_r_p_s R lr (ps i) \<sigma>" by blast
next
  show "ts (Suc len) = C\<langle>ts 0 \<cdot> \<mu>\<rangle>" by (rule len)
next
  fix i n
  assume i: "i \<le> len"
  from steps[OF i] have "ps i \<in> poss (ts i)" unfolding rstep_r_p_s_def' by auto
  from fpcond[OF i this, unfolded fpstep_ctxt_subst_cond_def]
  show "fpstep_cond Pi (hole_pos C ^ n @ ps i) (ctxt_subst C \<mu> n (ts i))" 
    unfolding fpstep_cond_def by blast
qed

section \<open>decision procedure for forbidden pattern loops\<close>

context fixed_subst 
begin
definition n0 :: "pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> nat"
  where "n0 p q oo \<equiv> nat (ceiling (rat_of_nat (size oo - size q) / (rat_of_nat (size p))))"

definition pos_dec :: "pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> (nat \<times> pos) option"
  where "pos_dec p q oo \<equiv>
 if p = Nil then  
  (case remove_suffix oo q of None \<Rightarrow> None | Some r \<Rightarrow> Some (0, r))
 else
  let n0 = nat (ceiling (rat_of_nat (size oo - size q) / (rat_of_nat (size p)))) in
  (case (remove_suffix oo ((p^n0) @ q)) of None  \<Rightarrow> None | Some r \<Rightarrow> Some (n0, r))"

lemma pos_dec_sound: 
  assumes l:"pos_dec p q oo = Some (n, r)"
  shows "p^n @ q = r @ oo"
proof(cases p, simp)
  case Nil
  with l have "remove_suffix oo q = Some r" unfolding pos_dec_def using option.distinct(1) by (cases "remove_suffix oo q", simp, force)
  with Nil show "q = r @ oo" apply (auto split: option.splits)
    using \<open>remove_suffix oo q = Some r\<close> remove_suffix_Some by blast
next
  case (Cons i p')
  let ?n0 = "nat (ceiling (rat_of_nat (size oo - size q) / (rat_of_nat (size (Cons i p')))))"
  let ?q = "(Cons i p')^?n0 @ q"
  from Cons l have n:"?n0 = n  \<and> remove_suffix oo ?q = Some r" unfolding pos_dec_def using option.distinct(1) by (cases "remove_suffix oo ?q", simp, force)
  then have "remove_suffix oo ((Cons i p')^n @ q) = Some r" by auto
  with Cons have "(Cons i p')^n @ q = r @ oo" apply (auto split: option.splits)
    using \<open>remove_suffix oo ((i # p') ^ n @ q) = Some r\<close> remove_suffix_Some by blast
  with Cons show ?thesis by blast
qed


lemma ceiling_mult_le:"int a * ceiling (b::rat) \<ge> ceiling (rat_of_nat a * b::rat)" 
proof(induct a, simp)
  case (Suc a)
  have "int (Suc a) * ceiling b = int a * ceiling b + ceiling b"
    by (simp add: int_distrib)
  with Suc have x:"int (Suc a) * ceiling b \<ge> ceiling (rat_of_nat a * b) + ceiling b" by auto
  have "int (Suc a) * ceiling b \<ge> ceiling (rat_of_nat a * b  + b)" using ceiling_add_le order_trans[OF _ x] by blast
  then show ?case by (simp add: field_simps)
qed

lemma size_n0: 
  assumes p:"p \<noteq> Nil" 
  shows "size (p ^ (n0 p q oo) @ q) \<ge> size oo"
proof -
  let ?n0 = "n0 p q oo"
  from p have nonzero:"size p > 0" by auto
  have 0:"(size p) * ?n0 = nat (int (size p)) * ?n0" by (metis nat_int)
  have "?n0 = nat (ceiling ((rat_of_nat (size oo - size q) / (rat_of_nat (size p)))))" unfolding n0_def using p by auto
  then have 1:"nat (int (size p)) * ?n0 = nat ((int (size p)) * ceiling ((rat_of_nat (size oo - size q) / (rat_of_nat (size p)))))" 
    by (simp add: nat_mult_distrib)
  have 2:"nat ((int (size p)) * ceiling ((rat_of_nat (size oo - size q) / (rat_of_nat (size p))))) \<ge> nat (ceiling ((rat_of_nat (size p)) * (rat_of_nat (size oo - size q) / (rat_of_nat (size p)))))" using ceiling_mult_le nat_mono by blast
  have 3:"nat (ceiling ((rat_of_nat (size p)) * (rat_of_nat (size oo - size q) / (rat_of_nat (size p))))) \<ge> nat (ceiling (rat_of_nat (size oo - size q)))" using nonzero by auto
  have 4:"nat (ceiling (rat_of_nat (size oo - size q))) = size oo - size q" by simp
  with 0 1 2 3 have "size p * ?n0 \<ge> size oo - size q" by auto
  then show ?thesis using power_size by auto
qed

lemma n0_min:
  assumes eq:"(size (p ^ n)) + size q \<ge> (size oo)"
    and p:"p \<noteq> Nil" 
  shows "n \<ge> n0 p q oo"
proof -
  let ?n0 = "n0 p q oo"
  from eq obtain r where "(size p) * n + size q = r + (size oo)" 
    using power_size le_iff_add by (metis add.commute)
  then have sum':"r + size oo - size q = (size p) * n" by linarith
  then have rp:"rat_of_nat (r + size oo - size q) = (rat_of_nat (size p)) *  rat_of_nat n" using of_nat_mult by force
  from p have z:"rat_of_nat (size p) > 0" by auto
  with rp have "rat_of_nat (r + size oo - size q) / (rat_of_nat (size p)) = rat_of_nat n" by force
  then have key:"nat (ceiling (rat_of_nat (r + size oo - size q) / (rat_of_nat (size p)))) = n" by force
  have "rat_of_nat (r + size oo - size q) \<ge> (rat_of_nat (size oo - size q))" (is "?l \<ge> ?r") by fastforce 
  from divide_right_mono[OF this] have "?l / (rat_of_nat (size p)) \<ge> ?r / (rat_of_nat (size p))" by auto
  with key show ?thesis unfolding n0_def using  ceiling_mono ceiling_of_nat [[linarith_split_limit = 15]] 
    by fastforce
qed

lemma pos_dec_complete:
  assumes rn:"p^n @ q = r @ oo"
  shows "\<exists> r' n'. pos_dec p q oo = Some (n', r') \<and> (n \<ge> n')"
proof(cases "p=Nil")
  case True
  with rn have "q = r @ oo" by simp
  then obtain r' where "r' @ oo = q" and "remove_suffix oo q = Some r'" by auto
  with True show ?thesis using pos_dec_def by auto
next
  case False
  let ?n0 = "n0 p q oo"
  from rn have "size (p^n) + size q \<ge> size oo"
    by (metis le_add2 length_append)
  then have n_ge_n0:"n \<ge> ?n0" using n0_min False by auto
  have pn0q_ge_o:"size (p^?n0 @ q) \<ge> size oo" using False size_n0 by auto
  from n_ge_n0 obtain k where "p^n = p^k @ p^?n0" by (metis le_add_diff_inverse2 power_append_distr)
  with rn False have pk:"p^k @ p^?n0 @ q = r @ oo" using append_assoc by auto
  then have "size (p^k) + size (p^?n0 @ q) = size r + size oo"
    by (metis length_append)
  with pn0q_ge_o have kr:"size (p^k) \<le> size r" by fastforce
  from pk have "p^k \<le>\<^sub>p r @ oo" using less_eq_pos_simps(1) by metis
  from pos_less_eq_append_not_parallel[OF this] kr have "p^k \<le>\<^sub>p r" using pos_cases prefix_smaller by fastforce
  then obtain r' where "r = p^k @ r'" using suffix_exists by auto
  with pk have "p^?n0 @ q  = r' @ oo" by auto
  then have "remove_suffix oo (p^?n0 @ q) = Some r'" by force
  with n_ge_n0 show ?thesis unfolding pos_dec_def n0_def using False by simp
qed


(* Loops Involving Forbidden Patterns of Type (_, _, H) *)

definition h_match_probs :: 
  "('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" 
  where "h_match_probs l oo q C t \<equiv> 
  (case (pos_dec (hole_pos C) q oo) of 
    None \<Rightarrow> {}
  | Some (n, o') \<Rightarrow> {((ctxt_subst C \<mu> n t) |_ o', l)})"


lemma fp_h_match_probs_sound:
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and mp: "mp \<in> h_match_probs l oo q C t"
    and sol: "match_solution mp (n, \<sigma>)"
  shows "\<not> fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.H) C \<mu> q t"
proof -
  from mp have "\<exists> n o'. pos_dec (hole_pos C) q oo = Some (n, o')" using h_match_probs_def by (cases "pos_dec (hole_pos C) q oo", auto) 
  then obtain k o' where sm:"pos_dec (hole_pos C) q oo = Some (k, o')" by auto
  let ?p = "hole_pos C"
  let ?q = "?p^k @ q"
  let ?pt = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.H)"
  let ?cs = "ctxt_subst C \<mu>"
  let ?t = "?cs (n + k) t"
  let ?q' = "?p^(n + k) @ q"
  have qpos:"?q  \<in> poss (?cs k t)" using qt ctxt_subst_hole_pos by auto
  have ppos:"?p^n \<in> poss ?t " using ctxt_subst_hole_pos by auto
  from sm have q:"?q = o' @ oo" using pos_dec_sound by auto 
  from qt q have o':"o' \<in> poss (?cs k t)" using ctxt_subst_hole_pos by (metis ctxt_subst_subt_at poss_append_poss poss_imp_subst_poss)
  then have opos:"o' \<in> poss ((?cs k t) \<cdot> \<mu> ^^ n)" using poss_imp_subst_poss by auto
  have "((?cs k t) |_ o') \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" using mp sol sm  h_match_probs_def match_solution_def by auto 
  with o' have eq:"((?cs k t) \<cdot> \<mu> ^^ n) |_ o' = l \<cdot> \<sigma>" by auto
  with qpos have "?t |_(?p^n) |_ (?p^k @ q) = l \<cdot> \<sigma>|_oo"  using ctxt_subst_add subt_at_subst q by auto
  then have "?t |_ ?q' = l \<cdot> \<sigma>|_ oo" by (simp add: power_append_distr)
  from sm have pos:"?p ^ k @ q = o' @ oo" by (rule pos_dec_sound)
  have l:"(ctxt_of_pos_term oo l)\<langle>l|_oo \<rangle> = l" using ctxt_supt_id ol by auto
  have l':"hole_pos (ctxt_of_pos_term oo l) = oo"using hole_pos_ctxt_of_pos_term ol by fast
  have tt:"?t|_(?p ^ n) = (?cs k t) \<cdot> \<mu> ^^ n" using ctxt_subst_ctxt by auto
  let ?C' = "ctxt_of_pos_term (?p ^ n @ o') ?t"
  from eq have "?t|_(?p ^ n) |_o' = l \<cdot> \<sigma>" using ctxt_subst_ctxt by auto
  then have t_ctxt:"?t = ?C'\<langle>l \<cdot> \<sigma>\<rangle>" using ppos opos tt by (metis ctxt_supt_id pos_append_poss subt_at_append)
  have "hole_pos ?C' = ?p ^ n @ o'" by (metis hole_pos_ctxt_of_pos_term opos pos_append_poss ppos tt)
  with t_ctxt q have "\<exists> C' \<sigma>.( ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> ?q' = hole_pos C' @ oo)" by (metis append_assoc power_append_distr)
  then have "\<not> fpstep_cond_single ?pt ?q' ?t" using fpstep_cond_single_def[of ?pt ?q'] l l' split_conv by force
  then show ?thesis  using fpstep_ctxt_subst_cond_def[of ?pt C \<mu> q t] by blast
qed

lemma fp_h_match_probs_complete:
  assumes nfp:"\<not> fpstep_cond_single (L, u, Forbidden_Patterns.H ) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)"
    and qt: "q \<in> poss t"
  shows "\<exists> mp n \<sigma>. mp \<in> h_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution mp (n, \<sigma>)"
proof -
  let ?ct = "ctxt_subst C \<mu> n t"
  let ?o = "hole_pos L"
  let ?p = "hole_pos C"
  from nfp obtain C' \<sigma> where c:"?ct = C'\<langle>(L \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>\<rangle> \<and> ?p ^ n @ q = (hole_pos C') @ ?o"
    unfolding fpstep_cond_single_def by auto
  then have oLs:"?o = hole_pos (L \<cdot>\<^sub>c \<sigma>)" using hole_pos_subst by auto
  let ?o' = "hole_pos C'"
  from c oLs have pos_eq0:"?p^n @ q = ?o' @ ?o" by fast
  then obtain o'' n' where pd:"pos_dec ?p q ?o = Some (n', o'')" and n_ge_n':"n \<ge> n'" using pos_dec_complete by blast
  then obtain k where nkn:"n = k + n'" by (metis le_iff_add add.commute)
  let ?mp = "((ctxt_subst C \<mu> n' t) |_ o'', L\<langle>u\<rangle>)"
  from pd have pos_eq1:"?p^n' @ q = o'' @ ?o" by (rule pos_dec_sound)
  then have "?p^k @ ?p^n' @ q = ?p^k @  o'' @ ?o" by metis
  with pos_eq1 have "?o' @ ?o = ?p^k @  o'' @ ?o" using nkn pos_eq0 by (simp add: power_append_distr)
  then have pos_eq2:"?o' = ?p^k @ o''" by auto
  have "?p^n' \<in> poss (ctxt_subst C \<mu> n' t)" using ctxt_subst_hole_pos by auto
  then have p_pos:"?p^n' @ q \<in> poss (ctxt_subst C \<mu> n' t)" using ctxt_subst_subt_at qt by (metis pos_append_poss poss_imp_subst_poss)
  from c have ls:"L\<langle>u\<rangle> \<cdot> \<sigma> = (ctxt_subst C \<mu> n t) |_ ?o'" using subst_apply_term_ctxt_apply_distrib subt_at_hole_pos by auto
  also have "\<dots> = ?ct |_ (?p^k @ o'')" using pos_eq2 by auto  
  also have "\<dots> =  (ctxt_subst C \<mu> k (ctxt_subst C \<mu> n' t)) |_  (?p^k @ o'')" using nkn using ctxt_subst_add by auto
  also have "\<dots> =  (ctxt_subst C \<mu> n' t) \<cdot> \<mu> ^^ k |_ o''" by (metis ctxt_subst_hole_pos ctxt_subst_subt_at subt_at_append) 
  also have "\<dots> = (ctxt_subst C \<mu> n' t) |_ o'' \<cdot> \<mu> ^^ k" using p_pos by (metis pos_eq1 poss_append_poss subt_at_subst)
  finally have sol:"match_solution ?mp (k,\<sigma>)" using match_solution_def by force
  from pd n_ge_n' have "h_match_probs L\<langle>u\<rangle> (hole_pos L) q C t = {?mp}" unfolding h_match_probs_def using split by (metis option.simps(5))
  with sol have "?mp \<in> h_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution ?mp (k, \<sigma>)" by auto
  then show ?thesis by fast
qed


(* Loops Involving Forbidden Patterns of Type (_, _, A) *)

definition a_match_probs :: 
  "('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" 
  where "a_match_probs l oo q C t \<equiv>
  case t|_ q of Var x \<Rightarrow> {}
   | Fun f ls \<Rightarrow>
   {(u, l) | u. \<exists>o'' q'. 
     u = (ctxt_subst C \<mu> (n0 (hole_pos C) q oo) t) |_ o'' \<and> 
     o'' \<le>\<^sub>p (hole_pos C)^(n0 (hole_pos C) q oo) @ q @ q' \<and> 
     q @ q' \<in> poss t \<and> 
     (hole_pos C)^ (n0 (hole_pos C) q oo) @ q <\<^sub>p o'' @ oo } 
   \<union> {(u, l) | s u. s \<in> \<mu> ` W (t |_ q) \<and> s \<unrhd> u \<and> is_Fun u}"

lemma fp_a_match_probs_sound:
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and mp: "(u, l) \<in> a_match_probs l oo q C t"
    and sol: "match_solution (u, l) (n, \<sigma>)"
  shows "\<not> fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.A) C \<mu> q t"
proof(cases "t |_ q")
  case (Var x)
  then have "a_match_probs l oo q C t = {}" unfolding a_match_probs_def by auto
  with mp show ?thesis by blast
next
  case (Fun f ls)
  then have tqf: "t |_ q = Fun f ls" by auto
  let ?p = "hole_pos C"
  let ?n0 = "n0 ?p q oo"
  let ?pt = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.A)"
  let ?cs = "ctxt_subst C \<mu>"
  from mp[unfolded a_match_probs_def] have 
    ab:"(u, l) \<in> {(u, l) | u. \<exists>o'' q'. u = (ctxt_subst C \<mu> ?n0 t) |_ o'' \<and>  (o'' \<le>\<^sub>p ?p^?n0 @ q @ q' \<and> q @ q' \<in> poss t \<and> (?p^?n0 @ q) <\<^sub>p (o'' @ oo)) } \<or>
   (u, l) \<in> {(u, l) | s u. s \<in> \<mu> ` W (t |_ q) \<and> s \<unrhd> u \<and> is_Fun u}" (is "?A \<or> ?B") using Un_iff tqf by auto
  have l:"(ctxt_of_pos_term oo l)\<langle>l|_oo \<rangle> = l" using ctxt_supt_id ol by auto
  have l':"hole_pos (ctxt_of_pos_term oo l) = oo" using ol by (metis hole_pos_ctxt_of_pos_term)
  show ?thesis
  proof(cases ?A)
    case True
    assume ?A
    with sol[unfolded match_solution_def] obtain o'' q' where  "((?cs ?n0 t) |_ o'') \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" and 
      ole:"o'' \<le>\<^sub>p ?p ^ ?n0 @ q @ q'" and qt:"q @ q' \<in> poss t" and pp:"?p ^ ?n0 @ q <\<^sub>p o'' @ oo" by auto
    then obtain k where ls:"((?cs ?n0 t) |_ o'') \<cdot> (\<mu> ^^ k) =  l \<cdot> \<sigma>" by auto
    let ?o' = "?p^k @ o''"
    let ?t = "ctxt_subst C \<mu> (k + ?n0) t"
    have "?p ^ ?n0 \<in> poss (?cs ?n0 t)" using ctxt_subst_hole_pos ctxt_subst_add by auto
    with qt have "?p ^ ?n0 @ q @ q' \<in> poss (ctxt_subst C \<mu> ?n0 t)" using  poss_append_poss poss_imp_subst_poss by force
    then have opos: "o'' \<in> poss (?cs ?n0 t)" using ole less_eq_pos_def poss_append_poss by metis
    have "?p^k \<in> poss (?cs (k + ?n0) t)" using ctxt_subst_hole_pos ctxt_subst_add by auto
    then have ot:"?o' \<in> poss ?t" using opos using ctxt_subst_add ctxt_subst_subt_at pos_append_poss poss_imp_subst_poss by auto
    then have "?t |_ ?o' = ((?cs k (?cs ?n0 t)) |_ ?p^k |_ o'')" using ctxt_subst_add subt_at_append by auto
    also have "\<dots> = (?cs ?n0 t) \<cdot> \<mu> ^^ k |_ o''" using ctxt_subst_subt_at by auto
    finally have eq:"?t |_ ?o' =  l \<cdot> \<sigma>" using ls opos by auto
    from pp have posc:"?p^(k + ?n0) @ q  <\<^sub>p ?o' @ oo" by (simp add: power_append_distr)
    let ?q = "?p^(k + ?n0) @ q"
    let ?C' = "ctxt_of_pos_term ?o' ?t"
    from eq have t_ctxt:"?t = ?C'\<langle>l \<cdot> \<sigma>\<rangle>" using ctxt_supt_id[OF ot] by force
    have "hole_pos ?C' = ?o'" by (metis hole_pos_ctxt_of_pos_term ot)
    with t_ctxt posc have "\<exists>C' \<sigma>. ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> ?p^(k + ?n0) @ q <\<^sub>p (hole_pos C') @ oo" by metis
    then have "\<not> fpstep_cond_single ?pt ?q ?t" using fpstep_cond_single_def[of ?pt] l l' split_conv by force
    then show ?thesis using fpstep_ctxt_subst_cond_def[of ?pt C \<mu> q t] by blast
  next
    case False
    then have ?B using ab by auto
    then obtain s where "s \<in> \<mu> ` (vars_iteration \<mu> (t |_ q))" and su:"s \<unrhd> u" and "is_Fun u" by auto
    then obtain x where s_mu_x:"s = \<mu>(x)" and "x \<in> vars_iteration \<mu> (t |_ q)" by auto
    then obtain i where "x \<in> vars_term (t |_ q \<cdot> \<mu> ^^ i)" unfolding vars_iteration_def by auto
    then obtain o'' where tx:"(t |_ q \<cdot> \<mu> ^^ i) |_ o'' = Var x" and ot:"o'' \<in> poss (t |_q \<cdot> \<mu> ^^ i)" 
      using supteq_imp_subt_at vars_term_supteq(1)[of x] by blast
    obtain r where u:"(Var x) \<cdot> \<mu> |_r = u" and r:"r \<in> poss ((Var x)  \<cdot> \<mu>)" using supteq_imp_subt_at su s_mu_x by auto
    let ?n = "Suc i + n"
    let ?o' = "?p ^ ?n @ q @ o'' @ r"
    let ?t = "ctxt_subst C \<mu> ?n t"
    have eq:"?t |_ ?o' = l \<cdot> \<sigma>"
    proof -
      have t_o':"?t |_ ?o' = ?t |_ ?p^?n |_ (q @ o'' @ r)" using subt_at_append ctxt_subst_hole_pos[of _ ?n] by blast
      also have "\<dots> = t |_q \<cdot> \<mu> ^^ ?n |_ (o'' @ r)" using ctxt_subst_subt_at[of C \<mu> ?n] qt by auto
      also have "\<dots> = t |_q \<cdot> (\<mu> ^^ i \<circ>\<^sub>s \<mu> ^^ (Suc n)) |_ (o'' @ r)" using subst_power_compose_distrib add_Suc_shift by metis
      also have lm:"\<dots> = t |_q \<cdot> \<mu> ^^ i \<cdot> \<mu> ^^ (Suc n) |_ (o'' @ r)" using subst_subst by auto
      also have "\<dots> = t |_q \<cdot> \<mu> ^^ i |_ o'' \<cdot> \<mu> ^^ (Suc n) |_ r" using lm ot by simp
      also have "\<dots> = (Var x) \<cdot> \<mu> \<cdot> \<mu> ^^ n |_ r" using tx subst_monoid_mult.power_Suc2 by (auto simp: subst_compose)
      finally show ?thesis using r u subt_at_subst sol t_o' unfolding match_solution_def by auto
    qed
    have cc:"ctxt_subst C \<mu> ((Suc i) + n) t = ctxt_subst C \<mu> (Suc i) (ctxt_subst C \<mu> n t)" using ctxt_subst_add by auto
    have ot: "?o' \<in> poss ?t"
    proof -
      from tx u have  "(t |_ q \<cdot> \<mu> ^^ i) \<cdot> \<mu> |_ o'' = (Var x) \<cdot> \<mu>" using subt_at_subst ot by force
      with r ot have "o'' @ r \<in> poss (t |_q \<cdot> \<mu> ^^ i \<cdot> \<mu>)" using pos_append_poss[OF ot] by auto 
      with qt have "q @ o'' @ r \<in> poss (t \<cdot> \<mu> ^^ i \<cdot> \<mu>)" using poss_append_poss by auto
      then have qor:"q @ o'' @ r \<in> poss (t \<cdot> \<mu> ^^ (Suc i))" using subst_subst subst_power_Suc by metis
      let ?s = "ctxt_subst (C \<cdot>\<^sub>c (\<mu> ^^ (Suc i) )) \<mu> n (t \<cdot> \<mu> ^^ (Suc i))"
      have ax:"?s |_ ?p^n = (t \<cdot> \<mu> ^^ (Suc i)) \<cdot> \<mu> ^^ n" using ctxt_subst_subt_at hole_pos_subst by metis
      have ps:"?p^n \<in> poss ?s" using hole_pos_subst ctxt_subst_hole_pos by metis
      with qor ax have pqor:"?p ^ n @ (q @ o'' @ r) \<in> poss ?s" using 
          pos_append_poss[OF ps] poss_imp_subst_poss by metis
      have ce:"(ctxt_subst C \<mu> n t) \<cdot> (\<mu> ^^ (Suc i)) = ?s" using ctxt_subst_subst_pow by blast
      with pqor have pqor:"?p ^ n @ (q @ o'' @ r) \<in> poss ((ctxt_subst C \<mu> n t) \<cdot> (\<mu> ^^ (Suc i)))" by auto
      from cc have tp:"?t |_ ?p^(Suc i) = (?cs n t) \<cdot> (\<mu> ^^ (Suc i))" using ctxt_subst_subt_at[of C \<mu> "Suc i"] by auto
      with pqor have pqor:"?p ^ n @ (q @ o'' @ r) \<in> poss (?t |_ ?p^(Suc i))" by auto
      have pit:"?p^(Suc i) \<in> poss ?t" using ctxt_subst_add ctxt_subst_hole_pos by auto
      with pqor show ?thesis using  pos_append_poss[OF pit pqor]
        by (simp add: power_append_distr)
    qed
    have o'':"[] <\<^sub>p o''" 
    proof -
      from tx have "is_Var (t \<cdot> \<mu> ^^ i |_ (q @ o''))"
        using poss_imp_subst_poss qt subt_at_append subt_at_subst by force
      with tqf show ?thesis using less_pos_def' subst_apply_eq_Var tx by fastforce
    qed
    let ?q = "?p^?n @ q"
    from o'' have posc:"?q <\<^sub>p ?o' @ oo" unfolding less_pos_def' by auto
    let ?C' = "ctxt_of_pos_term ?o' ?t"
    from eq ot have t_ctxt:"?t = ?C'\<langle>l \<cdot> \<sigma>\<rangle>" using ctxt_supt_id by metis
    have "hole_pos ?C' = ?o'" by (metis hole_pos_ctxt_of_pos_term ot)
    with t_ctxt posc have "\<exists>C' \<sigma>. ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> ?q <\<^sub>p (hole_pos C') @ oo" by auto
    then have "\<not> fpstep_cond_single ?pt ?q ?t" unfolding fpstep_cond_single_def[of ?pt ?q ?t] split_conv l l' by force
    then show ?thesis using fpstep_ctxt_subst_cond_def[of ?pt C \<mu> ?q t] by (metis fpstep_ctxt_subst_cond_def)
  qed
qed

lemma fp_a_match_probs_complete:
  assumes nfp:"\<not> fpstep_cond_single (L, u, Forbidden_Patterns.A) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)"
    and qt: "q \<in> poss t"
    and t_q_fun:"is_Fun (t |_ q)"
    and lfun: "is_Fun L\<langle>u\<rangle>"
  shows "\<exists> mp n \<sigma>. mp \<in> a_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution mp (n, \<sigma>)"
proof -
  let ?cs = "ctxt_subst C \<mu>"
  let ?ct = "?cs n t"
  let ?o = "hole_pos L"
  let ?p = "hole_pos C"
  from nfp obtain C' \<sigma> where ctxt_eq0:"?ct = C'\<langle>(L \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>\<rangle>" and pos_eq0:"?p ^ n @ q <\<^sub>p hole_pos C' @ ?o"
    unfolding fpstep_cond_single_def by auto
  then have oLs:"?o = hole_pos (L \<cdot>\<^sub>c \<sigma>)" using hole_pos_subst by auto
  let ?n0 = "n0 ?p q ?o"
  let ?match = "\<lambda> C' \<sigma> n. ?cs n t = C'\<langle>(L \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>\<rangle> \<and> ?p ^ n @ q <\<^sub>p hole_pos C' @ ?o" 
  let ?ex =  "\<exists> q' C' \<sigma> n. q @ q' \<in> poss t \<and> hole_pos C' \<le>\<^sub>p ?p ^ n @ q @ q' \<and> ?match C' \<sigma> n"
  show ?thesis
  proof(cases ?ex)
    case True note caseA=this (* case (a) *)
    assume ?ex
    then obtain q' C' \<sigma> n where qq':"q @ q' \<in> poss t" and geq:"hole_pos C' \<le>\<^sub>p ?p ^ n @ q @ q'" 
      and ctxt_eq:"?cs n t = C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle>" and pos_eq:"?p ^ n @ q <\<^sub>p hole_pos C' @ ?o" by auto
    let ?o' = "hole_pos C'"  
    let ?ct = "?cs n t"  
    show ?thesis
    proof(cases "?p = Nil")
      case True note pNil=this
      then have n00:"?n0 = 0" unfolding n0_def using split by auto
      then have a:"((?cs ?n0 t) |_ ?o') \<cdot> \<mu> ^^ n = t |_ ?o' \<cdot> \<mu> ^^ n" by auto
      from geq[unfolded pNil less_eq_pos_def] qq' have "?o' \<in> poss t" using poss_append_poss by (simp, metis)
      then have "t |_ ?o' \<cdot> \<mu> ^^ n =  t \<cdot> \<mu> ^^ n |_ ?o'" by auto
      also have "\<dots> =  (?cs n t) |_ (?p^n @ ?o')" unfolding ctxt_subst_subt_at[symmetric] by simp
      also have "\<dots> =  (?cs n t) |_ ?o'" using True by simp
      finally have sol:"((?cs ?n0 t) |_ ?o') \<cdot> \<mu> ^^ n = L\<langle>u\<rangle> \<cdot> \<sigma>" using a ctxt_eq subt_at_hole_pos by simp
      let ?mp = "((ctxt_subst C \<mu> ?n0 t) |_ ?o', L\<langle>u\<rangle>)"
      from sol have sol:"match_solution ?mp (n,\<sigma>)" using match_solution_def by force
      from geq qq' pos_eq have a:"?o' \<le>\<^sub>p ?p^?n0 @ q @ q' \<and> q @ q' \<in> poss t \<and> ?p^?n0 @ q <\<^sub>p ?o' @ ?o" unfolding True by simp
      let ?v=" (?cs ?n0 t) |_ ?o'"
      define property where "property = (\<lambda> v. (\<exists>o'' q'.  v = (ctxt_subst C \<mu> ?n0 t) |_ o'' \<and> t|_o'' = (?cs ?n0 t) |_ o'' \<and> 
         o'' \<le>\<^sub>p ?p^?n0 @ q @ q' \<and> q @ q' \<in> poss t \<and> ?p^?n0 @ q <\<^sub>p (o'' @ ?o)))"
      from a have  "\<exists> v. v = ?v \<and> property v" using n00 unfolding property_def by auto
      then have "?mp \<in> {(v, L\<langle>u\<rangle>) | v.  property v }" by auto 
      then have "?mp \<in> a_match_probs L\<langle>u\<rangle> ?o q C t" unfolding a_match_probs_def property_def using t_q_fun 
        by (cases "t|_q"; force)
      with sol show ?thesis by auto
    next
      case False note pNonNil=this
      have "\<exists>  n' o' \<sigma>' C'. o' \<le>\<^sub>p ?p ^ n' @ q @ q' \<and> n' \<ge> ?n0 \<and>
         ?p ^ n' @ q <\<^sub>p o' @ ?o \<and> ?cs n' t = C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>'\<rangle> \<and> hole_pos C' = o'"
      proof(cases "n \<ge> ?n0")
        case True
        assume "n \<ge> ?n0"
        with geq pos_eq ctxt_eq show ?thesis by auto 
      next
        case False 
        assume  "\<not>(n \<ge> ?n0)"
        let ?O = "?p^ ?n0 @ ?o'"
        let ?N = "?n0 + n"
        let ?C' = "ctxt_subst_ctxt C \<mu> ?n0 C'"
        let ?\<sigma>' = "\<sigma> \<circ>\<^sub>s \<mu> ^^ ?n0"
        have 0:"?N \<ge> ?n0" by simp
        have "?O = hole_pos ?C'" using ctxt_subst_ctxt_hole_pos by auto
        from geq have 1:"?O \<le>\<^sub>p ?p^ ?N @ q @ q'" by (simp add: power_append_distr)
        from pos_eq have 2: "?p ^ ?N @ q <\<^sub>p ?O @ ?o" by (simp add: power_append_distr)
        have "ctxt_subst C \<mu> ?N t =  ctxt_subst C \<mu> ?n0 (ctxt_subst C \<mu> n t)" using ctxt_subst_add by auto
        with ctxt_eq have "\<dots> = ctxt_subst C \<mu> ?n0 (C'\<langle>(L \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>\<rangle>)" by auto
        also have "\<dots> = ?C'\<langle>((L \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>) \<cdot> \<mu> ^^ ?n0\<rangle>" using ctxt_subst_ctxt by blast 
        also have "\<dots> = ?C'\<langle>L\<langle>u\<rangle> \<cdot> ?\<sigma>'\<rangle>" using subst_apply_term_ctxt_apply_distrib by simp
        finally have 3:"ctxt_subst C \<mu> ?N t = ?C'\<langle>L\<langle>u\<rangle> \<cdot> ?\<sigma>'\<rangle>" by auto
        have "hole_pos ?C' = ?O" using ctxt_subst_ctxt_hole_pos by simp 
        with 0 1 2 3 show ?thesis by blast
      qed
      then obtain n' o' \<sigma>' C' where 
        geq:"o' \<le>\<^sub>p ?p ^ n' @ q @ q'" and nn00:"n' \<ge> ?n0" and hole_pos_C':"hole_pos C' = o'" and
        pos_eq:"?p ^ n' @ q <\<^sub>p o' @ ?o" and  ctxt_eq:"ctxt_subst C \<mu> n' t = C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>'\<rangle>" by auto
      then have nn0':"(n' - ?n0) + ?n0 = n'" by (metis le_add_diff_inverse2)
      with geq have "o' \<le>\<^sub>p ?p ^ (n' - ?n0) @ (?p^?n0 @ q @ q')" using power_append_distr append_assoc by metis
      then have np:"\<not> (o' \<bottom> ?p ^ (n' - ?n0))" using pos_less_eq_append_not_parallel by auto
      have "?p ^ (n' - ?n0) \<le>\<^sub>p o'" 
      proof (rule ccontr)
        assume "\<not>(?p ^ (n' - ?n0) \<le>\<^sub>p o')"
        then have "o' <\<^sub>p ?p ^ (n' - ?n0)" using np pos_cases by (metis parallel_pos_sym)
        then have 1:"size o' + size ?o < size (?p ^ (n' - ?n0)) + size ?o" using prefix_smaller parallel_pos_sym by auto
        have 2:"size (?p ^ (n' - ?n0)) + size (?p ^ ?n0 @ q) = size (?p ^ n' @ q)" using nn0'
          by (metis append.assoc length_append power_append_distr)
        also have "\<dots> < size (?p ^ (n' - ?n0)) + size ?o" using pos_eq prefix_smaller 1 2 by fastforce
        finally have "size (?p ^ ?n0 @ q) < size ?o" using add_le_cancel_left not_le by auto
        then show False using size_n0[OF pNonNil] leD by blast
      qed
      then obtain o'' where dec_o':"o' = ?p ^ (n' - ?n0) @ o''" using less_eq_pos_def by metis
      have "o' \<le>\<^sub>p ?p^(n'-?n0) @ ?p^?n0 @ q @ q'" using geq nn0' power_append_distr by (metis append_assoc add.commute)
      with dec_o' have x:"o'' \<le>\<^sub>p ?p^?n0 @ q @ q'" by force
      from nn0' have dec_pn:"?p^n' = ?p^(n'-?n0) @ ?p^?n0"using power_append_distr by metis
      with pos_eq dec_o' nn0' have "?p^(n'-?n0) @ ?p^?n0 @ q <\<^sub>p ?p ^ (n' - ?n0) @ o'' @ ?o" using append_assoc by auto
      then have y:"?p^?n0 @ q <\<^sub>p o''@ ?o" by simp
      let ?mp = "((?cs ?n0 t) |_ o'', L\<langle>u\<rangle>)"
      let ?v="(?cs ?n0 t) |_ o''"
      define property where "property = (\<lambda> v. (\<exists>o'' q'. v = (?cs ?n0 t) |_ o'' \<and> o'' \<le>\<^sub>p ?p^?n0 @ q @ q' \<and> q @ q' \<in> poss t \<and> ?p^?n0 @ q <\<^sub>p o'' @ ?o))"
      from  x y qq' have "\<exists> v. v = ?v \<and> property v" unfolding property_def by auto
      then have "?mp \<in> {(v, L\<langle>u\<rangle>) | v. property v}" by auto
      then have mp:"?mp \<in> a_match_probs L\<langle>u\<rangle> ?o q C t" unfolding property_def a_match_probs_def using t_q_fun by (cases "t|_q", auto)
      have "match_solution ?mp (n' - ?n0, \<sigma>')"
      proof -
        have a:"?p^?n0 \<in> poss (?cs ?n0 t)" by (metis ctxt_subst_hole_pos)
        then have pos_ctxt_subst:"?p^(n'-?n0) \<in> poss (ctxt_subst C \<mu> n' t)" using nn0' ctxt_subst_hole_pos ctxt_subst_add by metis 
        from a qq' have "?p^?n0 @ q @ q' \<in> poss (ctxt_subst C \<mu> ?n0 t)" 
          using ctxt_subst_hole_pos ctxt_subst_subt_at poss_append_poss poss_imp_subst_poss by metis
        with geq have "o'' \<in> poss (ctxt_subst C \<mu> ?n0 t)" using less_eq_pos_def poss_append_poss x by metis
        then have "(?cs ?n0 t) |_ o'' \<cdot> \<mu> ^^ (n' - ?n0) = (?cs ?n0 t) \<cdot> \<mu> ^^ (n' - ?n0) |_ o''" 
          by auto
        also have "\<dots> = (?cs (n'-?n0) (?cs ?n0 t)) |_ ?p ^ (n' - ?n0) |_ o''" by (metis ctxt_subst_subt_at)
        also have "\<dots> = (?cs n' t) |_ ?p ^ (n' - ?n0) |_ o''" using nn0' by (metis ctxt_subst_add)
        also have "\<dots> = (?cs n' t) |_ o'" using dec_o' subt_at_append[OF pos_ctxt_subst] by auto
        also have "\<dots> =  L\<langle>u\<rangle> \<cdot> \<sigma>'" using ctxt_eq hole_pos_C' by auto
        finally show ?thesis using match_solution_def by force
      qed
      with mp show ?thesis by auto
    qed
  next
    case False note caseB=this (* case (b) *)
    let ?o' = "hole_pos C'"
    from ctxt_eq0 pos_eq0 have match_C':"?match C' \<sigma> n" by auto
    have "\<exists> q' x. ?p^n @ q @ q' <\<^sub>p ?o' \<and> q @ q' \<in> poss t \<and> Var x = t |_ (q @ q')"
    proof -
      from pos_eq0 obtain p0 where pos_eq':"?p^n @ (q @ p0) = ?o' @ ?o" and "?p^n @ q \<noteq> ?o' @ ?o" unfolding less_pos_def less_eq_pos_def by auto
      with caseB match_C' have qp0t:"q @ p0 \<notin> poss t" by force
      from ctxt_eq0 pos_eq' have "?p^n @ (q @ p0) \<in> poss (ctxt_subst C \<mu> n t)" by auto
      then have "q @ p0 \<in> poss (t \<cdot> \<mu>^^n)" using ctxt_subst_hole_pos by auto
      with qp0t obtain q0 q1 x where pos_eq:"q @ p0 = q0 @ q1" and q0pos:"q0 \<in> poss t" and var:"t |_ q0 = Var x" using pos_into_subst by metis
      have "\<exists>p3. q0 = q @ p3 \<and> p0 = p3 @ q1" (is ?E)
      proof(rule ccontr)
        assume a:"\<not> ?E"
        with pos_eq obtain q3 where dec_q:"q = q0 @ q3" and dec_q1:"q1 = q3 @ p0" using pos_append_cases[of q p0 q0 q1] by auto
        with var qt have "t |_ (q0 @ q3) = Var x" by auto
        with var have "q3 = []" by (metis is_VarI t_q_fun dec_q)
        with dec_q dec_q1 a show False by auto
      qed
      then obtain p3 where dec_q0:"q0 = q @ p3" and dec_p0:"p0 = p3 @ q1" by auto
      from  q0pos dec_q0 have "q @ p3 \<in> poss t" by auto
      with caseB match_C' have not_geq:"\<not>(?o' \<le>\<^sub>p ?p ^ n @ q @ p3)" by auto
      from pos_eq' dec_p0 have a:"?o' \<le>\<^sub>p (?p ^ n @ q @ p3) @ q1" by auto
      then have "\<not>(?p ^ n @ q @ p3 \<bottom> ?o')" using pos_less_eq_append_not_parallel[OF a] parallel_pos_sym by blast
      with not_geq have "?p ^ n @ q @ p3 <\<^sub>p ?o'" using parallel_pos
        using pos_cases by auto
      with var q0pos dec_q0 show ?thesis by auto
    qed
    then obtain q' x where o':"?p^n @ q @ q' <\<^sub>p ?o'" and qq':"q @ q' \<in> poss t" and varx:"Var x = t |_ (q @ q')" by auto
    from qq' have qq'':"q @ q' \<in> poss (t \<cdot> \<mu>^^n)" using poss_imp_subst_poss by blast
    from o' obtain o'' where dec_o':"?o' = ?p^n @ q @ q' @ o''" and oe:"[] <\<^sub>p o''" 
      unfolding less_pos_def less_eq_pos_def using append_assoc append_Nil2
      by (metis same_append_eq)
    then have "(ctxt_subst C \<mu> n t) |_ ?o' = (ctxt_subst C \<mu> n t) |_ ?p^n |_ (q @ q' @ o'')" by auto
    also have "\<dots> = t \<cdot> \<mu> ^^ n |_ (q @ q' @ o'')" by auto
    also have "\<dots> = t |_ (q @ q') \<cdot> \<mu>^^n |_ o''" using subt_at_append[OF qq''] subt_at_subst[OF qq'] using append_assoc by metis
    finally have eq:"(ctxt_subst C \<mu> n t) |_ ?o' =  t |_ (q @ q') \<cdot> \<mu>^^n |_ o''" by auto
    then have eq:"L\<langle>u\<rangle> \<cdot> \<sigma> =  t |_ (q @ q') \<cdot> \<mu>^^n |_ o''" using ctxt_eq0 by auto 
    from ctxt_eq0 have "?o' \<in> poss (ctxt_subst C \<mu> n t)" using hole_pos_poss by auto
    with dec_o' have "?p^n @ q @ q' @ o''  \<in> poss (ctxt_subst C \<mu> n t)" by auto
    then have "q @ q' @ o'' \<in> poss (t \<cdot> \<mu>^^n)" using ctxt_subst_subt_at poss_append_poss by auto
    with qq' varx have o'': "o'' \<in> poss (Var x \<cdot> \<mu>^^n)" by simp
    from eq varx have "L\<langle>u\<rangle> \<cdot> \<sigma> =  Var x \<cdot> \<mu>^^n |_ o''" by auto
    then obtain C' where "C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle> =  Var x \<cdot> \<mu>^^n" using subt_at_imp_ctxt o'' by auto
    then have rs:"redex_solution (Var x, L\<langle>u\<rangle>) (n,\<sigma>, C')" unfolding redex_solution_def by auto
    from match_prob_of_rp_complete[of "Var x" "L\<langle>u\<rangle>", OF rs, unfolded match_prob_of_rp_def split term.simps]
    have "\<exists> \<tau> s v j. s \<in> {Var x} \<union> \<mu> ` W (Var x) \<and> s \<unrhd> v \<and> is_Fun v \<and> match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" using lfun by (cases "L\<langle>u\<rangle>", auto)
    then obtain  \<tau> s v j where s_in:"s \<in> {Var x} \<union> \<mu> ` W (Var x)" and sv:"s \<unrhd> v" and fun_v:"is_Fun v" and sol:"match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" by blast
    from sv fun_v have "s \<noteq> Var x" by (metis is_VarI supteq_Var_id)
    with s_in have s_in:"s \<in> \<mu> ` W (Var x)" by auto 
    from varx qt have "t |_ q \<unrhd> Var x" by (metis less_eq_pos_imp_supt_eq less_eq_pos_simps(1) qq')
    then have "\<forall> i. t |_ q \<cdot> \<mu> ^^ i \<unrhd> Var x  \<cdot> \<mu> ^^ i" by auto
    then have "\<forall> i. vars_term(Var x  \<cdot> \<mu> ^^ i) \<subseteq> vars_term (t |_ q \<cdot> \<mu> ^^ i)" using supteq_imp_vars_term_subset by auto
    then have "W (Var x) \<subseteq> W (t |_ q)" using varx unfolding vars_iteration_def by auto
    with s_in have s_in:"s \<in> \<mu> ` W (t |_ q)" by auto 
    from s_in sv fun_v have "(v, L\<langle>u\<rangle>) \<in> a_match_probs L\<langle>u\<rangle> ?o q C t" unfolding a_match_probs_def using t_q_fun by (cases "t|_q", auto)
    with sol show "\<exists> mp n \<sigma>. mp \<in> a_match_probs L\<langle>u\<rangle> ?o q C t \<and> match_solution mp (n, \<sigma>)" by auto
  qed
qed

(* Loops Involving Forbidden Patterns of Type (_, _, B) *)

definition n0b :: "pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> nat"
  where "n0b p q oo \<equiv> nat (ceiling (rat_of_nat (Suc (size oo) - size q) / (rat_of_nat (size p))))"

lemma n0_n0b:"n0b p q oo = n0 p q (Cons 0 oo)" unfolding n0_def n0b_def by auto 

lemma n0b_min:
  assumes eq:"(size (p ^ n)) + size q > (size oo)"
    and p:"p \<noteq> Nil" 
  shows "n \<ge> n0b p q oo"
proof -
  from eq have "(size (p ^ n)) + size q \<ge> (size (Cons 0 oo))" by simp
  from n0_min[OF this p] show ?thesis using n0_n0b by simp
qed

lemma size_n0b: 
  assumes p:"p \<noteq> Nil" 
  shows "size (p ^ (n0b p q oo) @ q) > size oo" unfolding n0_n0b 
proof(rule Suc_le_lessD[unfolded Suc_eq_plus1])
  from size_n0[OF p, of "Cons 0 oo"] show "size oo + 1 \<le> size (p ^ n0 p q (Cons 0 oo) @ q)" by auto
qed

definition b_match_probs :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" where
  "b_match_probs l oo q C t \<equiv> \<Union> {h_match_probs l oo q' C t | q'. q' <\<^sub>p q}"


definition b_ematch_probs :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow>  pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ematch_prob set" where
  "b_ematch_probs l oo q C t \<equiv> 
  {(C |_c p', l, C \<cdot>\<^sub>c \<mu>, t') | p' p'' t'. 
   p' @ p'' = hole_pos C \<and> p' <\<^sub>p hole_pos C \<and> t'= (ctxt_subst C \<mu> (n0b (hole_pos C) p'' oo) t) \<cdot> \<mu> \<and> 
   (oo <\<^sub>p p'' @ (hole_pos C)^ (n0b (hole_pos C) p'' oo))}"

lemma b_match_probs_sound:
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and sol: "match_solution mp (n, \<sigma>)"
    and mp: "mp \<in> b_match_probs l oo q C t"
  shows "\<not> fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.B) C \<mu> q t"
proof -
  let ?p = "hole_pos C"
  let ?l = "(ctxt_of_pos_term oo l)\<langle>l|_oo\<rangle>"
  let ?pt = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.H)"
  let ?pt' = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.B)"
  from mp[unfolded b_match_probs_def] obtain q' where q': "q' <\<^sub>p q" and mp: "mp \<in> h_match_probs l oo q' C t" by auto
  have l:"(ctxt_of_pos_term oo l)\<langle>l|_oo \<rangle> = l" using ctxt_supt_id ol by auto
  have l':"hole_pos (ctxt_of_pos_term oo l) = oo" using hole_pos_ctxt_of_pos_term ol by metis
  from l have ls:" \<forall> \<sigma>. (ctxt_of_pos_term oo l \<cdot>\<^sub>c \<sigma>)\<langle>l |_ oo \<cdot> \<sigma>\<rangle> = l  \<cdot> \<sigma>" by (metis subst_apply_term_ctxt_apply_distrib)
  from qt q' have "q' \<in> poss t" using less_pos_def' poss_append_poss by force
  with mp have "\<not> fpstep_ctxt_subst_cond ?pt C \<mu> q' t" using fp_h_match_probs_sound qt ol sol by auto
  then obtain n where " \<not> fpstep_cond_single ?pt (?p ^ n @ q') (ctxt_subst C \<mu> n t)" using fpstep_ctxt_subst_cond_def by blast
  then have "\<exists>C' \<sigma>. ctxt_subst C \<mu> n t = C'\<langle>(ctxt_of_pos_term oo l \<cdot>\<^sub>c \<sigma>)\<langle>l |_ oo \<cdot> \<sigma>\<rangle>\<rangle> \<and>
         ?p ^ n @ q' = hole_pos C' @ oo" unfolding fpstep_cond_single_def using l' by auto
  then obtain C' \<sigma> where c':"ctxt_subst C \<mu> n t = C'\<langle>l \<cdot> \<sigma>\<rangle>" and st:"(?p ^ n @ q') = (hole_pos C') @ oo" using ls l' by metis
  with q' have "hole_pos C' @ oo <\<^sub>p (?p ^ n @ q)" using less_pos_simps(2) by metis
  with c' have "\<exists> C' \<sigma>. (ctxt_subst C \<mu> n t) = C'\<langle>?l \<cdot> \<sigma>\<rangle> \<and> hole_pos C' @ oo <\<^sub>p ?p ^ n @ q" by (metis l)
  then have "\<not> fpstep_cond_single ?pt' (?p ^ n @ q) (ctxt_subst C \<mu> n t)" using l' fpstep_cond_single_def
    by (auto simp: fpstep_cond_single_def)
  then show ?thesis  using fpstep_ctxt_subst_cond_def by blast
qed

lemma b_ematch_probs_sound:
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and sol: "ematch_solution emp (m, k,\<sigma>)"
    and emp: "emp \<in> b_ematch_probs l oo q C t"
  shows "\<not> fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.B) C \<mu> q t"
proof -
  let ?p = "hole_pos C"
  let ?pt' = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.B)"
  let ?cs = "ctxt_subst C \<mu>"
  from emp[unfolded b_ematch_probs_def] obtain p''' p'' t' where emp:"emp = (C |_c p''', l, C \<cdot>\<^sub>c \<mu>, t')" and  
    dec_p:"?p = p''' @ p'' " and pp':"p''' <\<^sub>p ?p" and t':"t' = ?cs (n0b ?p p'' oo) t \<cdot> \<mu>" and 
    ineq:"oo <\<^sub>p p'' @ ?p^ (n0b ?p p'' oo)" by force
  then have p_nonempty:"?p \<noteq> []" by auto
  let ?D = "C |_c p'''"
  let ?n0 = "n0b ?p p'' oo"
  let ?t' = "?cs (n0b ?p p'' oo) t \<cdot> \<mu>"
  from emp t' sol[unfolded ematch_solution_def] have eq:"l \<cdot> \<sigma> = ?D \<langle>ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu> m ?t'\<rangle> \<cdot> \<mu> ^^ k" by fastforce
  have hpD:"hole_pos ?D = p''" using hole_pos_subt_at_ctxt[OF dec_p] by simp
  have Cp':"\<forall>t. p''' \<in> poss C \<langle>t\<rangle>" using dec_p by (metis hole_pos_poss poss_append_poss)
  let ?o' = "?p ^k @ p'''"
  let ?nn = "k + Suc(m + ?n0)"
  define C' where "C' = ctxt_of_pos_term ?o' (?cs ?nn t)"
    (* some position reasoning *)
  have pk:"?p ^k \<in> poss (?cs ?nn t)" by (metis ctxt_subst_add ctxt_subst_hole_pos)
  from dec_p have a':"p''' \<in> poss (?cs (Suc (m + ?n0)) t)" using Cp' by auto
  then have "?o' \<in> poss (?cs k (?cs (Suc(m + ?n0)) t))" using ctxt_subst_subt_at pos_append_poss poss_imp_subst_poss by force
  then have o'poss:"?o' \<in> poss (?cs ?nn t)" using ctxt_subst_add by metis
  then have hC':"hole_pos C' = ?o'" unfolding C'_def using hole_pos_ctxt_of_pos_term by blast
  have l:"(ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle> = l" using ctxt_supt_id ol by fast
  have l':"hole_pos (ctxt_of_pos_term oo l) = oo" using hole_pos_ctxt_of_pos_term ol by force
      (* some term reasoning *)
  from pk have "(?cs ?nn t) |_?o' = (?cs ?nn t) |_ ?p ^k |_ p'''" using subt_at_append by auto
  also have "\<dots> = (?cs k (?cs (Suc (m + ?n0)) t)) |_ ?p ^k |_ p'''" using ctxt_subst_add by metis
  also have "\<dots> = (?cs (Suc (m + ?n0)) t) \<cdot> \<mu> ^^ k |_ p'''" using ctxt_subst_subt_at[of C] by presburger
  also have "\<dots> = C \<langle>(?cs (m + ?n0) t) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k |_ p'''" using ctxt_subst_ctxt_Suc by auto
  also have "\<dots> = C \<langle>(?cs (m + ?n0) t) \<cdot> \<mu>\<rangle> |_ p''' \<cdot> \<mu> ^^ k"
    using Cp' by (auto simp del: subt_at_subst simp: subt_at_subst [symmetric])
  also have "\<dots> = ?D \<langle>(?cs (m + ?n0) t) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k" using subt_at_subt_at_ctxt[OF dec_p] hpD by force
  also have "\<dots> = ?D \<langle>((?cs m (?cs ?n0 t))) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k" using ctxt_subst_add by simp
  also have "\<dots> = ?D \<langle>ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu> m ((?cs ?n0 t) \<cdot> \<mu>)\<rangle> \<cdot> \<mu> ^^ k" using ctxt_subst_subst by metis
  finally have "(?cs ?nn t) |_?o' = l \<cdot> \<sigma>" using eq by presburger
  then have eq:"?cs ?nn t = C'\<langle>l \<cdot> \<sigma>\<rangle>" unfolding C'_def hC' by (metis ctxt_supt_id o'poss)
      (* position comparisons *)
  have "?nn = k + 1 + ?n0 + m" unfolding Suc_eq_plus1 by presburger 
  then have "?p^?nn = ?p ^  ((k + Suc ?n0) + m)" by (metis Suc_eq_plus1 add_Suc_right add.commute)
  then have "?p^?nn = ?p ^ k @ ?p ^ 1 @ ?p ^ ?n0 @ ?p ^ m" using power_append_distr by (metis Suc_eq_plus1_left add.commute)
  then have "?p ^ k @ ?p @ ?p ^ ?n0 \<le>\<^sub>p ?p^?nn" by fastforce
  then have a:"?p ^ k @ p''' @ p'' @ ?p ^ ?n0 \<le>\<^sub>p ?p^?nn" unfolding dec_p by auto
  with ineq have "?p ^ k @ p''' @ oo <\<^sub>p ?p^?nn"
    by (simp add: order_pos.dual_order.strict_trans1)
  then have  "?o' @ oo <\<^sub>p ?p^?nn @ q" unfolding less_pos_def' by force
      (* combine to fpstep result *)
  with eq have "\<exists> C' \<sigma>. (?cs ?nn t) = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> hole_pos C' @ oo <\<^sub>p ?p ^ ?nn @ q" using hC' by fastforce
  then have "\<not> fpstep_cond_single ?pt' (?p ^ ?nn @ q) (?cs ?nn t)"
    unfolding fpstep_cond_single_def split l l'
    by (blast)
  then show ?thesis  using fpstep_ctxt_subst_cond_def by blast
qed

lemma fp_b_match_probs_complete:
  assumes nfp:"\<not> fpstep_cond_single (L, u, Forbidden_Patterns.B) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)"
    and qt: "q \<in> poss t"
    and lfun: "is_Fun L\<langle>u\<rangle>"
  shows "(\<exists> mp n \<sigma>. mp \<in> b_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution mp (n, \<sigma>)) \<or>
         (\<exists> emp n k \<sigma> p t'. emp \<in> b_ematch_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> ematch_solution emp (n, k, \<sigma>) \<and> emp = (C |_c p, L\<langle>u\<rangle>, C \<cdot>\<^sub>c \<mu>, t') \<and> p <\<^sub>p hole_pos C)"
proof -
  let ?cs = "ctxt_subst C \<mu>"
  let ?ct = "?cs n t"
  let ?o = "hole_pos L"
  let ?p = "hole_pos C"
  from nfp obtain C' \<sigma> where ctxt_eq:"?ct = C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle>" and pos_eq:"hole_pos C' @ ?o <\<^sub>p ?p ^ n @ q"
    unfolding fpstep_cond_single_def by auto
  let ?o' = "hole_pos C'"
  from qt have a:"?p ^ n @ q \<in> poss ((C ^ n)\<langle>t\<rangle>)" by (induct n, auto)
  with pos_eq have "?o' @ ?o \<in> poss ((C ^ n)\<langle>t\<rangle>)"
    by (metis less_eq_pos_def less_pos_def poss_append_poss)
  show ?thesis 
  proof(cases "?p ^ n \<le>\<^sub>p ?o' @ ?o")
    case True (* o'o ends in t *)
    from pos_eq[unfolded less_pos_def'] obtain o'' where pos_eq':"?p ^ n @ q = ?o' @ ?o @ o''" and oe:"o'' \<noteq> []" by auto
    from True[unfolded less_eq_pos_def] obtain q' where pos_eq'':"?o' @ ?o = ?p ^ n @ q'" by metis
    with pos_eq' have dec_q:"q = q' @ o''" by (metis same_append_eq append_assoc)
    with oe have qq':"q' <\<^sub>p q" by auto
    with qt have qt':"q' \<in> poss t" using dec_q by auto
    from pos_eq'' ctxt_eq have "\<not> fpstep_cond_single (L, u, Forbidden_Patterns.H) (?p ^ n @ q') ?ct" 
      unfolding fpstep_cond_single_def split by auto
    from fp_h_match_probs_complete[OF this qt'] obtain mp n \<sigma> where 
      "mp \<in> h_match_probs L\<langle>u\<rangle> ?o q' C t" and sol:"match_solution mp (n, \<sigma>)" by auto
    with qq' have "mp \<in> b_match_probs L\<langle>u\<rangle> ?o q C t" unfolding b_match_probs_def by auto
    with sol show ?thesis by fast
  next
    case False note caseB=this (* o'o ends in some occurrence of C *)
    have "\<not> (?o' @ ?o \<bottom> ?p ^n)" using pos_eq pos_less_eq_append_not_parallel[of "?o' @ ?o" "?p^n"] order_pos.less_imp_le by auto
    with False have pos_ieq:"?o' @ ?o <\<^sub>p ?p ^n" using pos_cases[of "?p^n" "?o' @ ?o"] parallel_pos_sym by blast
    then have p_nonempty:"?p \<noteq> []" and size_p_gt_0:"size ?p > 0" by auto
    from pos_ieq have  "?o' <\<^sub>p ?p ^n" unfolding less_pos_def' by force
    from less_pos_power_split[OF this] obtain p''' k where dec_o':"?o' = ?p ^ k @ p'''" and kn:"k < n" and "p''' <\<^sub>p ?p" by blast
    then obtain p'' where dec_p:"?p = p''' @ p''" and "p'' \<noteq> []"unfolding less_pos_def' by auto
    then have pp''':"p''' <\<^sub>p ?p" by auto
    let ?m = "n - k - 1"
    from kn have neq:"n = k + 1 + ?m" by auto
    then have "?p ^ n = ?p ^ (k + 1 + ?m)" by auto
    also have "\<dots> = ?p ^k @ p''' @ p'' @ ?p ^?m"  unfolding power_append_distr using dec_p by auto
    finally have pos_ineq:"?o <\<^sub>p p'' @ ?p ^?m" using dec_o' pos_ieq by auto 
    then have sizes:"(size p'') + (size (?p ^ ?m)) > size ?o" using prefix_smaller
      by fastforce
    let ?n0 = "n0b ?p p'' ?o"
    have mn0:"?m \<ge> ?n0" using n0b_min sizes p_nonempty by auto
    then have "\<exists> m'. ?m = ?n0 + m'" by presburger
    then obtain m' where dec_m:"?m = ?n0 + m'" by auto
    let ?D =  "C |_c p'''"
    have CD:"C |_c p''' = ?D" by (metis dec_p subt_at_subt_at_ctxt)
    have poss_p''':"\<forall> v. p''' \<in> poss C \<langle>v\<rangle>" using dec_p hole_pos_poss poss_append_poss by metis
    from ctxt_eq have "L\<langle>u\<rangle> \<cdot> \<sigma> = (?cs (k + 1 + ?m) t) |_ ?o'" using neq by auto
    also have "\<dots> = (?cs (k + 1 + ?m) t) |_ (?p^k @ p''')" using dec_o' by auto
    also have "\<dots> = (?cs k (?cs (1 + ?m) t)) |_ (?p^k @ p''')" using ctxt_subst_add by metis
    also have "\<dots> =  (?cs (Suc ?m) t) \<cdot> \<mu> ^^ k |_ p'''" using ctxt_subst_subt_at by auto
    also have "\<dots> = C \<langle>(?cs ?m t) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k |_ p'''" by simp
    also have "\<dots> = C \<langle>(?cs ?m t) \<cdot> \<mu>\<rangle> |_ p''' \<cdot> \<mu> ^^ k" using poss_p''' subt_at_subst by metis
    also have "\<dots> = ?D \<langle>(?cs ?m t) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k " using CD by (metis dec_p subt_at_subt_at_ctxt)
    also have "\<dots> = ?D \<langle>(?cs m' (?cs ?n0 t)) \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k" using dec_m ctxt_subst_add by (metis add.commute)
    finally have eq:"L\<langle>u\<rangle> \<cdot> \<sigma> = ?D \<langle>(ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu> m' ((?cs ?n0 t) \<cdot> \<mu>))\<rangle> \<cdot> \<mu> ^^ k" using ctxt_subst_subst by metis
    define emp where "emp = (?D, L\<langle>u\<rangle>, C \<cdot>\<^sub>c \<mu>, (?cs ?n0 t) \<cdot> \<mu>)"
    from eq have sol:"ematch_solution emp (m', k,\<sigma>)" unfolding ematch_solution_def split emp_def by simp
    from pp''' have Dh:"?D \<noteq> Hole" using hole_pos_subt_at_ctxt dec_p by fastforce 
    from pos_ineq have pos_ineq':"?o <\<^sub>p p'' @ ?p ^ ?n0 @ ?p^(?m - ?n0)"
      using dec_m by (simp add: power_append_distr)
    from pos_ineq' have "\<not> (?o \<bottom> p'' @ ?p ^ ?n0)" using pos_less_eq_append_not_parallel by (metis append_assoc less_pos_def)
    then have np:"\<not> (p'' @ ?p ^ ?n0 \<bottom> ?o)" using parallel_pos_sym by blast
    have "size (?p ^ ?n0) + size p'' > size ?o" using size_n0b[OF p_nonempty, of ?o] by auto
    then have "size (p'' @ ?p ^ ?n0) > size ?o" by auto
    with pos_ineq' np have ineq:"?o <\<^sub>p p'' @ ?p ^ ?n0" using prefix_smaller pos_cases
      by (metis less_pos_def nat_less_le not_less)
    define ematch where "ematch = (\<lambda> ee. \<exists>p' p'' t'. ee = (C |_c p', L\<langle>u\<rangle>, C \<cdot>\<^sub>c \<mu>, t') \<and> p' @ p'' = hole_pos C \<and>  p' <\<^sub>p hole_pos C \<and>
               t' = (?cs (n0b ?p p'' ?o) t) \<cdot> \<mu> \<and> ?o <\<^sub>p p'' @ ?p ^ (n0b ?p p'' ?o))"
    from sol dec_p pp''' have "ematch emp" unfolding ematch_def emp_def using ineq by force
    then have "emp \<in> {u. ematch u}" by auto
    then have "emp \<in> b_ematch_probs L\<langle>u\<rangle> ?o q C t" unfolding ematch_def b_ematch_probs_def emp_def n0_def by fastforce
    with sol show ?thesis
      unfolding emp_def using CD Dh by (metis pp''')
  qed
qed

(* Loops Involving Forbidden Patterns of Type (_, _, R) *)


definition r_match_probs :: 
  "('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" 
  where "r_match_probs l oo q C t \<equiv> 
   {(u,l) | u q'. q' \<in> poss t \<and> left_of_pos q' q \<and> u = t |_ q'} 
    \<union> {(u, l) | s u q'. s \<in> \<mu> ` W (t |_ q') \<and> s \<unrhd> u \<and> q' \<in> poss t \<and> left_of_pos q' q}
    \<union> {(u,l) | u p'. p' \<in> poss C\<langle>t\<rangle> \<and> left_of_pos p' (hole_pos C) \<and> u = C\<langle>t\<rangle> |_ p'}
    \<union> {(u,l) | s u p'. p' \<in> possc C \<and> left_of_pos p' (hole_pos C) \<and> s \<in> \<mu> ` W (C\<langle>t\<rangle> |_ p') \<and> s \<unrhd> u}"


lemma fp_r_match_probs_sound:
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and mp: "mp \<in> r_match_probs l oo q C t"
    and fl:"is_Fun l"
    and sol: "match_solution mp (n, \<sigma>)"
  shows "\<not> fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.R) C \<mu> q t"
proof-
  let ?M1 = "{(u,l) | u q'. q' \<in> poss t \<and> left_of_pos q' q \<and> u = t |_ q'}"
  let ?M2 = "{(u, l) | s u q'. s \<in> \<mu> ` W (t |_ q') \<and> s \<unrhd> u \<and> q' \<in> poss t \<and> left_of_pos q' q}"
  let ?M3 = "{(u,l) | u p'. p' \<in> poss C\<langle>t\<rangle> \<and> left_of_pos p' (hole_pos C) \<and> u = C\<langle>t\<rangle> |_ p'}"
  let ?M4 = "{(u,l) | s u p'. p' \<in> possc C \<and> left_of_pos p' (hole_pos C) \<and> s \<in> \<mu> ` W (C\<langle>t\<rangle> |_ p') \<and> s \<unrhd> u}" 
  let ?p = "hole_pos C"
  let ?pt = "(ctxt_of_pos_term oo l, l|_oo, Forbidden_Patterns.R)"
  let ?cs = "ctxt_subst C \<mu>"
  have l:" (ctxt_of_pos_term oo l)\<langle>l|_oo \<rangle> = l" using ctxt_supt_id ol by metis
  have l':"hole_pos (ctxt_of_pos_term oo l) = oo" using ol hole_pos_ctxt_of_pos_term by blast
  from mp[unfolded r_match_probs_def] have C:"mp \<in> ?M1 \<or> mp \<in> ?M2 \<or> mp \<in> ?M3 \<or> mp \<in> ?M4" by auto 
  show ?thesis 
  proof(cases "mp \<in> ?M1")
    case True
    then obtain u q' where mp:"mp = (u, l)" and qt:"q' \<in> poss t" and 
      left:"left_of_pos q' q" and u:"u = t |_ q'" by auto
    from split_conv sol[unfolded match_solution_def mp] u have "t|_q' \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" by force
    with subt_at_subst[OF qt] have "(t \<cdot> \<mu> ^^ n)|_ q' = l \<cdot> \<sigma>" by metis
    with ctxt_subst_subt_at[of C \<mu> n t] have e:"(ctxt_subst C \<mu> n t) |_ (?p ^ n @ q') = l \<cdot> \<sigma>"
      by (metis ctxt_subst_hole_pos subt_at_append)
    from qt poss_imp_subst_poss[OF qt] ctxt_subst_hole_pos ctxt_subst_subt_at poss_append_poss 
    have qt':"(?p ^ n @ q') \<in> poss (ctxt_subst C \<mu> n t)" by metis
    define D where "D = ctxt_of_pos_term (?p ^ n @ q') (?cs n t)"
    have d:"hole_pos D = ?p ^ n @ q'" using hole_pos_ctxt_of_pos_term[OF qt'] unfolding D_def by fast
    with e ctxt_supt_id[OF qt'] have cs:"?cs n t = D\<langle>l \<cdot> \<sigma>\<rangle>" unfolding D_def by force
    from left d have "left_of_pos (hole_pos D) (?p^n @ q)" using append_left_of_pos by auto
    with cs have "\<exists> C'. ?cs n t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> left_of_pos (hole_pos C') (?p^n @q)" by metis
    with l hole_pos_ctxt_of_pos_term[OF ol] show "\<not> fpstep_ctxt_subst_cond ?pt C \<mu> q t" 
      unfolding fpstep_ctxt_subst_cond_def[unfolded fpstep_cond_single_def] unfolding split_conv 
      by (simp add:l,force)
  next 
    case False note False2=this
    then show ?thesis proof(cases "mp \<in> ?M2")
      case True
      then obtain s u q' where mp:"mp = (u, l)" and "s \<in> \<mu> ` (vars_iteration \<mu> (t |_ q'))" 
        and su:"s \<unrhd> u" and lqq:"left_of_pos q' q" and qt':"q' \<in> poss t" by auto
      then obtain x where s_mu_x:"s = \<mu>(x)" and "x \<in> vars_iteration \<mu> (t |_ q')" by auto
      then obtain i where "x \<in> vars_term (t |_ q' \<cdot> \<mu> ^^ i)" unfolding vars_iteration_def by auto
      then obtain o'' where tx:"(t |_ q' \<cdot> \<mu> ^^ i) |_ o'' = Var x" and ot:"o'' \<in> poss (t |_q' \<cdot> \<mu> ^^ i)" 
        using supteq_imp_subt_at vars_term_supteq(1)[of x] by blast
      from supteq_imp_subt_at[OF su,unfolded s_mu_x] 
      obtain r where u:"(Var x) \<cdot> \<mu> |_r = u" and r:"r \<in> poss (Var x \<cdot> \<mu>)" by auto
      with split_conv sol[unfolded match_solution_def mp] have "((Var x) \<cdot> \<mu> |_r) \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" by force
      then have e:"((Var x) \<cdot> \<mu> \<cdot> \<mu> ^^ n |_r) = l \<cdot> \<sigma>" using subt_at_subst[OF r, of "\<mu> ^^ n"] by auto 
      let ?n = "i + Suc n"
      let ?o' = "?p ^ ?n @ q' @ o'' @ r"
      let ?t = "ctxt_subst C \<mu> ?n t"
      have eq:"?t |_ ?o' = l \<cdot> \<sigma>"
      proof -
        have t_o':"?t |_ ?o' = ?t |_ ?p^?n |_ (q' @ o'' @ r)" using subt_at_append ctxt_subst_hole_pos[of _ ?n] by blast
        also have "\<dots> = t |_q' \<cdot> \<mu> ^^ ?n |_ (o'' @ r)" using ctxt_subst_subt_at[of C \<mu> ?n] qt' by auto
        also have "\<dots> = t |_q' \<cdot> (\<mu> ^^ i \<circ>\<^sub>s \<mu> ^^ (Suc n)) |_ (o'' @ r)" using subst_power_compose_distrib by metis
        also have "\<dots> = t |_q' \<cdot> \<mu> ^^ i |_ o'' \<cdot> \<mu> ^^ (Suc n) |_ r" using subst_subst ot by simp
        also have "\<dots> = (Var x) \<cdot> \<mu> \<cdot> \<mu> ^^ n |_ r" using tx subst_monoid_mult.power_Suc2 by (auto simp: subst_compose)
        finally show ?thesis using e unfolding match_solution_def by auto
      qed
      have ot: "?o' \<in> poss ?t"
      proof-
        from tx u have  "(t |_ q' \<cdot> \<mu> ^^ i) \<cdot> \<mu> |_ o'' = (Var x) \<cdot> \<mu>" using subt_at_subst ot by force
        with r ot have "o'' @ r \<in> poss (t |_q' \<cdot> \<mu> ^^ i \<cdot> \<mu>)" using pos_append_poss[OF ot] by auto 
        with qt' have "q' @ o'' @ r \<in> poss (t \<cdot> \<mu> ^^ i \<cdot> \<mu>)" using pos_append_poss[OF ot] poss_append_poss by auto
        then have qor:"q' @ o'' @ r \<in> poss (t \<cdot> \<mu> ^^ (Suc i))" using subst_subst subst_power_Suc by metis
        let ?s = "ctxt_subst (C \<cdot>\<^sub>c (\<mu> ^^ (Suc i) )) \<mu> n (t \<cdot> \<mu> ^^ (Suc i))"
        have ax:"?s |_ ?p^n = (t \<cdot> \<mu> ^^ (Suc i)) \<cdot> \<mu> ^^ n" using ctxt_subst_subt_at hole_pos_subst by metis
        have ps:"?p^n \<in> poss ?s" using hole_pos_subst ctxt_subst_hole_pos by metis
        with qor ax have pqor:"?p ^ n @ (q' @ o'' @ r) \<in> poss ?s" using 
            pos_append_poss[OF ps] poss_imp_subst_poss by metis
        have ce:"(?cs n t) \<cdot> (\<mu> ^^ (Suc i)) = ?s" using ctxt_subst_subst_pow by blast
        with pqor have pqor:"?p ^ n @ (q' @ o'' @ r) \<in> poss ((?cs n t) \<cdot> (\<mu> ^^ (Suc i)))" by auto
        have cc:"?cs ((Suc i) + n) t = ctxt_subst C \<mu> (Suc i) (?cs n t)" using ctxt_subst_add by auto
        from cc have tp:"?t |_ ?p^(Suc i) = (?cs n t) \<cdot> (\<mu> ^^ (Suc i))" using ctxt_subst_subt_at[of C \<mu> "Suc i"] by auto
        with pqor have pqor:"?p ^ n @ (q' @ o'' @ r) \<in> poss (?t |_ ?p^(Suc i))" by auto
        have pit:"?p^(Suc i) \<in> poss ?t" using ctxt_subst_add ctxt_subst_hole_pos by auto
        with pqor show ?thesis
          using pos_append_poss[OF pit pqor] by (auto simp: power_append_distr)
      qed
      let ?q = "?p^?n @ q"
      from left_of_pos_append[OF lqq] append_left_of_pos pos_append_cases
      have left:"left_of_pos ?o' ?q" by metis
      let ?C' = "ctxt_of_pos_term ?o' ?t"
      from eq ot have t_ctxt:"?t = ?C'\<langle>l \<cdot> \<sigma>\<rangle>" using ctxt_supt_id by metis
      have "hole_pos ?C' = ?o'" by (metis hole_pos_ctxt_of_pos_term ot)
      with t_ctxt left have "\<exists>C' \<sigma>. ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> left_of_pos (hole_pos C') (?p ^ ?n @ q)" by auto
      then have "\<not> fpstep_cond_single ?pt ?q ?t" unfolding fpstep_cond_single_def[of ?pt ?q ?t] split_conv l l' by simp
      then show ?thesis unfolding fpstep_ctxt_subst_cond_def[of ?pt C \<mu> q t] by fast
    next
      case False note False3=this
      then show ?thesis proof(cases "mp \<in> ?M3")
        case True
        then obtain u p' where mp:"mp = (u, l)" and pt:"p' \<in> poss C\<langle>t\<rangle>"
          and lqq:"left_of_pos p' ?p" and up':"u = C\<langle>t\<rangle> |_ p'" by auto
        from split_conv sol[unfolded match_solution_def mp] up' have c:"C\<langle>t\<rangle> |_ p' \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" by force
        have " C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ n = l \<cdot> \<sigma> \<and> p' \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>"
        proof-
          have par:"?p \<bottom> p'" using left_pos_parallel[OF lqq] by auto
          have "C\<langle>t \<cdot> \<mu>\<rangle> |_ p' = C\<langle>t\<rangle> |_ p'" 
            using ctxt_of_pos_term_hole_pos parallel_replace_at_subt_at[OF par hole_pos_poss pt] by metis
          with c have c:"C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" by auto
          from ctxt_poss_imp_ctxt_subst_poss[OF pt] have "p' \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>" by auto
          with c show ?thesis by auto
        qed
        then have "C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" and pt:"p' \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>" by auto 
        then have "C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ n  |_ p' = l \<cdot> \<sigma>" using subt_at_subst[OF pt] by metis
        with ctxt_subst_subt_at[of C \<mu> n "C\<langle>t \<cdot> \<mu>\<rangle>"] have "?cs n C\<langle>t \<cdot> \<mu>\<rangle> |_ (?p ^ n @ p') = l \<cdot> \<sigma>" by auto
        with ctxt_subst_Suc have e:"?cs (Suc n) t |_ (?p ^ n @ p') = l \<cdot> \<sigma>" by metis
        define C' where "C' = ctxt_of_pos_term (?p ^ n @ p') (?cs (Suc n) t)"
        from pt have "?p ^ n @ p' \<in> poss (?cs n C\<langle>t \<cdot> \<mu>\<rangle>)" using ctxt_subst_hole_pos[of C n] 
            ctxt_subst_subt_at poss_append_poss[of "?p ^ n" p'] by (metis poss_imp_subst_poss)
        then have pt:"?p ^ n @ p' \<in> poss (?cs (Suc n) t)" using ctxt_subst_Suc by metis
        have hc:"hole_pos C' = ?p ^ n @ p'" unfolding C'_def using hole_pos_ctxt_of_pos_term[OF pt] by fast
        let ?q = "?p ^(Suc n) @ q"
        let ?t = "?cs (Suc n) t"
        from  append_left_of_pos left_of_pos_append[OF lqq, of "[]" q]
        have left:"left_of_pos (hole_pos C') ?q" unfolding hc power_pos_Suc by auto
        from ctxt_supt_id[OF pt, unfolded e] have cs:"?t = C'\<langle>l \<cdot> \<sigma>\<rangle>" unfolding C'_def by auto
        from cs left have "\<exists>C' \<sigma>. ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> left_of_pos (hole_pos C') ?q" by auto
        then have "\<not> fpstep_cond_single ?pt ?q ?t" unfolding fpstep_cond_single_def[of ?pt] split_conv l l' by simp
        then show ?thesis unfolding fpstep_ctxt_subst_cond_def[of ?pt C \<mu> q t] by fast
      next
        case False 
        then have "mp \<in> ?M4" using False2 False3 C by fast
        then obtain s u p' where mp:"mp = (u, l)" and  pt':"p' \<in> possc C" and lqq:"left_of_pos p' ?p"
          and "s \<in> \<mu> ` (vars_iteration \<mu> (C\<langle>t\<rangle> |_ p'))" and su:"s \<unrhd> u" by auto
        then obtain x where s_mu_x:"s = \<mu>(x)" and "x \<in> vars_iteration \<mu> (C\<langle>t\<rangle> |_ p')" by auto
        then obtain i where "x \<in> vars_term (C\<langle>t\<rangle> |_ p' \<cdot> \<mu> ^^ i)" unfolding vars_iteration_def by auto
        then obtain o'' where tx:"(C\<langle>t\<rangle> |_ p' \<cdot> \<mu> ^^ i) |_ o'' = Var x" and ot:"o'' \<in> poss (C\<langle>t\<rangle> |_p' \<cdot> \<mu> ^^ i)"
          using supteq_imp_subt_at vars_term_supteq(1)[of x] by blast
        from supteq_imp_subt_at[OF su,unfolded s_mu_x] 
        obtain r where u:"(Var x) \<cdot> \<mu> |_r = u" and r:"r \<in> poss (Var x \<cdot> \<mu>)" by auto
        with split_conv sol[unfolded match_solution_def mp] have xls:"((Var x) \<cdot> \<mu> |_r) \<cdot> \<mu> ^^ n = l \<cdot> \<sigma>" by force
        then have e:"((Var x) \<cdot> \<mu> \<cdot> \<mu> ^^ n |_r) = l \<cdot> \<sigma>" using subt_at_subst[OF r, of "\<mu> ^^ n"] by auto 
        let ?n = "i + Suc n"
        let ?o' = "?p ^ ?n @ p' @ o'' @ r"
        let ?t = "ctxt_subst C \<mu> (Suc ?n) t"
        have aux:"?p^ ?n \<in> poss ?t" using ctxt_subst_hole_pos ctxt_subst_Suc by metis
        from pt' have pt':"p' \<in> poss C\<langle>t \<cdot> \<mu>\<rangle>" unfolding possc_def by blast
        from lqq have par:"?p \<bottom> p'" by (rule left_pos_parallel)
        then have aux2:"C\<langle>t\<rangle> |_p' =  C\<langle>t \<cdot> \<mu>\<rangle> |_p'" using parallel_replace_at_subt_at[OF par hole_pos_poss pt', unfolded ctxt_of_pos_term_hole_pos] by auto
        have eq:"?t |_ ?o' = l \<cdot> \<sigma>"
        proof -
          have t_o':"?t |_ ?o' = ?t |_ ?p^?n |_ (p' @ o'' @ r)" using subt_at_append aux by blast
          also have "\<dots> = (ctxt_subst C \<mu> (i+ Suc n) C\<langle>t \<cdot> \<mu>\<rangle>) |_ ?p^(i+Suc n) |_ (p' @ o'' @ r)"  using ctxt_subst_Suc[of C \<mu>] by auto
          also have "\<dots> =  C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ (i + Suc n)|_ (p' @ o'' @ r)" using ctxt_subst_subt_at[of C \<mu>] by presburger 
          also have "\<dots> = (C\<langle>t \<cdot> \<mu>\<rangle>|_ p') \<cdot> \<mu> ^^ ?n |_ (o'' @ r)" using 
              subt_at_subst[OF pt', of "\<mu> ^^ ?n"] poss_imp_subst_poss[OF pt'] subt_at_append by metis
          also have "\<dots> = (C\<langle>t\<rangle>|_ p') \<cdot> \<mu> ^^ ?n |_ (o'' @ r)" using aux2 by auto
          also have "\<dots> = (C\<langle>t\<rangle> |_p') \<cdot> (\<mu> ^^ i \<circ>\<^sub>s (\<mu> ^^ Suc n)) |_ (o'' @ r)" using subst_power_compose_distrib by metis
          also have "\<dots> = C\<langle>t\<rangle> |_p' \<cdot> \<mu> ^^ i |_ o'' \<cdot> \<mu> ^^ Suc n |_ r" using subst_subst ot
              ctxt_poss_imp_ctxt_subst_poss by simp
          also have "\<dots> = (Var x) \<cdot> \<mu> \<cdot> \<mu> ^^ n |_ r" using tx subst_monoid_mult.power_Suc2 by (force simp: subst_compose)
          finally show ?thesis using e xls by auto
        qed   
        have ot: "?o' \<in> poss ?t"
        proof-
          from tx ot aux2 have tx':"C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ i \<cdot> \<mu> |_ o'' = Var x \<cdot> \<mu>" and 
            ot':"o'' \<in> poss (C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ i \<cdot> \<mu>)" by auto
          from r tx' pos_append_poss[OF ot',unfolded tx'] pt' have "o'' @ r \<in> poss ((C\<langle>t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ i) \<cdot> \<mu>)" by blast
          then have "o'' @ r \<in> poss ((C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> (\<mu> ^^ i \<circ>\<^sub>s \<mu>)) |_ p')" unfolding
              subst_subst[of _ "\<mu> ^^ i" \<mu>] using subt_at_subst[OF pt'] by metis
          from poss_imp_subst_poss[OF pt',of "\<mu> ^^ i \<circ>\<^sub>s \<mu>"] pos_append_poss[OF _ this] 
          have "p' @ o'' @ r \<in> poss (C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> (\<mu> ^^ i \<circ>\<^sub>s \<mu>))" by auto
          from poss_imp_subst_poss[OF this] subst_power_Suc[of i \<mu>] have 
            "p' @ o'' @ r \<in> poss (C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ (Suc i) \<cdot> \<mu> ^^ n)" by auto
          then have "p' @ o'' @ r \<in> poss (C\<langle>t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ ?n)"
            by (metis add_Suc add_Suc_right subst_subst subst_power_compose_distrib)
          with ctxt_subst_hole_pos[of C ?n \<mu> "C\<langle>t \<cdot> \<mu>\<rangle>"] have "?o' \<in> poss (ctxt_subst C \<mu> (i+ Suc n) C\<langle>t \<cdot> \<mu>\<rangle>)" 
            by (metis ctxt_subst_subt_at pos_append_poss) 
          then show ?thesis unfolding ctxt_subst_Suc[symmetric] by simp
        qed
        let ?q = "?p^Suc ?n  @ q"
        from append_left_of_pos left_of_pos_append[OF lqq, of "o'' @ r"]
        have "left_of_pos ?o' (?p^?n @ ?p @ q)" by auto
        then have left:"left_of_pos ?o' ?q" using power_pos_Suc[of ?p "i + Suc n"] 
          by (metis append_assoc)
        let ?C' = "ctxt_of_pos_term ?o' ?t"
        from eq ot have t_ctxt:"?t = ?C'\<langle>l \<cdot> \<sigma>\<rangle>" using ctxt_supt_id by metis
        have "hole_pos ?C' = ?o'" by (metis hole_pos_ctxt_of_pos_term ot)
        with t_ctxt left have "\<exists>C' \<sigma>. ?t = C'\<langle>l \<cdot> \<sigma>\<rangle> \<and> left_of_pos (hole_pos C') ?q" by auto
        then have "\<not> fpstep_cond_single ?pt ?q ?t" unfolding fpstep_cond_single_def[of ?pt ?q ?t] split_conv l l' by simp
        then show ?thesis using fpstep_ctxt_subst_cond_def[of ?pt C \<mu>] by blast
      qed
    qed
  qed
qed


lemma possc_left_of_hole_pos: assumes l:"left_of_pos p' (hole_pos C @ q)" and pC:"p' \<in> (possc C)" 
  shows "left_of_pos p' (hole_pos C)"
proof-
  let ?p = "hole_pos C"
  from possc_not_below_hole_pos[OF pC] have nlt:"\<not> (?p <\<^sub>p p')" by auto
  from possc_not_below_hole_pos[OF pC] pos_cases have cs:"p' \<le>\<^sub>p hole_pos C \<or> p' \<bottom> hole_pos C" by blast
  have nle:"\<not> (p' \<le>\<^sub>p hole_pos C)" unfolding less_eq_pos_def proof(rule notI)
    assume "\<exists>r. p' @ r = hole_pos C"
    then obtain r where "hole_pos C = p' @ r" by metis
    from l[unfolded left_of_pos_def, unfolded this] obtain r' i j where
      a:"r' @ [i] \<le>\<^sub>p p'" and b:"r' @ [j] \<le>\<^sub>p p' @ r @ q" and ij:"i < j" by auto
    from a[unfolded less_eq_pos_def] obtain p0 where c:"p' = (r' @ [i]) @ p0" by fast
    from b[unfolded c] less_eq_pos_simps(2) have "[j] \<le>\<^sub>p ([i] @ p0 @ r) @ q" by auto
    with ij show False  unfolding less_eq_pos_def by fastforce
  qed
  with cs append_left_of_cases[OF l] have "p' \<bottom> (?p @ q)" by (metis l left_pos_parallel parallel_pos_sym)
  with pC[unfolded possc_def] hole_pos_poss[of C] have "p' \<bottom> ?p" by (metis nle cs)
  from parallel_remove_prefix[OF this] show "left_of_pos p' ?p" by (metis \<open>?p <\<^sub>p p' \<or> right_of_pos ?p p'\<close> nlt)
qed

lemma aux: assumes possc:"p \<in> possc C - {hole_pos C}" and x:"C\<langle>t :: ('a, 'b) term\<rangle> |_ p = Var x" 
  shows "\<not> (p \<le>\<^sub>p hole_pos C) \<and> C\<langle>u\<rangle> |_ p = Var x"
proof-
  let ?p = "hole_pos C"
  have nle:"\<not> (p \<le>\<^sub>p hole_pos C)" proof
    assume "p \<le>\<^sub>p hole_pos C"
    then have cs:"p <\<^sub>p ?p \<or> p = ?p" using order_pos.le_less by auto
    with possc have lt:"p <\<^sub>p ?p" by fast
    from possc have "p \<in> poss C\<langle>t\<rangle>" unfolding possc_def by auto
    with hole_pos_poss[of C t] lt x show False by (metis less_pos_def' var_pos_maximal)
  qed
  with pos_cases possc_not_below_hole_pos[OF DiffD1[OF possc]] have par:"p \<bottom> ?p" by blast
  from possc have pt:"p \<in> poss C\<langle>t\<rangle>" unfolding possc_def by auto
  from nle parallel_replace_at_subt_at[OF parallel_pos_sym[OF par] 
      hole_pos_poss pt, unfolded ctxt_of_pos_term_hole_pos[of C t]] x
  show ?thesis by simp  
qed

lemma fp_r_match_probs_complete:
  assumes nfp:"\<not> fpstep_cond_single (L, u, Forbidden_Patterns.R) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)"
    and qt: "q \<in> poss t"
    and lfun: "is_Fun L\<langle>u\<rangle>"
  shows "(\<exists> mp n \<sigma>. mp \<in> r_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution mp (n, \<sigma>))"
proof-
  let ?cs = "ctxt_subst C \<mu>"
  let ?ct = "?cs n t"
  let ?o = "hole_pos L"
  let ?p = "hole_pos C"
  from nfp obtain C' \<sigma> where ctxt_eq:"?ct = C'\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle>" and left:"left_of_pos (hole_pos C') (?p ^ n @ q)"
    unfolding fpstep_cond_single_def by auto  
  let ?o' = "hole_pos C'"
  from ctxt_eq have ctxt_eq':"L\<langle>u\<rangle> \<cdot> \<sigma> = ?ct |_ ?o'" using subt_at_hole_pos by auto
  from qt have a:"?p ^ n @ q \<in> poss ((C ^ n)\<langle>t\<rangle>)" by (induct n, auto)
  let ?case1 = "\<exists>p'. ?o' = ?p ^ n @ p' \<and> p' \<in> poss t"
  let ?case2 = "\<exists>x p' p''. ?o' = ?p ^ n @ p' @ p'' \<and> p' \<in> poss t \<and> t |_ p' = Var x \<and> 
   p'' \<in> poss (Var x \<cdot> \<mu> ^^ n) \<and> n > 0"
  let ?case3 = "\<exists>k p'. k < n \<and> ?o' = ?p ^ k @ p' \<and> p' \<in> possc C"
  let ?case4 = "\<exists>k x p' p''. k < n \<and> ?o' = hole_pos C ^ k @ p' @ p'' \<and>
   p' \<in> possc C - {hole_pos C} \<and> C\<langle>t\<rangle> |_ p' = Var x \<and> p'' \<in> poss (Var x \<cdot> \<mu> ^^ k)"
  from ctxt_eq have ooposs:"?o' \<in> poss ?ct" using hole_pos_poss by simp
  from ctxt_subst_pos_cases[OF this] have or:"?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4" by auto
  show ?thesis proof(cases "\<not>?case4", cases "\<not>?case3", cases "\<not>?case2")
    (* Case (i) *)
    assume "\<not>?case4" and "\<not>?case2" and "\<not>?case3"
    with or have ?case1 by blast
    then obtain q' where eq:"?o' = ?p^n @ q'" and qt':"q' \<in> poss t" by auto
    from left[unfolded eq] have "left_of_pos (q') q" using append_left_of_pos by auto
    with r_match_probs_def qt' have p:"(t |_ q',  L\<langle>u\<rangle>) \<in> r_match_probs L\<langle>u\<rangle> ?o q C t" by auto
    let ?mp = "(t |_ q', L\<langle>u\<rangle>)"
    from ctxt_eq'[unfolded eq] subt_at_append[OF ctxt_subst_hole_pos] ctxt_subst_subt_at 
    have "L\<langle>u\<rangle> \<cdot> \<sigma> = t \<cdot> \<mu>^^n |_q'" by fastforce
    from this[unfolded subt_at_subst[OF qt']] have s:"match_solution ?mp (n,\<sigma>)" 
      unfolding eq match_solution_def[of ?mp "(n,\<sigma>)", unfolded split_conv] by simp
    with p show ?thesis by fast
  next
    assume "\<not> \<not>?case2"
    then obtain x p' p'' where peq:"?o' = ?p ^n @ p' @ p''" and pt:"p' \<in> poss t" and 
      tpx:"t |_ p' = Var x" and px:"p'' \<in> poss (Var x \<cdot> \<mu> ^^ n)" and npos:"n > 0" by auto
    from subt_at_append[OF ctxt_subst_hole_pos] have ceq:"?ct |_ ?o' = t \<cdot> \<mu> ^^ n |_ (p' @ p'')" 
      using peq ctxt_subst_subt_at[of C \<mu> n t] by force
    from subt_at_append[OF poss_imp_subst_poss[OF pt], of "\<mu> ^^ n", unfolded subt_at_subst[OF pt, unfolded tpx]]
    have txy:"t \<cdot> \<mu> ^^ n |_ (p' @ p'') =  Var x \<cdot> \<mu>^^n |_ p''" by auto
    with ctxt_eq'[unfolded ceq] have "L\<langle>u\<rangle> \<cdot> \<sigma> =  Var x \<cdot> \<mu>^^n |_ p''" by auto
    then obtain D where "D\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle> =  Var x \<cdot> \<mu>^^n" using subt_at_imp_ctxt px by auto
    then have rs:"redex_solution (Var x, L\<langle>u\<rangle>) (n,\<sigma>, D)" unfolding redex_solution_def by auto
    from match_prob_of_rp_complete[of "Var x" "L\<langle>u\<rangle>", OF rs, unfolded match_prob_of_rp_def split term.simps]
    have "\<exists> \<tau> s v j. s \<in> {Var x} \<union> \<mu> ` W (Var x) \<and> s \<unrhd> v \<and> is_Fun v \<and> match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" 
      using lfun by (cases "L\<langle>u\<rangle>", auto)
    then obtain  \<tau> s v j where s_in:"s \<in> {Var x} \<union> \<mu> ` W (Var x)" and sv:"s \<unrhd> v" and fun_v:"is_Fun v" 
      and sol:"match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" by blast
    from sv fun_v have "s \<noteq> Var x" by (metis is_VarI supteq_Var_id)
    with s_in tpx have s_in:"s \<in> \<mu> ` W (t |_ p')" by auto
    from left[unfolded peq] have l:"left_of_pos (p' @ p'') q" using append_left_of_pos by simp
    have "\<not> (p' <\<^sub>p q)" unfolding less_pos_def less_eq_pos_def using var_pos_maximal[OF pt tpx] qt by blast
    with l left_of_append_cases have "left_of_pos p' q" by auto
    with s_in sv pt have p:"(v, L\<langle>u\<rangle>) \<in> r_match_probs L\<langle>u\<rangle> ?o q C t" unfolding r_match_probs_def by auto
    with sol show ?thesis by fast
  next
    assume "\<not> \<not>?case3"
    then obtain k p' where kn:"k < n" and eq:"?o' = ?p ^ k @ p'" and possc:"p' \<in> possc C"
      and pC:"p' \<in> poss C\<langle>t\<rangle>" unfolding possc_def by auto
    let ?mp = "(C\<langle>t\<rangle> |_ p', L\<langle>u\<rangle>)"
    from less_imp_Suc_add[OF kn] obtain n' where n:"n = k + Suc n'" by auto
    from left[unfolded eq n] have l:"left_of_pos p' (?p @ ?p ^ n' @ q)" 
      using append_left_of_pos[of _ _ "?p ^ k"] unfolding power_append_distr by simp
    from possc_left_of_hole_pos[OF this possc] have pp':"left_of_pos p' ?p" by auto
    then have p:"?mp \<in> r_match_probs L\<langle>u\<rangle> (hole_pos L) q C t" unfolding r_match_probs_def using pC by auto
    have "match_solution ?mp (k, \<sigma>)" unfolding match_solution_def split
    proof-
      have aux:"C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> |_ p' = C\<langle>t\<rangle> |_ p'"
        using parallel_replace_at_subt_at[OF left_pos_parallel[OF pp'] hole_pos_poss[of C t] pC]
        unfolding ctxt_of_pos_term_hole_pos by auto
      from pC have pC':"p' \<in> poss C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle>" 
        using hole_pos_poss parallel_poss_replace_at[OF left_pos_parallel[OF pp'] hole_pos_poss[of C t]]
        unfolding ctxt_of_pos_term_hole_pos by auto
      from ctxt_eq have "L\<langle>u\<rangle> \<cdot> \<sigma> = (ctxt_subst C \<mu> n t) |_ ?o'" by auto
      also have "\<dots> = (ctxt_subst C \<mu> (k + Suc n') t) |_ (?p ^ k @ p')" unfolding eq n by auto
      also have "\<dots> = (ctxt_subst C \<mu> (Suc n') t) \<cdot> \<mu> ^^ k |_ p'" unfolding ctxt_subst_add[of C \<mu> k] 
        using ctxt_subst_subt_at  subt_at_append[OF ctxt_subst_hole_pos[of C k]] by simp
      also have "\<dots> = C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k |_ p'" using Suc_eq_plus1_left by auto
      also have "\<dots> = C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ k" using subt_at_subst[OF pC'] by blast
      finally show "C\<langle>t\<rangle> |_ p' \<cdot> \<mu> ^^ k = L\<langle>u\<rangle> \<cdot> \<sigma>" unfolding aux by auto
    qed
    with p show ?thesis by auto
  next 
    assume "\<not> \<not> ?case4"
    then obtain k x p' p'' where kn:"k < n" and eq:"?o' = ?p ^ k @ p' @ p''" and possc:"p' \<in> possc C"
      and pne:"p' \<noteq> hole_pos C" and ctx:"C\<langle>t\<rangle> |_ p' = Var x" and pposs'':"p'' \<in> poss (Var x \<cdot> \<mu> ^^ k)" by auto
    from less_imp_Suc_add[OF kn] obtain n' where n:"n = k + Suc n'" by auto
    have left:"left_of_pos p' ?p"
    proof-
      from left[unfolded eq n] append_left_of_pos[of _ _ "?p ^ k"] have left:"left_of_pos (p' @ p'') (?p @ (?p ^ n' @ q))" 
        unfolding power_append_distr by simp
      from aux[OF _ ctx] possc pne have "\<not> p' \<le>\<^sub>p ?p" by fast
      with pos_cases possc_not_below_hole_pos[OF possc] have par:"p' \<bottom> ?p" by auto
      from parallel_imp_right_or_left_of[OF this] have leftor:"left_of_pos p' ?p \<or> left_of_pos ?p p'" by auto
      from n have n':"n = Suc (n' + k)" by (metis add_Suc_right add.commute)
      from left_of_pos_append[of ?p p' "?p ^ n' @ q" p''] left_of_imp_not_right_of[OF left] 
      have "\<not> left_of_pos ?p p'" by auto
      with parallel_imp_right_or_left_of[OF par] show ?thesis by auto
    qed
    from possc have possC:"p' \<in> poss C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle>" unfolding possc_def by auto
    from aux pne possc ctx have a:"C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> |_ p' = Var x" by force
    from ctxt_eq'[unfolded eq n ctxt_subst_add[of C \<mu> k "Suc n'"]] ctxt_subst_subt_at ctxt_subst_hole_pos have 
      " L\<langle>u\<rangle> \<cdot> \<sigma> = (ctxt_subst C \<mu> (Suc n') t) \<cdot> \<mu> ^^ k |_ (p' @ p'')" by fastforce
    also have "\<dots> = C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> \<cdot> \<mu> ^^ k |_ (p' @ p'')" by auto
    also from subt_at_append[OF poss_imp_subst_poss[OF possC]] subt_at_subst[OF possC] have 
      "\<dots> = C\<langle>ctxt_subst C \<mu> n' t \<cdot> \<mu>\<rangle> |_ p' \<cdot> \<mu> ^^ k |_ p''" by metis
    finally have " L\<langle>u\<rangle> \<cdot> \<sigma> = Var x \<cdot> \<mu> ^^ k |_ p''" unfolding a by auto 
    with subt_at_imp_ctxt[OF pposs''] obtain D where "D\<langle>L\<langle>u\<rangle> \<cdot> \<sigma>\<rangle> =  Var x \<cdot> \<mu>^^k" by force
    then have rs:"redex_solution (Var x, L\<langle>u\<rangle>) (k,\<sigma>, D)" unfolding redex_solution_def by auto
    from match_prob_of_rp_complete[of "Var x" "L\<langle>u\<rangle>", OF rs, unfolded match_prob_of_rp_def split term.simps]
    have "\<exists> \<tau> s v j. s \<in> {Var x} \<union> \<mu> ` W (Var x) \<and> s \<unrhd> v \<and> is_Fun v \<and> match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" 
      using lfun by (cases "L\<langle>u\<rangle>", auto)
    then obtain  \<tau> s v j where s_in:"s \<in> {Var x} \<union> \<mu> ` W (Var x)" and sv:"s \<unrhd> v" and fun_v:"is_Fun v" 
      and sol:"match_solution (v, L\<langle>u\<rangle>) (j, \<tau>)" by blast
    from sv fun_v have "s \<noteq> Var x" by (metis is_VarI supteq_Var_id)
    with s_in ctx have s_in:"s \<in> \<mu> ` W (C\<langle>t\<rangle> |_ p')" by auto
    with s_in sv left possc have p:"(v, L\<langle>u\<rangle>) \<in> r_match_probs L\<langle>u\<rangle> ?o q C t" unfolding r_match_probs_def by blast
    with sol show ?thesis by fast
  qed
qed


(* combine to some general statement *)

definition fp_match_probs :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) match_prob set" where
  "fp_match_probs l oo q C t \<equiv> 
    (h_match_probs l oo q C t) \<union> (a_match_probs l oo q C t) \<union>  (b_match_probs l oo q C t) \<union> (r_match_probs l oo q C t)" 


lemma fp_match_probs_complete:
  assumes nfp:"\<not> fpstep_ctxt_subst_cond (L, u, loc) C \<mu> q t"
    and qt: "q \<in> poss t"
    and ft:"is_Fun (t|_ q)" and fl:"is_Fun L\<langle>u\<rangle>"
  shows "(\<exists> mp n \<sigma>. mp \<in> fp_match_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> match_solution mp (n, \<sigma>)) \<or>
         (\<exists> ep n \<sigma> k. ep \<in> b_ematch_probs L\<langle>u\<rangle> (hole_pos L) q C t \<and> ematch_solution ep (n, k, \<sigma>))" (is "?A \<or> ?B")
proof -
  from nfp obtain n where c:"\<not> fpstep_cond_single (L, u, loc) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)" 
    unfolding fpstep_ctxt_subst_cond_def by auto
  then show ?thesis 
  proof (cases loc)
    case H
    with fp_h_match_probs_complete[OF c[unfolded H] qt] show ?thesis unfolding fp_match_probs_def by blast
  next
    case A
    with fp_a_match_probs_complete[OF c[unfolded A] qt ft fl] show ?thesis unfolding fp_match_probs_def by blast
  next
    case B
    with fp_b_match_probs_complete[OF c[unfolded B] qt fl] show ?thesis unfolding fp_match_probs_def by blast
  next
    case R
    with fp_r_match_probs_complete[OF c[unfolded R] qt fl] show ?thesis unfolding fp_match_probs_def by blast
  qed
qed
end

end

