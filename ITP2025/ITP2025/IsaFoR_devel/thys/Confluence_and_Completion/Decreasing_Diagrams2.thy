(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  Harald Zankl (2014, 2015, 2016)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014, 2015, 2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)

section "Decreasing Diagrams2"

theory Decreasing_Diagrams2
imports 
  "Decreasing-Diagrams-II.Decreasing_Diagrams_II" 
  First_Order_Rewriting.Critical_Pairs
  Knuth_Bendix_Order.Lexicographic_Extension
  Auxx.Util
begin

(*Section 1: decreasingness for families of relations *)
text \<open>ARSs whose relation is the union of an indexed set of relations.\<close>

definition ds :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
 where "ds r S = {y . \<exists>x \<in> S. (y,x) \<in> r}"
 
lemma ds_to_under[simp]: "ds r {a} = under r a" "ds r {a,b} = under r a \<union> under r b"
by (auto simp: ds_def under_def)

definition fars_ld :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'b rel) \<Rightarrow> 'a set \<Rightarrow> bool"
 where "fars_ld gt r I = (\<forall> a \<in> I. \<forall> b \<in> I. \<forall> x y z. (x,y) \<in> r a \<and> (x,z) \<in> r b \<longrightarrow> (\<exists> y1 y2 z1 z2 v. 
  ( (y,y1) \<in> (\<Union>c\<in>under gt a. r c)\<^sup>* \<and> ((y1,y2) \<in> (r b)\<^sup>=) \<and> (y2,v) \<in> (\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>* \<and>
    (z,z1) \<in> (\<Union>c\<in>under gt b. r c)\<^sup>* \<and> ((z1,z2) \<in> (r a)\<^sup>=) \<and> (z2,v) \<in> (\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>*)))"

definition fars_eld :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> ('a \<Rightarrow> 'b rel) \<Rightarrow> bool"
 where "fars_eld gt ge r = ((\<forall> x y z a b. (x,y) \<in> r a \<and> (x,z) \<in> r b \<longrightarrow> (\<exists> y1 y2 z1 z2 v. 
  ((y,y1) \<in> ((\<Union>c\<in>under gt a. r c)\<^sup>\<leftrightarrow>)\<^sup>* \<and> (y1,y2) \<in> (\<Union>c\<in>under ge b. r c)\<^sup>= \<and> (y2,v) \<in> ((\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>* \<and>
    (z,z1) \<in> ((\<Union>c\<in>under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>* \<and> (z1,z2) \<in> (\<Union>c\<in>under ge a. r c)\<^sup>= \<and> (z2,v) \<in> ((\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>*))))"

definition rel_props :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
 where "rel_props gt ge \<longleftrightarrow> trans gt \<and> trans ge \<and> wf gt \<and> refl ge \<and> ge O gt O ge \<subseteq> gt"

lemma fars_eld_imp_cr:
 assumes rp: "rel_props gt ge" and pk: "fars_eld gt ge r"
 shows "CR (\<Union>c \<in> UNIV. r c)"
proof (induct rule: edd_cr[of gt ge])
  case (peak a b s t u)
  then have *: "(t,u) \<in> ((\<Union>c\<in>under gt a. r c)\<^sup>\<leftrightarrow>)\<^sup>* O (\<Union>c\<in>under ge b. r c)\<^sup>= O
    ((\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>* O (((\<Union>c\<in>under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>* O (\<Union>c\<in>under ge a. r c)\<^sup>= O
    ((\<Union>c\<in>under gt a \<union> under gt b. r c)\<^sup>\<leftrightarrow>)\<^sup>*)\<inverse>" using pk[unfolded fars_eld_def, rule_format, of s t a u b] by blast
 show ?case  by (intro subsetD[OF _ *]) (unfold converse_inward, regexp)
qed (insert rp, auto simp: rel_props_def refl_on_def)

(*Section 2: Closing local peaks in TRSs *)
type_synonym ('f,'v) step = "('f,'v) term \<times> ('f,'v) rule \<times> pos \<times> ('f,'v) subst \<times> bool \<times> ('f,'v) term"
type_synonym ('f,'v) lpeak = "('f,'v) step \<times> ('f,'v) step"
type_synonym ('f,'v) join = "('f,'v) step list \<times> ('f,'v) step list"
(*a labeling is a function from rewrite steps to a set that respects an ordering*)
type_synonym ('f,'v,'a) labeling = "('f,'v) step \<Rightarrow> 'a"

definition get_source :: "('f,'v) step \<Rightarrow> ('f,'v) term"
  where "get_source s = fst s"

definition get_rule :: "('f,'v) step \<Rightarrow> ('f,'v) rule"
 where "get_rule s = fst (snd s)"

definition get_pos :: "('f,'v) step \<Rightarrow> pos"
 where "get_pos s = fst (snd (snd s))"

definition get_subst :: "('f,'v) step \<Rightarrow> ('f,'v) subst"
 where "get_subst s = fst (snd (snd (snd s)))"

definition get_target :: "('f,'v) step \<Rightarrow> ('f,'v) term" where 
  "get_target step = (case step of 
    (s, r, p, \<sigma>, s_to_t, t) \<Rightarrow> if s_to_t then t else s)"

lemma rstep_r_p_s_ctxt_closed2: 
  assumes "(s,t) \<in> rstep_r_p_s R rl p \<sigma>" 
  shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> rstep_r_p_s R rl (hole_pos C@p) \<sigma>"
using assms by (auto simp: Let_def rstep_r_p_s_def ctxt_of_pos_term_append) 

lemma rstep_r_p_s_ctxt_closed: 
  assumes "(s,t) \<in> rstep_r_p_s R rl p \<sigma>" and "q \<in> poss u"
  shows "((ctxt_of_pos_term q u)\<langle>s\<rangle>,(ctxt_of_pos_term q u)\<langle>t\<rangle>) \<in> rstep_r_p_s R rl (q@p) \<sigma>"
using rstep_r_p_s_ctxt_closed2[OF assms(1)] assms(2)
by (auto simp: rstep_r_p_s_def Let_def replace_at_below_poss replace_at_subt_at)
   (metis hole_pos_ctxt_of_pos_term[OF assms(2)])+
 
lemma rstep_r_p_s_subst_closed:
  assumes "(s, t) \<in> rstep_r_p_s R rl p \<tau>" 
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep_r_p_s R rl p (\<tau> \<circ>\<^sub>s \<sigma>)" 
using assms unfolding rstep_r_p_s_def' 
by (auto simp add: ctxt_of_pos_term_subst)

fun step_close:: "('f,'v) step \<Rightarrow> ('f,'v) ctxt \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) step"
  where "step_close (s, rl, p, \<sigma>, b, t) C \<tau> = (C\<langle>s \<cdot> \<tau>\<rangle>, rl, hole_pos C @ p, \<sigma> \<circ>\<^sub>s \<tau>, b, C\<langle>t \<cdot> \<tau>\<rangle>)"

(* rewrite sequences *)
type_synonym ('f,'v) seq = "('f,'v) term \<times> ('f,'v) step list"

inductive_set seq :: "('f,'v) trs \<Rightarrow> ('f,'v) seq set" 
for \<R> where 
  "(s,[]) \<in> seq \<R>"
| "(s,t) \<in> rstep_r_p_s \<R> r p \<sigma> \<Longrightarrow> (t,ts) \<in> seq \<R> \<Longrightarrow> (s, (s,r,p,\<sigma>,True,t) # ts) \<in> seq \<R>"

lemma rstep_is_seq: 
  assumes "(s,t) \<in> rstep_r_p_s R r p \<sigma>"
  shows "(s,[(s,r,p,\<sigma>,True,t)]) \<in> seq R" 
using assms seq.intros by blast

fun first :: "('f,'v) seq \<Rightarrow> ('f,'v) term"
  where "first (s,_) = s"

fun last :: "('f,'v) seq \<Rightarrow> ('f,'v) term"
where 
  "last (s, []) = s"
| "last (s, step # ss) = last (get_target step, ss)"

lemma seq_chop_first: 
  assumes "(s,(s,rl,p,\<sigma>,True,t) # ss) \<in> seq R"
  shows "(t,ss) \<in> seq R" and "(s,t) \<in> rstep_r_p_s R rl p \<sigma>" 
using assms seq.cases by auto  

fun seq_close :: "('f,'v) seq \<Rightarrow> ('f,'v) ctxt \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) seq"
 where "seq_close ss C \<tau> = (C\<langle>fst ss \<cdot> \<tau>\<rangle>, map (\<lambda>step. step_close step C \<tau>) (snd ss))"

definition seq_concat :: "('f,'v) seq \<Rightarrow> ('f,'v) seq \<Rightarrow> ('f,'v) seq"
 where "seq_concat \<sigma>1 \<sigma>2 = (first \<sigma>1, snd \<sigma>1 @ snd \<sigma>2)"

lemma seq_concat_seq_close: 
  shows "seq_close (seq_concat ts us) C \<tau> = seq_concat (seq_close ts C \<tau>) (seq_close us C \<tau>)"
proof -
  obtain t tq u uq where ts_dec: "ts = (t,tq)" and us_dec: "us = (u,uq)"
    by (cases ts, cases us, auto)
  then show ?thesis unfolding seq_concat_def by auto
qed

lemma seq_concat_labels:
  shows "map l (snd (seq_concat ts us)) = (map l (snd ts)) @ (map l (snd us))"
proof -
  obtain t tq u uq where ts_dec: "ts = (t,tq)" and us_dec: "us = (u,uq)"
    by (cases ts, cases us, auto)
  show ?thesis unfolding seq_concat_def by auto
qed

lemma seq_dec:
  assumes "ss \<in> seq R"
  and "map l (snd ss) = l1 @ l2"
  shows "\<exists> L1 L2. ss = seq_concat L1 L2 \<and> L1 \<in> seq R \<and> L2 \<in> seq R \<and> map l (snd L1) = l1 \<and> 
    (map l (snd L2) = l2) \<and> first ss = first L1 \<and> last L1 = first L2 \<and> last L2 = last ss"
using assms 
proof (induct l1 arbitrary: ss)
  case Nil
  then have L1: "(first ss, []) \<in> seq R" (is "?L1 \<in> _") by (auto intro: seq.intros)
  then have "ss = seq_concat ?L1 ss" by (cases ss) (auto simp: seq_concat_def)
  then show ?case using Nil L1 by (cases ss) (auto)
next
  case (Cons a ls)
  then obtain s step ts where ss_dec: "ss = (s,step#ts)" by (cases ss, auto)
  with Cons(2) have "(s,step#ts) \<in> seq R" by auto
  then obtain rl p \<sigma> t where step_dec: "step = (s,rl,p,\<sigma>,True,t)" by (cases, auto)
  then have step: "(s,t) \<in> rstep_r_p_s R rl p \<sigma>" using Cons(2)
    unfolding ss_dec step_dec using seq.cases by auto
  have i1:"(t,ts) \<in> seq R" using Cons(2) seq_chop_first(1) unfolding ss_dec step_dec by fast
  have i2:"map l (snd (t,ts)) = ls@l2" using Cons(3) Cons unfolding ss_dec step_dec by auto 
  from Cons(1)[OF i1 i2] obtain L1 L2 where 
    IH: "(t, ts) = seq_concat L1 L2" "L1 \<in> seq R" "L2 \<in> seq R"
    "map l (snd L1) = ls" "map l (snd L2) = l2" 
    "first (t, ts) = first L1" "last L1 = first L2" "last L2 = last (t, ts)" by fast
  have t: "first L1 = t" using IH(1) unfolding seq_concat_def by auto
  have f1: "ss = seq_concat (s,step # snd L1) L2" using IH(1)
    unfolding ss_dec step_dec seq_concat_def by auto
  have f2: "(s,step # snd L1) \<in> seq R"
    unfolding step_dec using seq.intros(2)[OF step] IH(2) t 
    by (metis first.cases first.simps snd_conv step_dec)
  have f4: "map l (snd (s,step# snd L1)) = a # ls"
    using IH(4) Cons(3) unfolding ss_dec step_dec by auto
  have e1: "first ss = first ((s, step # snd L1))" unfolding ss_dec by auto
  have e2: "last (s,step#snd L1) = first L2"
    using IH step_dec apply (auto simp add: get_target_def)
    by (metis first.simps surjective_pairing)
  have e3: "last L2 = last ss"
    unfolding ss_dec step_dec last.simps get_target_def using IH by auto
  show ?case using f1 f2 IH(3) f4 IH(5) using e1 e2 e3 by metis
qed

lemma seq_close_length: "length (snd ss) = length (snd (seq_close ss C \<tau>))" by auto

lemma step_super_closed1: "get_target (step_close step C \<sigma>) = C\<langle>get_target step \<cdot> \<sigma>\<rangle>"
  unfolding get_target_def Let_def by (cases step, simp)

lemma seq_super_closed1:
  assumes seq:"ss \<in> seq R"
  shows "seq_close ss C \<sigma> \<in> seq R \<and> (first (seq_close ss C \<sigma>)) = C\<langle>first ss \<cdot> \<sigma>\<rangle> \<and> 
    last (seq_close ss C \<sigma>) = C\<langle>last ss \<cdot> \<sigma>\<rangle>" 
using seq
proof (induct "snd ss" arbitrary: ss)
  case Nil then obtain s where ss_dec: "ss = (s,[])" by (cases ss, auto)
  then show ?case using seq.intros unfolding ss_dec by auto
next
  case (Cons step ts)
  from Cons(2) obtain s where ss_dec: "ss=(s,step#ts)" by (cases ss, auto)
  with Cons(3) obtain rl p \<tau> t where step_dec: "step=(s,rl,p,\<tau>,True,t)" by (auto elim: seq.cases)
  then have step: "(s,t) \<in> rstep_r_p_s R rl p \<tau>" and  i:"(t,ts) \<in> seq R" (is "?ts \<in> _") 
    using Cons(3) seq.cases unfolding ss_dec step_dec by auto
  from Cons(1)[OF _ i] have ih: 
    "seq_close ?ts C \<sigma> \<in> seq R" "(first (seq_close ?ts C \<sigma>)) = (C\<langle>first ?ts\<cdot>\<sigma>\<rangle>)"
    "last (seq_close ?ts C \<sigma>) = C\<langle>last ?ts\<cdot>\<sigma>\<rangle>" 
    by auto
  have C_step: "(C\<langle>s\<cdot>\<sigma>\<rangle>,C\<langle>t\<cdot>\<sigma>\<rangle>) \<in> rstep_r_p_s R rl (hole_pos C@p) (\<tau>\<circ>\<^sub>s \<sigma>)" 
    using rstep_r_p_s_ctxt_closed2[OF rstep_r_p_s_subst_closed[OF step]] by auto
  then have C_seq: "(seq_close ss C \<sigma>) \<in> seq R" 
    using ih(1) seq.intros(2)[OF C_step] unfolding ss_dec step_dec by auto
  then have C_first: "first (seq_close ss C \<sigma>) = C\<langle>first ss\<cdot>\<sigma>\<rangle>" unfolding ss_dec step_dec by auto
  have "last (seq_close ?ts C \<sigma>) = C\<langle>last ?ts\<cdot>\<sigma>\<rangle>" using ih by auto
  then have C_last: "last (seq_close ss C \<sigma>) = C\<langle>last ss\<cdot>\<sigma>\<rangle>"
    unfolding ss_dec seq_close.simps last.simps fst_conv snd_conv  
      list.map get_target_def step_dec by auto
  show ?case using C_seq C_first C_last by auto
qed

(*peaks*)
definition local_peaks :: "('f,'v) trs \<Rightarrow> (('f,'v) lpeak) set"
  where "local_peaks \<R> = {((s,r\<^sub>1,p\<^sub>1,\<sigma>\<^sub>1,True,t),(s,r\<^sub>2,p\<^sub>2,\<sigma>\<^sub>2,True,u)) | s t u r\<^sub>1 r\<^sub>2 p\<^sub>1 p\<^sub>2 \<sigma>\<^sub>1 \<sigma>\<^sub>2. 
  (s,t) \<in> rstep_r_p_s \<R> r\<^sub>1 p\<^sub>1 \<sigma>\<^sub>1 \<and> (s,u) \<in> rstep_r_p_s \<R> r\<^sub>2 p\<^sub>2 \<sigma>\<^sub>2}"

context
  fixes ren :: "'v :: infinite renaming2" 
begin
definition critical_peaks :: "('f,'v) trs \<Rightarrow> (bool \<times> ('f,'v) lpeak) set"
  where "critical_peaks \<R> = {(C = \<box>, (l \<cdot> \<sigma>, (l, r), [], \<sigma>, True, r \<cdot> \<sigma>), (l \<cdot> \<sigma>, (l', r'), hole_pos C, \<tau>, True, (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>)) | l r l' r' l'' C \<sigma> \<tau>.  
    (l, r) \<in> \<R> \<and> (l', r') \<in> \<R> \<and> l = C\<langle>l''\<rangle> \<and> is_Fun l'' \<and>
    mgu_vd ren l'' l' = Some (\<sigma>, \<tau>) }"

lemma critical_peak_is_local_peak:
  assumes "(b,s1,s2) \<in> critical_peaks R"
  shows "(s1,s2) \<in> local_peaks R"
using assms
unfolding critical_peaks_def local_peaks_def rstep_r_p_s_def
by auto (metis ctxt_of_pos_term_hole_pos hole_pos_subst mgu_vd_sound)+

lemma critical_peaksI:
  assumes "(l, r) \<in> R" and "(l', r') \<in> R" and "l = C\<langle>l''\<rangle>"
  and "is_Fun l''" and "mgu_vd ren l'' l' = Some (\<sigma>, \<tau>)" and "s = r \<cdot> \<sigma>"
  and "t =  (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>" and "b = (C = \<box>)"
  shows "(b, (l \<cdot> \<sigma>, (l, r), [], \<sigma>, True, s), (l \<cdot> \<sigma>, (l', r'), hole_pos C, \<tau>, True, t)) \<in> critical_peaks R"
using assms unfolding critical_peaks_def by blast

lemma critical_peak_to_critical_pair:
  assumes "(b,s1,s2) \<in> critical_peaks R"
  shows "(b, get_target s2,get_target s1) \<in> critical_pairs ren R R"
using assms 
unfolding critical_peaks_def critical_pairs_def get_target_def 
by fastforce

definition parallel_peak :: "('f,'v) trs \<Rightarrow> (('f,'v) lpeak) \<Rightarrow> bool"
 where "parallel_peak \<R> p = (
  p \<in> local_peaks \<R> \<and>
  (let ((s,r\<^sub>1,p\<^sub>1,\<sigma>\<^sub>1,b,t),(s,r\<^sub>2,p\<^sub>2,\<sigma>\<^sub>2,d,u)) = p in parallel_pos p\<^sub>1 p\<^sub>2)
 )"

definition variable_peak :: "('f,'v) trs \<Rightarrow> (('f,'v) lpeak) \<Rightarrow> bool"
 where "variable_peak \<R> p = (
  p \<in> local_peaks \<R> \<and>
  (let ((s,rl\<^sub>1,p\<^sub>1,\<sigma>\<^sub>1,b,t),(s,rl\<^sub>2,p\<^sub>2,\<sigma>\<^sub>2,d,u)) = p in
  \<exists> r. ((p\<^sub>1 @ r = p\<^sub>2) \<and> \<not> (r \<in> poss (fst rl\<^sub>1) \<and> is_Fun ((fst rl\<^sub>1) |_ r)))
 ))"

definition function_peak :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> bool"
 where "function_peak \<R> p = (
  p \<in> local_peaks \<R> \<and>
  (let ((s,rl\<^sub>1,p\<^sub>1,\<sigma>\<^sub>1,b,t),(s,rl\<^sub>2,p\<^sub>2,\<sigma>\<^sub>2,d,u)) = p in
  \<exists> r. ((p\<^sub>1 @ r = p\<^sub>2) \<and> r \<in> poss (fst rl\<^sub>1) \<and> is_Fun ((fst rl\<^sub>1) |_ r)))
 )"

lemma function_peak_inst_of_critical_peak:
  assumes "function_peak R p"
  shows "\<exists> C \<delta> b cp. (b,cp) \<in> critical_peaks R \<and> p = (step_close (fst cp) C \<delta>, step_close (snd cp) C \<delta>)"
proof -
  from assms obtain s l1 r1 p1 \<sigma>1 t l2 r2 p2 \<sigma>2 u v where
    p: "p = ((s, (l1, r1), p1, \<sigma>1, True, t), (s, (l2, r2), p2, \<sigma>2, True, u))" and
    st:"(s,t) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1" and
    su:"(s,u) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2" and
    v:"p1 @ v = p2" and vl1:"v \<in> poss l1" and l1v:"is_Fun (l1 |_ v)"
    unfolding function_peak_def local_peaks_def by auto
  from st su have
    p1: "p1 \<in> poss s" and \<sigma>1: "s |_ p1 = l1 \<cdot> \<sigma>1" and
    t: "t = replace_at s p1 (r1 \<cdot> \<sigma>1)" and lr1: "(l1,r1) \<in> R" and
    p2: "p2 \<in> poss s" and \<sigma>2: "s |_ p2 = l2 \<cdot> \<sigma>2" and
    u: "u = replace_at s p2 (r2 \<cdot> \<sigma>2)" and lr2: "(l2,r2) \<in> R"
    unfolding rstep_r_p_s_def' by auto
  from v have l2v: "(l1 \<cdot> \<sigma>1) |_ v = l2 \<cdot> \<sigma>2" using \<sigma>1 \<sigma>2 p1 by auto
  from l2v subt_at_subst[OF vl1] have "l1 |_ v \<cdot> \<sigma>1 = l2 \<cdot> \<sigma>2" by metis
  from mgu_vd_complete[OF this]
  obtain \<mu>1 \<mu>2 \<delta> where mgu: "mgu_vd ren (l1 |_ v) l2 = Some (\<mu>1, \<mu>2)"
    and d1:"\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<delta>" and d2:"\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<delta>" and mu12:"l1 |_v \<cdot> \<mu>1 = l2 \<cdot> \<mu>2"
    by fast
  let ?s' = "l1 \<cdot> \<mu>1"
  let ?t' = "r1 \<cdot> \<mu>1"
  let ?C' = "ctxt_of_pos_term v l1"
  let ?u' = "(?C' \<cdot>\<^sub>c \<mu>1)\<langle>r2 \<cdot> \<mu>2\<rangle>"
  let ?C = "ctxt_of_pos_term p1 s"
  from p1 \<sigma>1 d1 have s_inst:"?C\<langle>?s' \<cdot> \<delta>\<rangle> = s" using replace_at_ident by simp
  from d1 t have t_inst:"t = ?C\<langle>?t' \<cdot> \<delta>\<rangle>" using replace_at_ident by simp
  from u v[symmetric] d2 ctxt_of_pos_term_append[OF p1] \<sigma>1 d1
  have u_inst: "?C\<langle>?u' \<cdot> \<delta>\<rangle> = u" apply simp
    unfolding ctxt_of_pos_term_subst[OF vl1] subst_subst
    by simp
  have "v = hole_pos ?C'" by (metis hole_pos_ctxt_of_pos_term vl1)
  with critical_peaksI[OF lr1 lr2 _ l1v mgu, of ?C' ?t' ?u' "?C' = \<box>"] ctxt_supt_id[OF vl1]
  have "(?C' = \<box>, (?s', (l1, r1), [], \<mu>1, True, ?t') ,(?s', (l2, r2), v, \<mu>2, True, ?u')) \<in> critical_peaks R"
    (is "(?b, ?cp) \<in> _") by auto
  moreover have "p = (step_close (fst ?cp) ?C \<delta>, step_close (snd ?cp) ?C \<delta>)"
    unfolding p using s_inst p1 d1 d2 v u_inst t_inst by simp
  ultimately show ?thesis by fast
qed

lemma mirror: 
  assumes "p \<in> local_peaks R" 
  shows "(snd p,fst p) \<in> local_peaks R" 
using assms unfolding local_peaks_def by auto

lemma local_peaks_helper:
  assumes pos: "p1 \<le>\<^sub>p p2" 
  and p: "((s,r1,p1,\<sigma>1,t),(s,r2,p2,\<sigma>2,u)) \<in> local_peaks R" (is "?p \<in> _")
  shows "variable_peak R ?p \<or> function_peak R ?p" 
proof -
  from pos obtain r where "(p1 @ r) = p2" using prefix_pos_diff by fast
  then show ?thesis using p unfolding variable_peak_def function_peak_def by auto
qed

lemma local_peaks_cases:
  assumes p: "p \<in> local_peaks \<R>"
  shows "parallel_peak \<R> p \<or> variable_peak \<R> p \<or> variable_peak \<R> (snd p, fst p) \<or> function_peak \<R> p \<or> function_peak \<R> (snd p, fst p)" 
proof -
  from assms obtain  s t u r1 r2 p1 p2 \<sigma>1 \<sigma>2 where 
    "(s,t) \<in> rstep_r_p_s \<R> r1 p1 \<sigma>1 \<and> (s,u) \<in> rstep_r_p_s \<R> r2 p2 \<sigma>2" and
    p_dec: "p = ((s,r1,p1,\<sigma>1,True,t),(s,r2,p2,\<sigma>2,True,u))" 
    unfolding local_peaks_def by fast
  then show ?thesis
  proof (cases "parallel_pos p1 p2")
    case True 
    then have "parallel_peak \<R> p" 
      using p unfolding parallel_peak_def p_dec Let_def by auto
    then show ?thesis by auto
  next
    case False note F = this
    then show ?thesis 
    proof (cases "p1 \<le>\<^sub>p p2") 
      case True then show ?thesis using local_peaks_helper p p_dec by fast 
    next
      case False 
      then have "p2 \<le>\<^sub>p p1" using F parallel_pos by auto 
      then show ?thesis using local_peaks_helper mirror p p_dec by (metis fst_conv snd_conv)
    qed
  qed  
qed
end

lemma variable_peak_decompose: 
  assumes "variable_peak R p" 
  shows "\<exists> s t u l1 r1 p1 \<sigma>1 l2 r2 p2 \<sigma>2 q q1 q2 w. (
   p = ((s,(l1,r1),p1,\<sigma>1,True,t),(s,(l2,r2),p2,\<sigma>2,True,u)) \<and>
   (s,t) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1 \<and>
   (s,u) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2 \<and>
   p1 @ q = p2 \<and>
   (q1@ q2) = q \<and>
   q1 \<in> poss l1 \<and>
   l1 |_ q1 = Var w)" 
proof -
  from assms obtain s rl1 p1 s1 t rl2 p2 s2 u q where 
    p: "p \<in> local_peaks R" and 
    p_dec: "p = ((s,rl1,p1,s1,True,t),(s,rl2,p2,s2,True,u))" and
    q:"p1 @ q = p2" and 
    px: "\<not> (q \<in> poss (fst rl1) \<and> is_Fun ((fst rl1) |_ q))" 
    unfolding variable_peak_def local_peaks_def Let_def  by blast 
  then obtain l1 r1 l2 r2 where rl1: "(l1,r1) = rl1" and rl2: "(l2,r2) = rl2" 
    using surjective_pairing by metis
  then have s1: "(s,t) \<in> rstep_r_p_s R (l1,r1) p1 s1" and s2:"(s,u) \<in> rstep_r_p_s R (l2,r2) p2 s2" 
    using p p_dec unfolding local_peaks_def by auto
  have \<sigma>1: "s |_ p1 = l1 \<cdot> s1" using s1 unfolding rl1[symmetric] rstep_r_p_s_def' by auto
  have p2: "p2 \<in> poss s" using s2 unfolding rl2[symmetric] rstep_r_p_s_def' by auto
  from px have py: "\<not>(q \<in> poss l1 \<and> is_Fun (l1 |_ q))" using rl1 by auto 
  from py obtain q1 q2 w where k: "q = q1@q2" and q1:"q1 \<in> poss l1" and w:"l1 |_ q1 =  Var w" 
    using \<sigma>1 p2 pos_into_subst[of l1 s1 "s |_ p1" q] poss_append_poss q[symmetric] by auto 
  then show ?thesis using s1 s2 q p_dec rl1 rl2 by fast
qed

(* close variable peaks *)
lemma variable_steps_lin:
  assumes xy:"(x, y) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1"
  and xz:"(x, z) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2"
  and "p1 @ v = p2"
  and "(v1 @ v2) = v" and "v1 \<in> poss l1" and "l1 |_ v1 = Var w"
  and linl1: "linear_term l1"
  defines "\<tau> \<equiv> (\<lambda>y. if y = w then replace_at (\<sigma>1 y) v2 (r2 \<cdot> \<sigma>2) else \<sigma>1 y)"
  defines "t \<equiv> (ctxt_of_pos_term p1 x)\<langle>r1 \<cdot> \<tau>\<rangle>"
  shows "(z, t) \<in> (rstep_r_p_s R (l1, r1) p1 \<tau>)" (is "?g1")
    "linear_term r1 \<longrightarrow> (
     (y = t)  \<or> 
      (\<exists>q. (q \<in> poss r1 \<and>  (r1 |_ q = Var w) \<and> (y,t) \<in> (rstep_r_p_s R (l2,r2) (p1@q@v2) \<sigma>2))))" (is "?g2")
proof -
  from xy[unfolded rstep_r_p_s_def'] 
  have p1: "p1 \<in> poss x" and lr1: "(l1,r1) \<in> R" and \<sigma>1: "x |_ p1 = l1 \<cdot> \<sigma>1"
    and y: "y = replace_at x p1 (r1 \<cdot> \<sigma>1)" by auto
  from xz[unfolded rstep_r_p_s_def'] 
  have p2: "p2 \<in> poss x" and lr2: "(l2,r2) \<in> R" and \<sigma>2: "x |_ p2 = l2 \<cdot> \<sigma>2"
    and z: "z = replace_at x p2 (r2 \<cdot> \<sigma>2)" by auto
  from assms(3) have v:"p2 = p1 @ v" using less_eq_pos_def by auto
  then have l2v:"(l1 \<cdot> \<sigma>1) |_ v = l2 \<cdot> \<sigma>2" using \<sigma>1 \<sigma>2 p1 p2 by auto
  from v z \<sigma>1 have zp1:"z = replace_at x p1 (replace_at (l1 \<cdot> \<sigma>1) v (r2 \<cdot> \<sigma>2))" 
    using ctxt_of_pos_term_append[OF p1] ctxt_ctxt by force
  from assms have  v12: "v = v1 @ v2" by auto
  from assms have  w: "l1 |_ v1 = Var w" by auto
  from assms p2 have ths: "v \<in> poss (x |_ p1)" by auto
  have v1: "v1 \<in> poss l1" using assms by auto
  from assms have  wv2: "\<sigma>1 w |_ v2 = l2 \<cdot> \<sigma>2" using l2v by auto
  have v1l1\<sigma>1:"v1 \<in> poss (l1 \<cdot> \<sigma>1)" using v1 by simp
  let ?cr = "replace_at x p1 (r1 \<cdot> \<tau>)"
  from linear_term_replace_in_subst[OF linl1 v1 w, of \<sigma>1 \<tau>, simplified]
  have "l1 \<cdot> \<tau> = replace_at (l1 \<cdot> \<sigma>1) v1 (\<tau> w)" using \<tau>_def by auto
  also have "... = replace_at (l1 \<cdot> \<sigma>1) v1 (replace_at (\<sigma>1 w) v2 (r2 \<cdot> \<sigma>2))" using \<tau>_def by auto
  also have "... = replace_at (l1 \<cdot> \<sigma>1) v (r2 \<cdot> \<sigma>2)" 
    using v12 v1 w
      ctxt_of_pos_term_append[OF v1l1\<sigma>1] 
      ctxt_ctxt by auto
  finally have "l1 \<cdot> \<tau> = replace_at (l1 \<cdot> \<sigma>1) v (r2 \<cdot> \<sigma>2)" .
  with zp1 have zp2: "z = replace_at x p1 (l1 \<cdot> \<tau>)" by auto
  then have zcr:"(z, ?cr) \<in> rstep R" using subset_rstep lr1 by auto
  have p1z: "p1 \<in> poss z" using zp1 by (metis less_eq_pos_simps(1) p2 replace_at_below_poss v z)
  have k: "ctxt_of_pos_term p1 x = ctxt_of_pos_term p1 z" 
    using ctxt_of_pos_term_replace_at_below[OF p1] zp2 by auto
  have zcr: "(z,?cr) \<in> rstep_r_p_s R (l1,r1) p1 \<tau>" 
    unfolding rstep_r_p_s_def Let_def
    using p1z lr1 zp2 k by force
  then show "?g1" unfolding t_def by auto
  (*second goal*)
  have g2a: "(w \<notin> vars_term r1) \<longrightarrow> (y = ?cr)" 
  proof
    assume A: "w \<notin> vars_term r1" 
    show "y = ?cr" 
    proof -
      from A have "r1 \<cdot> \<tau> = r1 \<cdot> \<sigma>1" unfolding \<tau>_def by (induct r1, auto)
      then have "?cr = y" using y by auto
      then show ?thesis by auto
    qed
  qed       
 (*third goal*)
  have g2b: "w \<in> vars_term r1 \<longrightarrow> (linear_term r1 \<longrightarrow> (\<exists>q. (q \<in> poss r1 \<and>  (r1 |_ q = Var w) \<and> 
    (y, ?cr) \<in> (rstep_r_p_s R (l2,r2) (p1@q@v2) \<sigma>2))))" (is "_ \<longrightarrow> (?l \<longrightarrow> ?s)")
  proof
    assume W: "w \<in> vars_term r1" 
    show "?l \<longrightarrow> ?s"
    proof 
      assume linr1: "linear_term r1"
      show "?s" proof -
      from W obtain q where q: "q \<in> poss r1" and qw: "r1 |_ q = Var w" 
        using supteq_imp_subt_at[OF supteq_Var[OF W]] by auto
      have qr1\<sigma>1:"q \<in> poss (r1 \<cdot> \<sigma>1)" using q by simp
      from linear_term_replace_in_subst[OF linr1 q qw, of \<sigma>1 \<tau>, simplified]
      have "r1 \<cdot> \<tau> = replace_at (r1 \<cdot> \<sigma>1) q (\<tau> w)" using \<tau>_def by auto
      also have "... = replace_at (r1 \<cdot> \<sigma>1) q (replace_at (\<sigma>1 w) v2 (r2 \<cdot> \<sigma>2))" using \<tau>_def by auto
      also have "... = replace_at (r1 \<cdot> \<sigma>1) (q @ v2) (r2 \<cdot> \<sigma>2)" 
        using q qw ctxt_of_pos_term_append[OF qr1\<sigma>1] ctxt_ctxt by auto
      finally have s3:"r1 \<cdot> \<tau> = replace_at (r1 \<cdot> \<sigma>1) (q @ v2) (r2 \<cdot> \<sigma>2)" .
      from wv2 qw have "(r1 \<cdot> \<sigma>1) |_ (q @ v2) = l2 \<cdot> \<sigma>2" 
        using q subt_at_append[OF qr1\<sigma>1, of v2] by auto
      then have ths: "r1 \<cdot> \<sigma>1 = (ctxt_of_pos_term (q @ v2) (r1 \<cdot> \<sigma>1))\<langle>l2 \<cdot> \<sigma>2\<rangle>"
        using qr1\<sigma>1 ctxt_supt_id \<sigma>1 p2 poss_append_poss q qw subt_at_subst v v1 v12 w using y by metis
      have k: "(q@v2) \<in> poss (r1 \<cdot> \<sigma>1)" using q 
        by (metis v12 w v1 \<sigma>1 p2 poss_append_poss qr1\<sigma>1 qw eval_term.simps(1) subt_at_subst v)
      from ths k lr2 have key: "(r1 \<cdot> \<sigma>1, r1 \<cdot> \<tau>) \<in> rstep_r_p_s R (l2,r2) (q@v2) \<sigma>2" 
        unfolding s3 rstep_r_p_s_def Let_def by auto 
      then have r: "((ctxt_of_pos_term p1 x)\<langle>r1\<cdot>\<sigma>1\<rangle>,(ctxt_of_pos_term p1 x)\<langle>r1 \<cdot> \<tau>\<rangle>) \<in> rstep_r_p_s R (l2,r2) (p1@q@v2) \<sigma>2"
        using rstep_r_p_s_ctxt_closed p1 by auto
      show ?thesis using q qw r unfolding y by auto
    qed
   qed
  qed
  show "?g2" using g2a g2b unfolding t_def by auto
qed

(* towards left-linear variable peaks *)

(* auxiliary functions and lemmas for parallel rewriting *)

fun mapi :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "mapi f i [] = []"
| "mapi f i (x # xs) = f i x # mapi f (i + 1) xs"

lemma append_mapi:
  "mapi f n (xs @ ys) = mapi f n xs @ mapi f (n + length xs) ys"
by (induct xs arbitrary: n) simp_all

lemma length_mapi:
  "length (mapi f n xs) = length xs"
by (induct xs arbitrary: n) simp_all

lemma length_concat_mapi:
  "length (concat (mapi (\<lambda>i. map (f i)) n xs)) = length (concat xs)"
by (induct xs arbitrary: n) simp_all

lemma concat_replicate_empty:
  "concat (mapi (\<lambda>i. map (f i)) n (replicate m [])) = []"
by (induct m arbitrary: n) simp_all

lemma mapi_nth:
  assumes "i < length xs"
  shows "(mapi f j xs) ! i = f (j + i) (xs ! i)"
using assms
by (induct i arbitrary: xs j) (case_tac[!] xs, auto)

lemma mapi_drop:
  shows "drop i (mapi f j xs) = mapi f (j + i) (drop i xs)"
by (induct xs arbitrary: j i) (auto, case_tac i, auto)

lemma mapi_map_replicate_trivial:
  shows "mapi (\<lambda>i. map (f i)) j (replicate i []) = replicate i []"
by (induct i arbitrary: j) auto

lemma fst_concat_mapi1:
  "map fst (concat xs) = map fst (concat (mapi (\<lambda>i. map (\<lambda>(rl,p,\<sigma>). (rl,i#p,\<sigma>))) n xs))"
by (induct xs arbitrary: n) auto

lemma fst_concat_mapi2:
  assumes "\<forall>i < length (concat steps). fst ((concat steps) ! i) = (l,r)"
  shows "\<forall>i < length (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps)). 
           fst (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps) ! i) = (l, r)"
proof (intro allI impI)
  fix i
  assume A: "i < length (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps))"
  have l: "i < length (concat steps)" using A length_concat_mapi by metis
  have "map fst (concat steps) ! i = (l, r)" using nth_map l assms by auto
  then have "map fst (concat (mapi (\<lambda>i. map (\<lambda>(rl,p,\<sigma>). (rl, i # p,\<sigma>))) n steps)) ! i = (l, r)"
    using fst_concat_mapi1 l by metis
  then show "fst (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps) ! i) = (l, r)"
    using nth_map A by auto
qed

lemma fst_concat_mapi3:
  assumes "\<forall>j < length steps. \<forall>i < length (steps ! j). fst (steps ! j ! i) = (l, r)"
  shows "\<forall>i < length (concat steps). fst ((concat steps) ! i) = (l, r)"
using assms
proof (induct steps)
  case (Cons s ss)
  show ?case
  proof (intro allI impI)
    fix i 
    assume A: "i < length (concat (s # ss))"
    show "fst (concat (s # ss) ! i) = (l, r)"
    proof (cases "i < length s") 
      case True
      have "\<forall>i < length s. fst (s ! i) = (l, r)" using Cons by auto
      then have elt: "fst (s ! i) = (l, r)" using True by auto
      from True have "s ! i = concat (s # ss) ! i" using nth_append[of s] by simp
      then show ?thesis using elt by auto
    next
      case False 
      have k: "\<forall>j < length ss. \<forall>i < length (ss ! j). fst (ss ! j ! i) = (l, r)" using Cons(2) by auto
      have k2: "\<forall>i < length s. fst (s ! i) = (l, r)" using Cons(2) by auto 
      then have k': "\<forall>i < length (concat ss). fst (concat ss ! i) = (l, r)" using Cons(1)[OF k] by auto
      have "i < length s + length (concat ss)" using k' False A by auto
      then have "fst (concat ss ! (i - length s)) = (l, r)" using False k' by auto
      then show ?thesis using k2 False using nth_append[of s] by simp
    qed
  qed
qed auto

lemma fst_concat_mapi: 
  assumes "\<forall>j<length steps. \<forall>i<length (steps ! j). fst (steps ! j ! i) = (l, r)"
  shows "\<forall>i<length (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps)). 
           fst (concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) n steps) ! i) = (l, r)"
by (rule fst_concat_mapi2[OF fst_concat_mapi3[OF assms]])

lemma concat_singleton:
  assumes "concat xs = [z]"
  shows "(\<exists>i < length xs. xs ! i = [z] \<and> (\<forall>j < length xs. j \<noteq> i \<longrightarrow> (xs ! j) = []))"
using assms
proof (induct xs)
  case (Cons x xs)
  show ?case
  proof (cases x)
    case Nil
    with Cons have "concat xs = [z]" by auto
    with Cons obtain i where 
      len:"i<length xs" and 
      z:"xs ! i = [z]" and 
      nil:"\<forall>j<length xs. j \<noteq> i \<longrightarrow> (xs ! j) = []" 
      by auto
    let ?i = "Suc i"
    from len have "?i<length (x # xs)"
      by auto
    moreover from z have "(x # xs) ! ?i = [z]" by auto
    moreover have "\<forall>j<length (x # xs). j \<noteq> ?i \<longrightarrow> (x # xs) ! j = []" using Nil nil
      by (metis gr0_conv_Suc length_Cons linorder_neqE_nat not_less_eq nth_Cons' nth_Cons_Suc)
    ultimately show ?thesis by auto  
  qed (insert Cons, auto)
qed auto

lemma concat_Cons:
  assumes "concat xss = x # xs"
  shows "\<exists>i < length xss. \<exists>ys. (\<forall>j < i. xss ! j = []) \<and> 
    xss ! i = x # ys \<and> xs = ys @ concat (drop (Suc i) xss)"
using assms
proof (induct xss arbitrary: x xs)
  case (Cons z zs)
  show ?case
  proof (cases "z = []")
    case False
    with Cons have x:"x = hd z" by (metis concat.simps(2) hd_append2 list.sel(1))
    have "0 < length (z # zs)" by auto
    moreover have "\<forall>j < 0. (z # zs) ! j = []" by auto
    moreover have "(z # zs) ! 0 = x # tl z" using x nth_Cons_0 False by simp
    moreover have "xs = tl z @ concat (drop (Suc 0) (z # zs))" using Cons False    
      by (metis concat.simps(2) drop_0 drop_Suc_Cons list.sel(3) tl_append2)
    ultimately show ?thesis by auto
  next
    case True
    with Cons have "concat zs = x # xs" by auto
    from Cons(1)[OF this] obtain i ys where IH:
      "i < length zs"
      "\<forall>j<i. zs ! j = []"
      "zs ! i = x # ys"
      "xs = ys @ concat (drop (Suc i) zs)"
      by auto
    then have "(Suc i) < length (z # zs)" by auto
    moreover have "\<forall>j < Suc i. (z # zs) ! j = []" using IH True less_Suc_eq_0_disj by force
    moreover have "(z # zs) ! (Suc i) = x # ys" using IH by auto
    moreover have "xs = ys @ concat (drop (Suc (Suc i)) (z # zs))" using IH  by auto
    ultimately show ?thesis by auto
  qed
qed auto

lemma update_eq:
  assumes "\<forall>j < length ss. j \<noteq> i \<longrightarrow> ss ! j = ts ! j"
  and "length ss = length ts"
  shows "ss = ts[i:=ss ! i]"
proof -
  have "\<forall>j < length ss. ss ! j = ts[i:=ss ! i] ! j"
    apply clarsimp using assms apply (case_tac "j = i") by auto
  moreover have "length ss = length (ts[i:=ss ! i])" using assms by auto
  ultimately show ?thesis using nth_equalityI by blast
qed

lemma concat_steps_empty: 
  assumes "[] = concat (mapi (\<lambda>i. map (f i)) n steps)"
  shows "\<forall> i < length steps. steps ! i = []"
using assms
proof (induct steps arbitrary: n)
  case Nil then show ?case by auto
next
  case (Cons x xs) 
  from Cons have x:"x = []" by auto
  from Cons have "[] = concat (mapi (\<lambda>i. map (f i)) (Suc n) xs)" by auto
  then have "\<forall>i<length xs. xs ! i = []" using Cons by auto
  then show ?case using x by (metis Suc_less_eq gr0_conv_Suc length_Cons nth_Cons_Suc nth_non_equal_first_eq)
qed

(*parallel step with r/p/s information*)
inductive_set
  par_rstep2 :: "('f,'v) trs \<Rightarrow> (('f,'v)term \<times> (('f,'v) rule \<times> pos \<times> ('f,'v) subst)list \<times> ('f,'v) term) set"
  for R :: "('f,'v)trs"
where
  root_step2[intro]: "(s,t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>, [((s, t), [], \<sigma>)], t \<cdot> \<sigma>) \<in> par_rstep2 R"
| par_step_fun2[intro]: "\<lbrakk>\<And>i. i < length ts \<Longrightarrow> (ss ! i, steps ! i, ts ! i) \<in> par_rstep2 R\<rbrakk> \<Longrightarrow> 
    length ss = length ts \<Longrightarrow> length ss = length steps \<Longrightarrow>
    (Fun f  ss, concat (mapi (\<lambda>i si. (map (\<lambda> (rl, p, \<sigma>). (rl, i # p,\<sigma>)) si)) 0 steps), Fun f ts) \<in> par_rstep2 R"
| par_step_var2[intro]: "(Var x, [], Var x) \<in> par_rstep2 R"

lemma par_rstep2_refl:
  shows "(s, [], s) \<in> par_rstep2 R"
proof (induct s)
  case (Fun f ts) 
  let ?steps = "replicate (length ts) []"
  {
    fix i
    assume "i < length ts"
    then have "(ts ! i, replicate (length ts) [] ! i, ts ! i) \<in> par_rstep2 R" using Fun by auto
  }
  from par_rstep2.intros(2)[OF this]
  show ?case using concat_replicate_empty length_replicate by metis
qed auto

lemma par_rstep2_empty:
  assumes "(s, [], t) \<in> par_rstep2 R"
  shows "s = t"
using assms
proof (induct s arbitrary: t)
  case (Var x) show ?case using par_rstep2.cases[OF Var] by auto
next
  case (Fun f ss)  obtain ts steps where
    steps_empty: "[] = concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) 0 steps)" and t_dec: "t = Fun f ts"
    and steps: "(\<forall>x<length ts. (ss ! x, steps ! x, ts ! x) \<in> par_rstep2 R)" and l:"length ss = length ts" "length ss = length steps" 
    using Fun(2) unfolding  par_rstep2.simps[of "Fun f ss" "[]" t R] by auto
  have steps_i: "\<forall>i < length steps. (steps ! i = [])" using concat_steps_empty steps_empty l by fast
  then have "\<forall>i<length ts. (ss ! i, steps ! i, ts ! i) \<in> par_rstep2 R" using steps l by auto 
  have "\<forall>i < length ts. (ss ! i = ts ! i)"
  proof (intro allI impI)
    fix i
    assume A: "i < length ts" 
    have "(ss ! i, steps ! i, ts ! i) \<in> par_rstep2 R" using steps A by auto
    then show "ss ! i = ts ! i" using Fun(1) by (metis A steps_i l(1) l(2) nth_mem) 
  qed
  then have "ss = ts" using l by (metis nth_equalityI)
  then show ?case unfolding t_dec by auto
qed

lemma par_rstep2_append:
  assumes "length ss = length ts" and "length ts = length steps"
  and "\<forall>i < length ss. (ss ! i, steps ! i, ts ! i) \<in> par_rstep2 R"
  and "\<forall>i < length ss'. (ss' ! i, steps' ! i, ts' ! i) \<in> par_rstep2 R"
  shows "\<forall> i < length (ss @ ss'). ((ss @ ss') ! i, (steps @ steps') ! i, (ts @ ts') ! i) \<in> par_rstep2 R"
using assms
proof (induct rule: list_induct3)
  case (Cons s ss t ts step steps)
  show ?case 
  proof (intro allI impI)
    fix i
    assume i: "i < length ((s # ss) @ ss')"
    show "(((s # ss) @ ss') ! i, ((step # steps) @ steps') ! i, ((t # ts) @ ts') ! i) \<in> par_rstep2 R"
    proof (cases i)
      case 0
      then show ?thesis using Cons by auto
    next
      case (Suc j)
      from Cons have "\<forall>i<length (ss @ ss'). ((ss @ ss') ! i, (steps @ steps') ! i, (ts @ ts') ! i) \<in> par_rstep2 R" by fastforce
      with Suc i show ?thesis by simp
    qed
  qed
qed auto

lemma par_rstep2_ctxt_closed:
  assumes "(s,steps,t) \<in> par_rstep2 R"
  shows "(C\<langle>s\<rangle>, map (\<lambda> (rl, p, \<sigma>). (rl, hole_pos C @ p, \<sigma>)) steps, C\<langle>t\<rangle>) \<in> par_rstep2 R"
using assms
proof (induct C arbitrary:s t steps)
  case (More f ls C' rs) 
  then have step: "(C'\<langle>s\<rangle>, map (\<lambda> (rl, p, \<sigma>). (rl, hole_pos C' @ p, \<sigma>)) steps, C'\<langle>t\<rangle>) \<in> par_rstep2 R" (is "(_,?steps,_) \<in> _")
    using More by auto
  have ls: "\<forall> i < length ls. (ls ! i, [], ls ! i) \<in> par_rstep2 R"
    using par_rstep2_refl by auto
  have rs: "\<forall> i < length rs. (rs ! i,[], rs ! i) \<in> par_rstep2 R"
    using par_rstep2_refl  by auto
  let ?steps' = "replicate (length ls) [] @ (?steps # replicate (length rs) [])"
  from par_rstep2_append[of "[C'\<langle>s\<rangle>]" "[C'\<langle>t\<rangle>]" "[?steps]"] step rs
  have "\<forall>i < length (C'\<langle>s\<rangle> # rs). ((C'\<langle>s\<rangle> # rs) ! i, (?steps # replicate (length rs) []) ! i, (C'\<langle>t\<rangle> # rs) ! i) \<in> par_rstep2 R"
    by simp
  then have x: "\<forall>i < length (ls @ C'\<langle>s\<rangle> # rs). ((ls @ C'\<langle>s\<rangle> # rs) ! i, ?steps' ! i, (ls @ C'\<langle>t\<rangle> # rs) ! i) \<in> par_rstep2 R"
    (is "\<forall> i < length _ . (?ss ! i, _, ?ts ! i) \<in> _")
    using par_rstep2_append[of ls ls] ls by simp
  have l: "length ?ss = length ?ts" by auto
  have lx: "length (replicate (length ls) []) = length ls" by auto
  have "(Fun f ?ss, concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) 0 ?steps'), Fun f ?ts) \<in> par_rstep2 R"
    using x l by auto
  then have "(Fun f ?ss,concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) (length ls) ([?steps] @ replicate (length rs) [])), Fun f ?ts)  \<in> par_rstep2 R" 
    unfolding append_mapi concat_append concat_replicate_empty[where ?n=0] by auto
  then have "(Fun f ?ss,
    concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) (length ls) [?steps]) @
    concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) (Suc (length ls)) (replicate (length rs) [])), Fun f ?ts) \<in> par_rstep2 R"
    unfolding append_mapi concat_append by auto
  then have *: "(Fun f ?ss, concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) (length ls) [?steps]), Fun f ?ts)  \<in> par_rstep2 R"
    unfolding length_append[symmetric] lx using concat_replicate_empty append_Nil2 by metis
  have f_comp: "((\<lambda>(rl, p, \<sigma>). (rl, length ls # p, \<sigma>)) \<circ> (\<lambda>(rl, p, \<sigma>). (rl, hole_pos C' @ p, \<sigma>))) = 
    ((\<lambda>(rl, p, \<sigma>). (rl, length ls # hole_pos C' @ p, \<sigma>)))" by auto 
   from * show ?case apply auto using f_comp by metis
qed auto

lemma rstep_r_p_s_imp_par_rstep2: 
  assumes "(s,t) \<in> rstep_r_p_s R (l,r) p \<sigma>"
  shows "(s, [((l, r), p, \<sigma>)], t) \<in> par_rstep2 R"
proof -
  from assms obtain C  where lr: "(l,r) \<in> R" and C_dec: "C = ctxt_of_pos_term p s" and p: "p \<in> poss s" 
    and  s_dec: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t_dec: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"  unfolding rstep_r_p_s_def by fastforce
  have h: "hole_pos C = p" unfolding C_dec using p by auto 
  then have s:"(l \<cdot> \<sigma>, [((l, r), [], \<sigma>)], r \<cdot> \<sigma>) \<in> par_rstep2 R" using par_rstep2.intros(1)[OF lr] by auto
  have "(C\<langle>l \<cdot> \<sigma>\<rangle>, [((l, r), p, \<sigma>)], C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> par_rstep2 R" using par_rstep2_ctxt_closed[OF s] using h by auto
  then show ?thesis unfolding s_dec t_dec using par_rstep2_ctxt_closed C_dec by auto
qed

lemma par_rstep2_singleton:
  assumes "(s, steps, t) \<in> par_rstep2 R"
  and "steps = [(lr, p, \<sigma>)]"
  shows "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
  using assms
proof (induct arbitrary: lr p \<sigma>)
  case (par_step_fun2 ts ss steps f)
  let ?msteps = "mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 steps"
  from par_step_fun2 obtain i where
    im:"i < length ?msteps" and mstepsi:"?msteps ! i = [(lr, p, \<sigma>)]"
    and mstepsnil:"\<forall>j < length ?msteps. j \<noteq> i \<longrightarrow> ?msteps ! j = []"
    using concat_singleton[of ?msteps "(lr, p, \<sigma>)"] by auto
  then have i: "i < length steps" using length_mapi by metis
  from i par_step_fun2 have its:"i < length ts" by auto
  {
    fix j
    assume j:"j < length ss"  and "j \<noteq> i"
    with par_step_fun2 mstepsnil im length_mapi have nil:"?msteps ! j = []" by metis
    from j have *:"j < length steps" by (metis par_step_fun2(4))
    from nil have nil:"steps ! j = []" unfolding mapi_nth[OF *] by simp
    have "j < length ts" using j par_step_fun2(3) by auto
    from par_step_fun2(1)[OF this, unfolded nil] have "ss ! j = ts ! j"
      using par_rstep2_empty by auto
  }
  then have  "\<forall>j < length ss. j \<noteq> i \<longrightarrow> ss ! j = ts ! j" by blast
  then have "ss = ts[i := ss ! i]" using i par_step_fun2 update_eq by blast 
  then have ts:"ts = take i ss @ ts ! i # drop (Suc i) ss"
    by (metis append_eq_conv_conj append_take_drop_id its length_take par_step_fun2.hyps(3) take_drop_update_first upd_conv_take_nth_drop)
  from mapi_nth[OF i,of _ 0] have
    stepsi:"?msteps ! i  = (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) i (steps ! i)" by auto
  with mstepsi obtain q where q:"p = i#q" by auto
  with stepsi mstepsi have stepsi:"steps ! i = [(lr, q, \<sigma>)]" by auto
  from par_step_fun2(2)[OF its stepsi] have
    "q \<in> poss (ss ! i)" "lr \<in> R"
    "(ss ! i) |_ q = fst lr \<cdot> \<sigma>" "(ts ! i) = (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle>"
    unfolding rstep_r_p_s_def' by auto
  then have "(Fun f ss, Fun f ts) \<in> rstep_r_p_s R lr p \<sigma>" using q
    its par_step_fun2(3) unfolding rstep_r_p_s_def' apply auto
    using id_take_nth_drop[of i ts] ts by metis
  then show ?case by auto
next
  case (root_step2 l r \<tau>)
  then show ?case unfolding rstep_r_p_s_def by auto
qed auto


(*
lemma par_rstep2_subst_closed:
 assumes "(s,steps,t) \<in> par_rstep2 R"
 shows "(s\<cdot>\<tau>,map (\<lambda> (rl,p,\<sigma>). (rl,hole_pos C@p,\<sigma>\<circ>\<^sub>s\<tau>)) steps,t\<cdot>\<tau>) \<in> par_rstep2 R"
s o r r y
*)

(*
lemma assumes "\<forall>x.\<exists>y. P(x,y)" shows "\<exists>f.\<forall>x. P(x,f(x))" using assms by metis
lemma y: assumes "\<forall>j < length (s # ss). P((s # ss)!j)" shows "\<forall>j < length ss. P(ss!j)" proof
 fix j show "j < length ss \<longrightarrow> P (ss!j)" using assms by auto
qed
*)

lemma par_step_merge:
  assumes  "length ss = length ts" 
  and "\<forall> j < length ss. \<exists> steps. (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (ss ! j, steps, ts ! j) \<in> par_rstep2 R"
  shows "\<exists> steps. (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (Fun f ss, steps, Fun f ts) \<in> par_rstep2 R"
proof -
  from assms have a:"\<exists> steps. (length steps = length ss) \<and> 
    (\<forall> j < length ss. (\<forall>i<length (steps ! j). fst ((steps ! j) ! i) = (l, r)) \<and> (ss ! j, steps ! j, ts ! j) \<in> par_rstep2 R)"
  proof (induct ss arbitrary: ts)
    case (Cons s ss) 
    obtain u us where ts_dec: "ts = u # us" using Cons by (cases ts, auto)
    then have l: "length ss = length us" using Cons by auto
    from Cons(3) obtain steps1 where step1: "(\<forall>i<length steps1. fst (steps1 ! i) = (l,r)) \<and> (s, steps1, u) \<in> par_rstep2 R" 
      using ts_dec by auto
    have y: "\<forall>j<length ss. \<exists>steps. (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (ss ! j, steps, us ! j) \<in> par_rstep2 R"
    proof (intro allI impI)
      fix j
      assume A:"j < length ss"
      from Cons(3) A obtain steps where
        "(\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> ((s # ss) ! (j + 1), steps, (u # us) ! (j + 1)) \<in> par_rstep2 R"
        unfolding ts_dec by auto
      then show "\<exists> steps. (\<forall>i<length steps. ((fst (steps!i) = (l,r)))) \<and> (ss ! j, steps, us ! j) \<in> par_rstep2 R"
        using Cons by auto
    qed
    obtain steps2 where l1: "length steps2 = length ss" and
      steps2: "\<forall>j<length ss. (\<forall>i<length (steps2 ! j). fst (steps2 ! j ! i) = (l, r)) \<and> (ss ! j, steps2 ! j, us ! j) \<in> par_rstep2 R"
      using Cons(1)[OF l y] unfolding ts_dec by auto
    have l: "length (steps1 # steps2) = length (s # ss)" using l1 by auto
    have "\<forall>j<length (s # ss). 
      (\<forall>i<length ((steps1 # steps2) ! j). fst ((steps1 # steps2) ! j ! i) = (l,r)) \<and>  
      ((s # ss) ! j, (steps1 # steps2) ! j, ts ! j) \<in> par_rstep2 R"
    proof (intro allI impI)
      fix j
      assume j: "j < length (s # ss)"
      show "(\<forall>i<length ((steps1 # steps2) ! j). fst ((steps1#steps2)!j!i) = (l,r)) \<and> 
        ((s # ss) ! j, (steps1 # steps2) ! j, ts ! j) \<in> par_rstep2 R"
      proof (cases j) 
        case 0
        then show ?thesis using step1 unfolding ts_dec by auto
      next
        case (Suc j')
        then show ?thesis unfolding ts_dec using steps2 j by (metis length_Cons not_less_eq nth_Cons_Suc)
      qed
    qed
    then show ?case using l by metis
  qed auto
  then obtain steps where l: "length steps = length ss" and
    k: "\<forall>j<length ts. (\<forall>i<length (steps ! j). fst (steps ! j ! i) = (l, r)) \<and> (ss ! j, steps ! j, ts ! j) \<in> par_rstep2 R"
    using assms(1) by auto
  then have two: "(Fun f ss, concat (mapi (\<lambda>i. map (\<lambda>(rl, p, \<sigma>). (rl, i # p, \<sigma>))) 0 steps), Fun f ts) \<in> par_rstep2 R"
    (is "(_,?steps,_) \<in>  _")
    using assms by auto
  have j: "\<forall>j<length steps. \<forall>i<length (steps ! j). fst (steps ! j ! i) = (l, r)" using k l assms(1) by auto
  have one: "\<forall>i<length ?steps. fst (?steps ! i) = (l, r)" using fst_concat_mapi[OF j] by auto
  show ?thesis using one two by auto
qed

lemma subst_step_imp_par_rstep2:
  assumes "(\<sigma>1(w), \<tau>(w)) \<in> rstep_r_p_s R (l, r) v2 \<sigma>2"
  and "\<forall>x. (x = w) \<or> (\<sigma>1(x) = \<tau>(x))" 
  shows "\<exists> steps. (\<forall>i < length steps. fst (steps ! i) = (l, r)) \<and> (t \<cdot> \<sigma>1, steps, t \<cdot> \<tau>) \<in> par_rstep2 R"
proof (induct t)
  case (Var y)
  then show ?case
  proof (cases "y = w")
    case True 
    let ?steps = "[((l, r), v2, \<sigma>2)]"
    have len: "\<forall>i < length ?steps. fst (?steps ! i) = (l, r)" by auto
    from True have "(\<sigma>1 y, \<tau> y) \<in> rstep_r_p_s R (l, r) v2 \<sigma>2"
      using assms unfolding par_rstep2_def by auto
    then have "(\<sigma>1 y, ?steps, \<tau> y) \<in> par_rstep2 R" using rstep_r_p_s_imp_par_rstep2 by fast
    then have "(Var y \<cdot> \<sigma>1, ?steps, Var y \<cdot> \<tau>) \<in> par_rstep2 R" by auto
    then show ?thesis using len by blast 
  next
    case False 
    have len: "\<forall>i < length []. fst ([] ! i) = (l, r)" by auto
    have id: "(Var y \<cdot> \<sigma>1, [], Var y \<cdot> \<sigma>1) \<in> par_rstep2 R" using par_rstep2_refl by auto
    have "\<sigma>1(y) = \<tau>(y)" using assms False by auto
    then have "(Var y \<cdot> \<sigma>1, [], Var y \<cdot> \<tau>) \<in> par_rstep2 R" using id by auto
    then show ?thesis using len by blast
  qed
next
  case (Fun f ts) 
  let ?ts\<sigma> = "map (\<lambda>t. t \<cdot> \<sigma>1) ts"
  let ?ts\<tau> = "map (\<lambda>t. t \<cdot> \<tau>) ts"
  from Fun have "\<forall> j < length ts. \<exists> steps. 
    (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (ts ! j \<cdot> \<sigma>1, steps, ts ! j \<cdot> \<tau>) \<in> par_rstep2 R" by auto
  then have x: "\<forall>j < length ?ts\<sigma>. \<exists> steps. 
    (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (?ts\<sigma> ! j, steps, ?ts\<tau> ! j) \<in> par_rstep2 R" by auto
  have "\<exists>steps. (\<forall>i<length steps. fst (steps ! i) = (l, r)) \<and> (Fun f ?ts\<sigma>, steps, Fun f ?ts\<tau>) \<in> par_rstep2 R"
    using par_step_merge[OF _ x] by auto
  then show ?case by auto 
qed

lemma par_rstep2_decompose:
  assumes "(s, steps, t) \<in> par_rstep2 R"
  and "steps = x # xs"
  shows "\<exists> s'. (s, [x], s') \<in> par_rstep2 R \<and> (s', xs, t) \<in> par_rstep2 R"
using assms
proof (induct  arbitrary: x xs rule: par_rstep2.induct)
  case (root_step2 s t \<sigma>)
  then have "xs = []" by auto
  then have "(t \<cdot> \<sigma>, xs, t \<cdot> \<sigma>) \<in> par_rstep2 R" using par_rstep2_refl by auto
  moreover from root_step2 have "(s \<cdot> \<sigma>, [x], t \<cdot> \<sigma>) \<in> par_rstep2 R" by auto
  ultimately show ?case by auto
next
  case (par_step_fun2 ts ss steps f)
  let ?msteps = "mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 steps"
  from concat_Cons[OF par_step_fun2(5)] obtain i ys where
    i: "i < length ?msteps" and 
    nil: "\<forall>j < i. ?msteps ! j = []" and
    x: "?msteps ! i = x # ys" and
    xs: "xs = ys @ concat (drop (Suc i) ?msteps)" by auto
  then have ist: "i < length steps" using length_mapi by metis
  from x have "x # ys = map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>)) (steps ! i)"
    unfolding mapi_nth[OF ist, of _ 0]  by auto
  then obtain lr p \<sigma> zs where x:"x = (lr, i#p, \<sigma>)" and zs:"steps ! i = (lr, p, \<sigma>) # zs"
    and ys:"ys = map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>)) zs" by auto
  with par_step_fun2 ist obtain s' where
    s': "(ss ! i, [(lr, p, \<sigma>)], s') \<in> par_rstep2 R \<and> (s', zs, ts ! i) \<in> par_rstep2 R"
    by fastforce
  let ?z = "(lr, p, \<sigma>)"
  let ?us = "take i ss @ s' # drop (Suc i) ss"
  let ?steps' = "replicate i [] @ [[?z]] @ replicate (length steps - (Suc i)) []"
  have steps':"length ss = length ?steps'" using ist par_step_fun2(4) by auto
  have us: "length ss = length ?us" using ist par_step_fun2(4) by auto
  {
    fix j
    assume j:"j < length ?us"
    {
      assume "j < i"
      then have "?steps' ! j = []" 
        by (metis (erased, opaque_lifting) length_replicate nth_append nth_replicate)
      moreover have "?us ! j = ss ! j"         
        by (metis \<open>j < i\<close> j nat_le_linear nth_append_take_is_nth_conv take_all us)
      ultimately have "(ss ! j, ?steps' ! j, ?us ! j) \<in> par_rstep2 R"
        using par_rstep2_refl by auto
    } moreover {
      assume "j = i"
      then have "?us ! j = s'" by (metis j nat_less_le nth_append_take us)
      moreover have "?steps' ! j = [?z]"
        by (metis \<open>j = i\<close> append_Cons length_replicate nth_append_length)
      ultimately have "(ss ! j, ?steps' ! j, ?us ! j) \<in> par_rstep2 R"
        using s' \<open>j = i\<close> by auto
    } moreover {
      assume *:"j > i"
      have "j < length steps" unfolding par_step_fun2(4)[symmetric] us using j .
      then have "j - Suc i < length steps - Suc i" using * by auto
      then have "?steps' ! j = []" using * unfolding nth_append by auto
      moreover from * have "?us ! j = ss ! j" 
        by (metis j less_imp_le_nat nat_le_linear nth_append nth_append_drop_is_nth_conv take_all us)
      ultimately have "(ss ! j, ?steps' ! j, ?us ! j) \<in> par_rstep2 R"
        using par_rstep2_refl by auto
    }
    ultimately
    have "(ss ! j, ?steps' ! j, ?us ! j) \<in> par_rstep2 R" by fastforce
  } note args = this
  have conc: "concat (mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 ?steps') = [x]"
    apply (subst append_mapi)+
    apply (subst concat_append)+
    apply (subst mapi_map_replicate_trivial)+
    apply (subst concat_replicate_trivial)+
    using x by auto
  from par_rstep2.intros(2)[OF args us steps', unfolded conc]
  have first:"(Fun f ss, [x], Fun f ?us) \<in> par_rstep2 R" by auto
  let ?steps'' = "take i steps @ zs # drop (Suc i) steps"
  have steps'': "length ?us = length ?steps''" 
    by (metis ist length_list_update par_step_fun2(4) upd_conv_take_nth_drop)
  have ts: "length ?us = length ts"by (metis par_step_fun2(3) us)
  {
    fix j
    assume j: "j < length ts"
    have "(?us ! j, ?steps'' ! j, ts ! j) \<in> par_rstep2 R"
      by (metis ist j less_imp_le_nat nth_append_take nth_list_update_neq par_step_fun2.hyps(1) par_step_fun2.hyps(4) s' upd_conv_take_nth_drop)
  } note args = this
  let ?isteps = "mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 (take i steps)"
  {
    fix xs
    assume "xs \<in> set ?isteps"
    then obtain j where j:"j < length (take i steps)" and xs: "?isteps ! j = xs"
      by (metis (erased, lifting) in_set_idx length_mapi)
    then have eq: "steps ! j = (take i steps) ! j" by auto
    from j have j2:"j < length steps" by auto
    from  xs eq have "?msteps ! j = xs"
      unfolding mapi_nth[OF j2, of _ 0] mapi_nth[OF j, of _ 0] by auto
    moreover have "j < i" using j by auto
    ultimately have "xs = []" using nil by blast
  }   
  then have *:"concat (mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 (take i steps)) = []"
    by auto
  from ist have min:"(min (length steps) i) = i" by auto
  have conc: "concat (mapi (\<lambda>i. map (\<lambda>(lr, p, \<sigma>). (lr, i # p, \<sigma>))) 0 ?steps'') = xs"
    apply (subst append_mapi)
    apply (subst concat_append)
    apply (subst *)
    apply (simp add: min)
    unfolding xs ys zs
    apply (subst mapi_drop[of "Suc i" _ 0 steps])
    by auto
  from par_rstep2.intros(2)[OF args ts steps'', unfolded conc]
  have "(Fun f ?us, xs, Fun f ts) \<in> par_rstep2 R" by auto
  with first show ?case by auto
qed auto

lemma par_rstep2_imp_seq:
  assumes "(t, steps, v) \<in> par_rstep2 R"
  shows "\<exists> ss \<in> seq R. first ss = t \<and> last ss = v \<and> length steps = length (snd ss) \<and> 
  (\<forall> i < length steps. steps ! i = (get_rule (snd ss ! i), get_pos (snd ss ! i), get_subst (snd ss ! i)))"
using assms
proof (induct steps arbitrary: t)
  case Nil then have eq:"t = v" using par_rstep2_empty by auto
  then have "(t,[]) \<in> seq R" (is "?ss") using seq.intros by auto
  then show ?case unfolding eq apply auto
    by (metis last.simps(1) first.simps snd_conv)
next
  case (Cons x xs)
  then obtain t' where step: "(t, [x], t') \<in> par_rstep2 R" and steps: "(t', xs, v) \<in> par_rstep2 R"
    using par_rstep2_decompose by metis
  then obtain rl p \<sigma> where x_dec: "x = (rl,p,\<sigma>)" using prod_cases3 by blast
  with step have step: "(t, t') \<in> rstep_r_p_s R rl p \<sigma>"
    using par_rstep2_singleton by metis
  then obtain ss' where key: "ss' \<in> seq R \<and> first ss' = t' \<and> last ss' = v \<and> length xs = length (snd ss') \<and> 
    (\<forall>i<length xs. xs ! i = (get_rule (snd ss' ! i), get_pos (snd ss' ! i), get_subst (snd ss' ! i)))"
    using Cons steps by metis
  then have "(t, (t, rl, p, \<sigma>, True, t') # snd ss') \<in> seq R" (is "?ss \<in> _")
    using step seq.intros(2) by (metis first.elims snd_conv)
  moreover have "first ?ss = t" by auto
  moreover have "last ?ss = v" using key unfolding last.simps get_target_def
    apply auto by (metis first.simps surjective_pairing)
  moreover have "length (x # xs) = length (snd ?ss)" using key by auto
  moreover have "\<forall>i<length (x # xs). (x # xs) ! i = (get_rule (snd ?ss ! i), get_pos (snd ?ss ! i), get_subst (snd ?ss ! i))"
    apply (intro allI impI) apply (case_tac i)
    using key unfolding x_dec get_rule_def get_pos_def get_subst_def by auto
  ultimately show ?case by fast
qed

(* close variable peaks (left-linear case) *)
lemma variable_steps_left_lin:
  assumes xy:"(s, t) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1"
  and     xz:"(s, u) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2"
  and "p1 @ q = p2"
  and "(v1 @ v2) = q" and "v1 \<in> poss l1" and "l1 |_ v1 = Var w"
  and lin: "linear_term l1"
  defines "\<tau> \<equiv> (\<lambda>y. if y = w then replace_at (\<sigma>1 y) v2 (r2 \<cdot> \<sigma>2) else \<sigma>1 y)"
  defines "v \<equiv> (ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> \<tau>\<rangle>"
  shows "(u, v) \<in> (rstep_r_p_s R (l1, r1) p1 \<tau>)" (is "?g1")
    "\<exists>steps. (\<forall> i < length steps. ((fst (steps!i)) = (l2,r2))) \<and> 
    (t,steps,v) \<in> par_rstep2 R" (is "?g2")
proof -
  from assms show ?g1 using variable_steps_lin(1)[OF xy xz] by fast
  (*begin*)
  show ?g2
  proof - 
    have k1: "p1@v1 \<in> poss s" using assms unfolding rstep_r_p_s_def Let_def by auto
    have k2: "(p1@v1)@v2 \<in> poss s" using assms unfolding rstep_r_p_s_def Let_def by auto 
    have s_dec1: "s = (ctxt_of_pos_term p1 s)\<langle>l1\<cdot>\<sigma>1\<rangle>" using xy unfolding rstep_r_p_s_def Let_def by auto
    then have "s|_p1 = l1\<cdot>\<sigma>1" by (metis (erased, lifting) mem_Collect_eq old.prod.case rstep_r_p_s_def subt_at_ctxt_of_pos_term xy)
    then have "(s|_p1)|_v1 = \<sigma>1(w)" using assms by (metis eval_term.simps(1) subt_at_subst)
    then have "s|_(p1@v1) = \<sigma>1(w)" using k1 by (metis subterm_poss_conv)
    then have "(s|_(p1@v1))|_v2 = (\<sigma>1(w))|_v2" by metis
    then have "(s|_(p1@v1@v2)) = (\<sigma>1(w))|_v2"  using k2 by (metis append_assoc k1 subt_at_append)
    then have "(s|_p2) = (\<sigma>1(w))|_v2"  using assms by auto    
    have s_dec2: "s = (ctxt_of_pos_term p2 s)\<langle>l2\<cdot>\<sigma>2\<rangle>" using xz unfolding rstep_r_p_s_def Let_def by auto
    then have "s|_p2 = l2\<cdot>\<sigma>2" by (metis (erased, lifting) mem_Collect_eq old.prod.case rstep_r_p_s_def subt_at_ctxt_of_pos_term xz)
    then have s1:"\<sigma>1(w) = replace_at (\<sigma>1 w) v2 (l2\<cdot>\<sigma>2)" using assms
      by (metis \<open>s |_ (p1 @ v1) = \<sigma>1 w\<close> \<open>s |_ p2 = \<sigma>1 w |_ v2\<close> ctxt_supt_id k2 subterm_poss_conv)
    have s2:"\<tau>(w)  = replace_at (\<sigma>1 w) v2 (r2\<cdot>\<sigma>2)" using assms by auto
    have "(l2\<cdot>\<sigma>2,r2\<cdot>\<sigma>2) \<in> rstep_r_p_s R (l2,r2) [] \<sigma>2" using assms unfolding rstep_r_p_s_def Let_def by auto
    then have "(replace_at (\<sigma>1 w) v2 (l2\<cdot>\<sigma>2),replace_at (\<sigma>1 w) v2 (r2\<cdot>\<sigma>2)) \<in> rstep_r_p_s R (l2,r2) v2 \<sigma>2"
      unfolding rstep_r_p_s_def Let_def apply auto
      apply (metis \<open>s |_ (p1 @ v1) = \<sigma>1 w\<close> k2 poss_append_poss s1) apply (metis s1) by (metis s1)
    then have subst_step: "(\<sigma>1(w),\<tau>(w)) \<in> rstep_r_p_s R (l2,r2) v2 \<sigma>2" using s1 s2 by auto 
    have aux: "\<forall>x. (x = w) \<or> (\<sigma>1(x) = \<tau>(x))" using assms unfolding \<tau>_def by auto
    then obtain steps where A1: "\<forall>i < length steps. (fst (steps!i) = (l2,r2))" and B1: "(r1\<cdot>\<sigma>1,steps,r1\<cdot>\<tau>) \<in> par_rstep2 R"
      using subst_step_imp_par_rstep2[OF subst_step aux] by fast
  (*end*)
    have B2: "((ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> \<sigma>1\<rangle>, map (\<lambda>(rl, p, \<sigma>). (rl, hole_pos (ctxt_of_pos_term p1 s) @ p, \<sigma>)) steps, (ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> \<tau>\<rangle>) \<in> par_rstep2 R" (is "(_,?steps,_) \<in> _")
      using par_rstep2_ctxt_closed[OF B1] by auto
    have A2: "\<forall>i < length ?steps. ((fst (?steps!i)) = (l2,r2))"
    proof (intro allI impI)
      fix i
      assume "i < length ?steps"
      then have l:"i < length steps" by auto
      then have "fst (steps!i) = (l2,r2)" using A1 by auto
      then obtain p1 \<sigma>1 where step_dec: "steps!i = ((l2,r2),p1,\<sigma>1)" by (cases "steps ! i", auto)
      have "(\<lambda>(rl, p, \<sigma>). (rl, hole_pos (ctxt_of_pos_term p1 s) @ p, \<sigma>)) (steps ! i) = 
            ((l2, r2),hole_pos (ctxt_of_pos_term p1 s) @p1,\<sigma>1)"
        using step_dec by auto
      then show "fst (?steps!i) = (l2,r2)" unfolding nth_map[OF l] using step_dec by auto
    qed
    have t_dec: "t = (ctxt_of_pos_term p1 s)\<langle>r1\<cdot>\<sigma>1\<rangle>" using xy unfolding rstep_r_p_s_def Let_def by auto
    from A2 B2 show ?thesis unfolding t_dec v_def  by fast
  qed
qed

(*Section 3: decreasingness for TRSs *)

(* new part begin: conversions *)
type_synonym ('f,'v) conv = "('f,'v) term \<times> ('f,'v) step list"

inductive_set conv :: "('f,'v) trs \<Rightarrow> ('f,'v) conv set" 
for \<R> where 
   "(s, []) \<in> conv \<R>"
 | "(s, t) \<in> rstep_r_p_s \<R> r p \<sigma> \<Longrightarrow> (t, ts) \<in> conv \<R> \<Longrightarrow> (s, (s,r,p,\<sigma>,True,t) # ts) \<in> conv \<R>"
 | "(s, t) \<in> rstep_r_p_s \<R> r p \<sigma> \<Longrightarrow> (s, ts) \<in> conv \<R> \<Longrightarrow> (t, (s,r,p,\<sigma>,False,t) # ts) \<in> conv \<R>"

lemma seq_imp_conv: 
assumes "ss \<in> seq R"
shows "ss \<in> conv R" 
using assms 
proof (induct "snd ss" arbitrary:"ss")
  case Nil then obtain s where ss_dec: "ss = (s,[])" by (cases ss, auto)
  then show ?case by (auto intro: conv.intros)
next
  case (Cons step ts)
  from Cons(2) obtain s where ss_dec: "ss = (s, step # ts)" by (cases ss, auto)
  with Cons(3) obtain rl p \<tau> t where step_dec: "step = (s, rl, p, \<tau>, True, t)" by (auto elim: seq.cases)
  then have "(s,t) \<in> rstep_r_p_s R rl p \<tau>" and "(t, ts) \<in> conv R"
    using Cons by (auto simp add: seq_chop_first ss_dec step_dec)
  then show ?case unfolding ss_dec step_dec by (simp add: conv.intros) 
qed

fun conv_close :: "('f,'v) seq \<Rightarrow> ('f,'v) ctxt \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) seq"
 where "conv_close ss C \<tau> = (C\<langle>fst ss \<cdot> \<tau>\<rangle>, map (\<lambda>step. step_close step C \<tau>) (snd ss))"

lemma conv_super_closed1:
  assumes "ss \<in> conv R"
  shows "conv_close ss C \<sigma> \<in> conv R \<and> (first (conv_close ss C \<sigma>)) = C\<langle>first ss \<cdot> \<sigma>\<rangle> \<and> 
    last (conv_close ss C \<sigma>) = C\<langle>last ss \<cdot> \<sigma>\<rangle>"
proof - 
  from assms obtain u steps where "ss = (u, steps)" and conv:"(u, steps) \<in> conv R" by (cases ss) auto 
  let ?ss = "(u, steps)"
  from conv have "conv_close ?ss C \<sigma> \<in> conv R \<and> (first (conv_close ?ss C \<sigma>)) = C\<langle>first ?ss \<cdot> \<sigma>\<rangle> \<and> 
    last (conv_close ?ss C \<sigma>) = C\<langle>last ?ss \<cdot> \<sigma>\<rangle>"
  proof (induct rule: conv.induct)
    case (2 s t r p \<tau> ts)
    then have "(C\<langle>s \<cdot> \<sigma>\<rangle>,C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> rstep_r_p_s R r (hole_pos C@p) (\<tau> \<circ>\<^sub>s \<sigma>)" 
      using rstep_r_p_s_ctxt_closed2[OF rstep_r_p_s_subst_closed[OF 2(1)]] by auto
    with 2 show ?case by (auto intro: conv.intros simp: get_target_def)
  next
    case (3 t s r p \<tau> ts)
    then have "(C\<langle>t \<cdot> \<sigma>\<rangle>,C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> rstep_r_p_s R r (hole_pos C@p) (\<tau> \<circ>\<^sub>s \<sigma>)" 
      using rstep_r_p_s_ctxt_closed2[OF rstep_r_p_s_subst_closed[OF 3(1)]] by auto
    with 3 show ?case by (auto intro: conv.intros simp: get_target_def)
  qed (auto intro: conv.intros)
  with \<open>ss = (u, steps)\<close> show ?thesis by auto
qed

definition conv_concat :: "('f,'v) seq \<Rightarrow> ('f,'v) seq \<Rightarrow> ('f,'v) seq"
 where "conv_concat \<sigma>1 \<sigma>2 = (first \<sigma>1, snd \<sigma>1 @ snd \<sigma>2)"

lemma conv_chop_first_left: 
  assumes "(s, (s, rl, p, \<sigma>, True, t) # ss) \<in> conv R"
  shows "(t, ss) \<in> conv R \<and> (s, t) \<in> rstep_r_p_s R rl p \<sigma>" 
using assms by cases auto

lemma conv_chop_first_right: 
  assumes "(s, (t, rl, p, \<sigma>, False, s) # ss) \<in> conv R"
  shows "(t, ss) \<in> conv R \<and> (t, s) \<in> rstep_r_p_s R rl p \<sigma>" 
using assms by cases auto

lemma conv_dec:
  assumes "ss \<in> conv R"
  and "map l (snd ss) = l1 @ l2"
  shows "\<exists> L1 L2. ss = conv_concat L1 L2 \<and> L1 \<in> conv R \<and> L2 \<in> conv R \<and> map l (snd L1) = l1 \<and> 
    (map l (snd L2) = l2) \<and> first ss = first L1 \<and> last L1 = first L2 \<and> last L2 = last ss"
using assms 
proof (induct l1 arbitrary: ss)
  case Nil
  then have L1: "(first ss, []) \<in> conv R" (is "?L1 \<in> _") by (auto intro: conv.intros)
  then have "ss = conv_concat ?L1 ss" by (cases ss) (auto simp: conv_concat_def)
  then show ?case using Nil L1 by (cases ss) (auto)
next
  case (Cons a ls)
  then obtain s step ts where ss_dec: "ss = (s,step#ts)" by (cases ss, auto)
  with Cons(2) have "(s,step#ts) \<in> conv R" by auto
  then consider (left) rl p \<sigma> t where "step = (s,rl,p,\<sigma>,True,t)" "(s,t) \<in> rstep_r_p_s R rl p \<sigma>"
    | (right) rl p \<sigma> t where "step = (t,rl,p,\<sigma>,False,s)" "(t, s) \<in> rstep_r_p_s R rl p \<sigma>"
  by cases  auto
  then show ?case
  proof (cases)
    case (left)
    have i1:"(t,ts) \<in> conv R" using conv_chop_first_left(1)[OF Cons(2)[unfolded ss_dec[unfolded left]]] by auto
    have i2:"map l (snd (t,ts)) = ls@l2" using Cons(3) Cons unfolding ss_dec left by auto 
    from Cons(1)[OF i1 i2] obtain L1 L2 where 
      IH: "(t, ts) = conv_concat L1 L2" "L1 \<in> conv R" "L2 \<in> conv R"
      "map l (snd L1) = ls" "map l (snd L2) = l2" 
      "first (t, ts) = first L1" "last L1 = first L2" "last L2 = last (t, ts)" by fast
    have t: "first L1 = t" using IH(1) unfolding conv_concat_def by auto
    have f1: "ss = conv_concat (s,step # snd L1) L2" using IH(1)
      unfolding ss_dec left conv_concat_def by auto
    have f2: "(s,step # snd L1) \<in> conv R"
      using conv.intros step IH(2) t using left apply auto by (smt conv.intros(2) first.simps prod.collapse)
    have f4: "map l (snd (s,step# snd L1)) = a # ls"
      using IH(4) Cons(3) unfolding ss_dec left by auto
    have e1: "first ss = first ((s, step # snd L1))" unfolding ss_dec by auto
    have e2: "last (s,step#snd L1) = first L2"
      using IH left apply (auto simp add: get_target_def)
      by (metis first.simps surjective_pairing)
    have e3: "last L2 = last ss"
      unfolding ss_dec left last.simps get_target_def using IH by auto
    show ?thesis using f1 f2 IH(3) f4 IH(5) using e1 e2 e3 by metis
  next
    case (right)
have i1:"(t,ts) \<in> conv R" using conv_chop_first_right(1)[OF Cons(2)[unfolded ss_dec[unfolded right]]] by auto
    have i2:"map l (snd (t,ts)) = ls@l2" using Cons(3) Cons unfolding ss_dec right by auto 
    from Cons(1)[OF i1 i2] obtain L1 L2 where 
      IH: "(t, ts) = conv_concat L1 L2" "L1 \<in> conv R" "L2 \<in> conv R"
      "map l (snd L1) = ls" "map l (snd L2) = l2" 
      "first (t, ts) = first L1" "last L1 = first L2" "last L2 = last (t, ts)" by fast
    have t: "first L1 = t" using IH(1) unfolding conv_concat_def by auto
    have f1: "ss = conv_concat (s,step # snd L1) L2" using IH(1)
      unfolding ss_dec right conv_concat_def by auto
    have f2: "(s,step # snd L1) \<in> conv R"
      using conv.intros step IH(2) t using right apply auto by (smt conv.intros(3) first.simps prod.collapse)
    have f4: "map l (snd (s,step# snd L1)) = a # ls"
      using IH(4) Cons(3) unfolding ss_dec right by auto
    have e1: "first ss = first ((s, step # snd L1))" unfolding ss_dec by auto
    have e2: "last (s,step#snd L1) = first L2"
      using IH right apply (auto simp add: get_target_def)
      by (metis first.simps surjective_pairing)
    have e3: "last L2 = last ss"
      unfolding ss_dec right last.simps get_target_def using IH by auto
    show ?thesis using f1 f2 IH(3) f4 IH(5) using e1 e2 e3 by metis
  qed
qed
(** new part end **) 


(*diagrams*)
definition ld_trs :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> 
 ('f,'v) seq \<Rightarrow> ('f, 'v) seq \<Rightarrow> ('f, 'v) seq \<Rightarrow>
 ('f,'v) seq \<Rightarrow> ('f, 'v) seq \<Rightarrow> ('f, 'v) seq \<Rightarrow>
  bool"
 where "ld_trs R p jl1 jl2 jl3 jr1 jr2 jr3 = (p \<in> local_peaks R \<and> 
jl1 \<in> seq R \<and> jl2 \<in> seq R \<and> jl3 \<in> seq R \<and>
jr1 \<in> seq R \<and> jr2 \<in> seq R \<and> jr3 \<in> seq R \<and>
get_target (fst p) = first jl1 \<and> last jl1 = first jl2 \<and> last jl2 = first jl3 \<and>
get_target (snd p) = first jr1 \<and> last jr1 = first jr2 \<and> last jr2 = first jr3 \<and> 
last jl3 = last jr3
)"

(* new begin *)

definition ldc_trs :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> 
 ('f,'v) conv \<Rightarrow> ('f, 'v) seq \<Rightarrow> ('f, 'v) conv \<Rightarrow>
 ('f,'v) conv \<Rightarrow> ('f, 'v) seq \<Rightarrow> ('f, 'v) conv \<Rightarrow> bool"
where "ldc_trs R p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 = (p \<in> local_peaks R \<and> 
  cl\<^sub>1 \<in> conv R \<and> sl \<in> seq R \<and> cl\<^sub>2 \<in> conv R \<and>
  cr\<^sub>1 \<in> conv R \<and> sr \<in> seq R \<and> cr\<^sub>2 \<in> conv R \<and>
  get_target (fst p) = first cl\<^sub>1 \<and> last cl\<^sub>1 = first sl \<and> last sl = first cl\<^sub>2 \<and>
  get_target (snd p) = first cr\<^sub>1 \<and> last cr\<^sub>1 = first sr \<and> last sr = first cr\<^sub>2 \<and> 
  last cl\<^sub>2 = last cr\<^sub>2)"
(* new end *)

definition diamond_trs :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv \<Rightarrow> bool"
 where "diamond_trs R p jl jr = (ldc_trs R p (get_target (fst p),[]) jl (last jl,[]) (get_target (snd p),[]) jr (last jr,[]) 
\<and> length (snd jl) \<le> 1 \<and> length (snd jr) \<le> 1)"

definition ld2_trs :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv \<Rightarrow> bool"
 where "ld2_trs R p jl jr = (ldc_trs R p (get_target (fst p),[]) jl (last jl,[]) (get_target (snd p),[]) jr (last jr,[]) \<and> (length (snd jr) \<le> 1 \<and> (length (snd jl) \<le> 1 \<or> (\<not> linear_term (snd (get_rule (fst p)))))))"
 
type_synonym 'a relp = "'a rel \<times> 'a rel"

definition ELD_1 :: "'a relp \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
 where "ELD_1 r \<beta> \<alpha> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 = (set \<sigma>\<^sub>1 \<subseteq> ds (fst r) {\<beta>} \<and> length \<sigma>\<^sub>2 \<le> 1 \<and> set \<sigma>\<^sub>2 \<subseteq> ds (snd r) {\<alpha>} \<and> set \<sigma>\<^sub>3 \<subseteq> ds (fst r) {\<alpha>,\<beta>})"

(* new begin *)
definition eld_conv :: "(('f,'v,'a) labeling) \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak 
 \<Rightarrow> ('f,'v) conv \<Rightarrow>  ('f,'v) seq \<Rightarrow> ('f,'v) conv 
 \<Rightarrow> ('f,'v) conv \<Rightarrow>  ('f,'v) seq \<Rightarrow> ('f,'v) conv \<Rightarrow> bool"
where "eld_conv l r p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 = 
 (ELD_1 r (l (fst p)) (l (snd p)) (map l (snd cl\<^sub>1)) (map l (snd sl)) (map l (snd cl\<^sub>2)) \<and>
 ELD_1 r (l (snd p)) (l (fst p)) (map l (snd cr\<^sub>1)) (map l (snd sr)) (map l (snd cr\<^sub>2)))"

definition eldc :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak \<Rightarrow> bool"
where "eldc \<R> l r p = (\<exists> cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2. 
  ldc_trs \<R> p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 \<and> eld_conv l r p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2)"

definition fan :: "('f,'v) trs \<Rightarrow> ('f,'v) lpeak \<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv
\<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv \<Rightarrow> ('f,'v) conv \<Rightarrow> bool"
where "fan R p jl1 jl2 jl3 jr1 jr2 jr3 = (
  (\<forall> i < length (snd jl1). (get_source (fst p),get_source ((snd jl1)!i)) \<in> (rstep R)^*) \<and>
  (\<forall> i < length (snd jl2). (get_source (fst p),get_source ((snd jl2)!i)) \<in> (rstep R)^*) \<and>
  (\<forall> i < length (snd jl3). (get_source (fst p),get_source ((snd jl3)!i)) \<in> (rstep R)^*) \<and>
  (\<forall> i < length (snd jr1). (get_source (fst p),get_source ((snd jr1)!i)) \<in> (rstep R)^*) \<and>
  (\<forall> i < length (snd jr2). (get_source (fst p),get_source ((snd jr2)!i)) \<in> (rstep R)^*) \<and>
  (\<forall> i < length (snd jr3). (get_source (fst p),get_source ((snd jr3)!i)) \<in> (rstep R)^*)
)"

definition eld_fan :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak \<Rightarrow> bool"
where "eld_fan \<R> l r p = (\<exists> cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2. 
  ldc_trs \<R> p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 \<and> eld_conv l r p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 \<and> fan \<R> p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2)"

(* new end *)
(*
definition eld_seq :: "(('f,'v,'a) labeling) \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak 
 \<Rightarrow> ('f,'v) seq \<Rightarrow>  ('f,'v) seq \<Rightarrow> ('f,'v) seq
 \<Rightarrow> ('f,'v) seq \<Rightarrow>  ('f,'v) seq \<Rightarrow> ('f,'v) seq
\<Rightarrow> bool"
 where "eld_seq l r p jl1 jl2 jl3 jr1 jr2 jr3 = (\<exists> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3. (
 (map l (snd jl1) = \<sigma>1) \<and> map l (snd jl2) = \<sigma>2 \<and> map l (snd jl3) = \<sigma>3 \<and>
 (map l (snd jr1) = \<tau>1) \<and> map l (snd jr2) = \<tau>2 \<and> map l (snd jr3) = \<tau>3 \<and>
 (ELD_1 r (l (fst p)) (l (snd p)) \<sigma>1 \<sigma>2 \<sigma>3) \<and>
 (ELD_1 r (l (snd p)) (l (fst p)) \<tau>1 \<tau>2 \<tau>3)
))"

*)

definition eld :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak \<Rightarrow> bool"
where 
  "eld \<R> l r p = (\<exists> cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2. 
    ld_trs \<R> p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 \<and> eld_conv l r p cl\<^sub>1 sl cl\<^sub>2 cr\<^sub>1 sr cr\<^sub>2 )"

(* abstract labelings *)
definition is_labeling :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> bool"
where "is_labeling R l r = (\<forall> b1 b2 s rl1 t u rl2 v C \<rho> \<sigma>1 \<sigma>2 p1 p2 b.
  ((s, t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1 \<and> (u, v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<longrightarrow> (
  let st1 = (s, rl1, p1, \<sigma>1, b1, t) in
  let st2 = (u, rl2, p2, \<sigma>2, b2, v) in
    ((l st1, l st2) \<in> (fst r) \<longrightarrow> (l (step_close st1 C \<rho>), l (step_close st2 C \<rho>)) \<in> (fst r)) \<and>
    ((l st1, l st2) \<in> (snd r) \<longrightarrow> (l (step_close st1 C \<rho>), l (step_close st2 C \<rho>)) \<in> (snd r)))) \<and>
  l (s, rl1, p1, \<sigma>1, b, t) = l (s, rl1, p1, \<sigma>1, \<not> b, t))"

definition labels :: "('f,'v,'a) labeling \<Rightarrow> ('f,'v) conv \<Rightarrow> 'a set"
 where "labels l ss = set (map l (snd ss))"

definition weld_seq :: "('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak \<Rightarrow> ('f,'v) seq \<Rightarrow> ('f,'v) seq \<Rightarrow> bool"
where "weld_seq l r p jl jr = (
  (\<forall> a \<in> labels l jl. a \<in> ds (snd r) {l (snd p)}) \<and> 
  (\<forall> b \<in> labels l jr. b \<in> ds (snd r) {l (fst p)}))"

definition weld :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> ('f,'v) lpeak \<Rightarrow> bool"
 where "weld R l r p = (\<exists> jl jr. (ld2_trs R p jl jr \<and> weld_seq l r p jl jr))"

definition compatible :: "('f,'v :: infinite) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> bool"
where "compatible R l r = (is_labeling R l r \<and> 
  (\<forall> p. variable_peak R p \<or> parallel_peak R p \<longrightarrow> eldc R l r p))"
 
definition weakly_compatible :: "('f,'v :: infinite) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a relp \<Rightarrow> bool"
where "weakly_compatible R l r = (is_labeling R l r \<and> 
  (left_linear_trs R \<longrightarrow> (\<forall> p. variable_peak R p \<or> parallel_peak R p \<longrightarrow> weld R l r p)))"

lemma linear_and_weld_imp_eld:
  assumes "linear_trs R" and "weld R l r p"
  shows "eldc R l r p"
proof - 
  from assms obtain jl jr where ld2_trs: "ld2_trs R p jl jr" and weld_seq: "weld_seq l r p jl jr"
    unfolding weld_def by auto
  then obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u where
    p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))" and lp: "p \<in> local_peaks R" 
    unfolding ld2_trs_def ldc_trs_def local_peaks_def by fast
   obtain jl1 where jl1_eq: "jl1 = (get_target (fst p),[])" and "jl1 \<in> conv R" using conv.simps by fastforce
   obtain jl3 where jl3_eq: "jl3 = (last jl,[])" and "jl3 \<in> conv R" using conv.simps by fastforce
   obtain jr1 where jr1_eq: "jr1 = (get_target (snd p),[])" and "jr1 \<in> conv R" using conv.simps by fastforce
   obtain jr3 where jr3_eq: "jr3 = (last jr,[])" and "jr3 \<in> conv R" using conv.simps by fastforce
  then have ld: "ldc_trs R p jl1 jl jl3 jr1 jr jr3" using jl1_eq jl3_eq jr1_eq jr3_eq ld2_trs unfolding ld2_trs_def by auto
  from lp have "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" unfolding local_peaks_def p_dec by auto 
  then have "rl1 \<in> R" unfolding rstep_r_p_s_def by (auto simp: Let_def)
  then have "linear_term (snd (get_rule (fst p)))" unfolding p_dec get_rule_def apply auto using assms unfolding linear_trs_def by (metis assms(1) linear_trsE prod.collapse)
  then have jl: "length (snd jl) \<le> 1"  using ld2_trs unfolding weld_def ldc_trs_def ld2_trs_def weld_seq_def eld_conv_def linear_trs_def  using assms(1) by auto
  have jr: "length (snd jr) \<le> 1" using ld2_trs unfolding ld2_trs_def by auto
  have "ELD_1 r (l (fst p)) (l (snd p)) [] (map l (snd jl))  []" using weld_seq jl unfolding ELD_1_def ds_def apply auto unfolding weld_seq_def labels_def ds_def by auto 
  moreover have "ELD_1 r (l (snd p)) (l (fst p)) [] (map l (snd jr))  []" using weld_seq jr unfolding ELD_1_def ds_def apply auto unfolding weld_seq_def labels_def ds_def by auto
  ultimately have "eld_conv l r p jl1 jl jl3 jr1 jr jr3" unfolding jl1_eq jl3_eq jr1_eq jr3_eq eld_conv_def by auto
  then have "eld_conv l r p jl1 jl jl3 jr1 jr jr3" and "ldc_trs R p jl1 jl jl3 jr1 jr jr3" using ld by auto
  then have "\<exists> jl1 jl2 jl3 jr1 jr2 jr3. ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3 \<and> eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3" by blast
  then show ?thesis unfolding eldc_def by auto
qed

lemma linear_and_weakly_compatible_is_compatible:
 assumes "linear_trs R" and "weakly_compatible R l r"
 shows "compatible R l r" proof -
  from assms have ll: "left_linear_trs R" unfolding linear_trs_def left_linear_trs_def by auto
  have 1: "is_labeling R l r" using assms unfolding weakly_compatible_def by auto
  {
    fix p assume A: "variable_peak R p \<or> parallel_peak R p" 
    then have " weld R l r p" using assms(2) ll unfolding weakly_compatible_def by metis 
    then have "eldc R l r p" using linear_and_weld_imp_eld[OF assms(1)] by fast
  }
  then show ?thesis using 1 unfolding compatible_def by auto
qed
  
lemma ldc_trs_closed:
  fixes C \<tau>
  assumes "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
  shows "ldc_trs R ((step_close (fst p) C \<tau>),(step_close (snd p) C \<tau>)) 
 (conv_close jl1 C \<tau>) (seq_close jl2 C \<tau>) (conv_close jl3 C \<tau>)
 (conv_close jr1 C \<tau>) (seq_close jr2 C \<tau>) (conv_close jr3 C \<tau>) " (is "ldc_trs R ?P _ _ _ _ _ _") 
proof -
  from assms obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u 
  where p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))" and "p \<in> local_peaks R" 
    unfolding ldc_trs_def local_peaks_def by fast
  then have l:"(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" and r:"(s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2" unfolding local_peaks_def by auto
  from l have P1: "(C\<langle>s\<cdot>\<tau>\<rangle>,C\<langle>t\<cdot>\<tau>\<rangle>) \<in> rstep_r_p_s R rl1 (hole_pos C@ p1) (\<sigma>1\<circ>\<^sub>s \<tau>)" 
    using rstep_r_p_s_ctxt_closed2 rstep_r_p_s_subst_closed by metis
  from r have P2: "(C\<langle>s\<cdot>\<tau>\<rangle>,C\<langle>u\<cdot>\<tau>\<rangle>) \<in> rstep_r_p_s R rl2 (hole_pos C@ p2) (\<sigma>2\<circ>\<^sub>s \<tau>)" 
    using rstep_r_p_s_ctxt_closed2 rstep_r_p_s_subst_closed by metis
  from P1 P2 have P: "?P \<in> local_peaks R" unfolding local_peaks_def p_dec step_close.simps fst_conv snd_conv Let_def by fast
  from assms have jl1:"jl1 \<in> conv R" and jl2:"jl2 \<in> seq R" and jl3:"jl3 \<in> conv R"
    and  jr1:"jr1 \<in> conv R" and jr2:"jr2 \<in> seq R" and jr3:"jr3 \<in> conv R"
    and l: "get_target (fst p) = first jl1" and r: "get_target (snd p) = first jr1" and b: "last jl3 = last jr3" unfolding ldc_trs_def by auto
  have JL1: "conv_close jl1 C \<tau> \<in> conv R" using conv_super_closed1[OF jl1] by fast
  have JL2: "seq_close jl2 C \<tau> \<in> seq R" using seq_super_closed1[OF jl2] by fast
  have JL3: "conv_close jl3 C \<tau> \<in> conv R" using conv_super_closed1[OF jl3] by fast
  have JR1: "conv_close jr1 C \<tau> \<in> conv R" using conv_super_closed1[OF jr1] by fast
  have JR2: "seq_close jr2 C \<tau> \<in> seq R" using seq_super_closed1[OF jr2] by fast
  have JR3: "conv_close jr3 C \<tau> \<in> conv R" using conv_super_closed1[OF jr3] by fast
  have L1: "get_target (step_close (fst (p)) C \<tau>) = first (conv_close jl1 C \<tau>)" 
    using step_super_closed1 l conv_super_closed1[OF jl1] by metis
  have L2: "last (conv_close jl1 C \<tau>) = first (seq_close jl2 C \<tau>)" 
    using l conv_super_closed1[OF jl1] seq_super_closed1[OF jl2] by (metis assms ldc_trs_def)
  have L3: "last (seq_close jl2 C \<tau>) = first (conv_close jl3 C \<tau>)" 
    using l seq_super_closed1[OF jl2] conv_super_closed1[OF jl3] by (metis assms ldc_trs_def)
  have R1: "get_target (step_close (snd (p)) C \<tau>) = first (conv_close jr1 C \<tau>)" 
    using step_super_closed1 r conv_super_closed1[OF jr1] by metis 
  have R2: "last (conv_close jr1 C \<tau>) = first (seq_close jr2 C \<tau>)" 
    using l conv_super_closed1[OF jr1] seq_super_closed1[OF jr2] by (metis assms ldc_trs_def)
  have R3: "last (seq_close jr2 C \<tau>) = first (conv_close jr3 C \<tau>)" 
    using l seq_super_closed1[OF jr2] conv_super_closed1[OF jr3] by (metis assms ldc_trs_def)
  have "last (conv_close jl3 C \<tau>) = last (conv_close jr3 C \<tau>)" using conv_super_closed1 jl3 jr3 b by metis 
  then show ?thesis using P JL1 JL2 JL3 JR1 JR2 JR3 L1 L2 L3 R1 R2 R3 unfolding ldc_trs_def by auto
qed

lemma el_closed:
  fixes C \<tau>
  assumes lab: "is_labeling R l r"
  and s1: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1"
  and ss: "ss \<in> seq R"
  and dec: "\<forall> b \<in> set (map l (snd ss)). (b,l (s,rl1,p1,\<sigma>1,True,t)) \<in> (snd r)"
  shows "\<forall> b \<in> set (map l (snd (seq_close ss C \<tau>))). (b,l (step_close (s,rl1,p1,\<sigma>1,True,t) C \<tau>)) \<in> (snd r)" 
using ss dec
proof (induct "snd ss" arbitrary:"ss")
 case Nil then show ?case by auto
next
 case (Cons step steps) 
 from Cons(2) obtain u where ss_dec: "ss = (u,step # steps)" by (cases ss, auto)
 with Cons(3) obtain rl2 p2 \<sigma>2 v where step_dec: "step = (u,rl2,p2,\<sigma>2,True,v)" and s2: "(u,v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2" 
   using seq.cases by blast
 have "(l step, l (s,rl1,p1,\<sigma>1,True,t)) \<in> (snd r)" using Cons unfolding ss_dec step_dec by auto
 then have step_close: "(l (step_close step C \<tau>), l (step_close (s,rl1,p1,\<sigma>1,True,t) C \<tau>)) \<in> snd r" 
   using lab s1 s2 unfolding is_labeling_def step_dec Let_def by blast
 then have vs: "(v,steps) \<in> seq R" using Cons unfolding ss_dec step_dec using seq_chop_first by fast
 then have "\<forall>b\<in>set (map l (snd (v,steps))). (b, l (s, rl1, p1, \<sigma>1, True, t)) \<in> snd r" using Cons unfolding ss_dec step_dec by auto
 then have "\<forall> b \<in> set (map l (snd (seq_close (v,steps) C \<tau>))). (b,l (step_close (s,rl1,p1,\<sigma>1,True,t) C \<tau>)) \<in> snd r" 
   using Cons(1)[OF _ vs] Cons by auto
 then show ?case using step_close unfolding ss_dec by auto
qed

lemma eseq_super_closed2:
fixes C \<sigma>
assumes step': "(s',t') \<in> rstep_r_p_s R rl' p' \<rho>"
and lab: "is_labeling R l r"
and seq: "ss \<in> seq R"
and dec:"\<forall> b \<in> set (map l (snd ss)). (b,l (s',rl',p',\<rho>,True,t')) \<in> (fst r)"
shows "(\<forall> b \<in> set (map l (snd (seq_close ss C \<sigma>))). (b,l (step_close (s',rl',p',\<rho>,True,t') C \<sigma>)) \<in> (fst r))" 
 using seq dec proof (induct "snd ss" arbitrary: ss)
 case Nil then obtain s where ss_dec: "ss = (s,[])" using surjective_pairing by metis 
 then show ?case using seq.intros unfolding ss_dec by auto
next
 case (Cons step ts)
 from Cons(2) obtain s where ss_dec: "ss=(s,step#ts)" by (cases ss, auto)
 with Cons(3) obtain rl p \<tau> t where step_dec: "step=(s,rl,p,\<tau>,True,t)"  using seq.cases by blast
 then have step: "(s,t) \<in> rstep_r_p_s R rl p \<tau>" and i:"(t,ts) \<in> seq R" (is "?ts \<in> _") using Cons(3) seq.cases unfolding ss_dec step_dec by auto
 have j:"\<forall>b \<in> set (map l (snd ?ts)). (b,l (s',rl',p',\<rho>,True,t')) \<in> fst r" using Cons unfolding ss_dec snd_conv by auto 
 from Cons(1)[OF _ i j] have
 ih: "(\<forall> b \<in> set (map l (snd (seq_close ?ts C \<sigma>))). (b,l (C\<langle>s'\<cdot>\<sigma>\<rangle>,rl',hole_pos C@p',\<rho> \<circ>\<^sub>s \<sigma>,True,C\<langle>t'\<cdot>\<sigma>\<rangle>)) \<in> fst r)" by auto
 have C_label: "(l (s,rl,p,\<tau>,True,t),l (s',rl',p',\<rho>,True,t')) \<in> fst r" using Cons unfolding ss_dec step_dec snd_conv  by auto
 have C_label2: "(l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),l (step_close (s',rl',p',\<rho>,True,t') C \<sigma>)) \<in> fst r" 
  using step step' C_label lab dec  unfolding is_labeling_def Let_def by fast
 then have C_labels: "(\<forall>b\<in>set (map l (snd (seq_close ss C \<sigma>))). (b, l (C\<langle>s' \<cdot> \<sigma>\<rangle>, rl', hole_pos C @ p', \<rho> \<circ>\<^sub>s \<sigma>,True, C\<langle>t' \<cdot> \<sigma>\<rangle>)) \<in> fst r)" 
  using ih(1) unfolding ss_dec step_dec seq_close.simps snd_conv step_close.simps Let_def by auto  
 show ?case using C_labels by auto
qed

lemma eseq_super_closed3:
fixes C \<sigma>
assumes step': "(s',t') \<in> rstep_r_p_s R rl' p' \<rho>"
and step'': "(s'',t'') \<in> rstep_r_p_s R rl'' p'' \<rho>'"
and lab: "is_labeling R l r"
and seq: "ss \<in> seq R"
and dec:"\<forall> b \<in> set (map l (snd ss)). ((b,l (s',rl',p',\<rho>,True,t')) \<in> fst r \<or> (b,l (s'',rl'',p'',\<rho>',True,t'')) \<in> fst r)"
shows "(\<forall> b \<in> set (map l (snd (seq_close ss C \<sigma>))). ((b,l (step_close (s',rl',p',\<rho>,True,t') C \<sigma>)) \<in> fst r) \<or> (b,l (step_close (s'',rl'',p'',\<rho>',True,t'') C \<sigma>)) \<in> fst r)"
 using seq dec proof (induct "snd ss" arbitrary: ss)
 case Nil then obtain s where ss_dec: "ss = (s,[])" using surjective_pairing by metis 
 then show ?case using seq.intros unfolding ss_dec by auto
next
 case (Cons step ts)
 from Cons(2) obtain s where ss_dec: "ss=(s,step#ts)" by (cases ss, auto)
 with Cons(3) obtain rl p \<tau> t where step_dec: "step=(s,rl,p,\<tau>,True,t)"
   using seq.cases by blast
 then have step: "(s,t) \<in> rstep_r_p_s R rl p \<tau>"  and i:"(t,ts) \<in> seq R" (is "?ts \<in> _") using Cons(3) seq.cases unfolding step_dec ss_dec by auto
 have j:"\<forall>b \<in> set (map l (snd ?ts)). ((b, l (s',rl',p',\<rho>,True,t')) \<in> fst r \<or> (b,l (s'',rl'',p'',\<rho>',True,t'')) \<in> fst r)" using Cons unfolding ss_dec snd_conv by auto 
 from Cons(1)[OF _ i j] have
 ih: "(\<forall> b \<in> set (map l (snd (seq_close ?ts C \<sigma>))). ((b,l (step_close (s',rl',p',\<rho>,True,t') C \<sigma>)) \<in> fst r) \<or> (b,l (step_close (s'',rl'',p'',\<rho>',True,t'') C \<sigma>)) \<in> fst r)" (is "\<forall> b \<in> _. (b,?a') \<in> ?r \<or> (b,?a'') \<in> ?r") by auto
 have C_step: "(C\<langle>s\<cdot>\<sigma>\<rangle>,C\<langle>t\<cdot>\<sigma>\<rangle>) \<in> rstep_r_p_s R rl (hole_pos C@p) (\<tau>\<circ>\<^sub>s \<sigma>)" using rstep_r_p_s_ctxt_closed2[OF rstep_r_p_s_subst_closed[OF step]] by auto 
 have C_label: "(l (s,rl,p,\<tau>,True,t),l (s',rl',p',\<rho>,True,t')) \<in> fst r \<or> (l (s,rl,p,\<tau>,True,t),l (s'',rl'',p'',\<rho>',True,t'')) \<in> fst r" using Cons(4) unfolding ss_dec step_dec snd_conv by auto
 have C_label2: "(l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),?a') \<in> fst r \<or> (l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),?a'') \<in> fst r" (is "(?a,_) \<in> fst r \<or> _") proof(cases "(l (s,rl,p,\<tau>,True,t),l (s',rl',p',\<rho>,True,t')) \<in> ?r")
  case True then show ?thesis using step step' lab dec unfolding is_labeling_def Let_def by fast 
  next
  case False then have l: "(l (s,rl,p,\<tau>,True,t),l (s'',rl'',p'',\<rho>',True,t'')) \<in> fst r" using C_label by auto
  then show ?thesis using step step'' C_step rstep_r_p_s_ctxt_closed2[OF rstep_r_p_s_subst_closed[OF step''],of "C" "\<sigma>"] l lab dec unfolding is_labeling_def Let_def by fast
 qed
 then have C_labels: "(\<forall>b\<in>set (map l (snd (seq_close ss C \<sigma>))). ((b,?a') \<in> fst r \<or> (b,?a'') \<in> fst r))" 
  using ih unfolding ss_dec step_dec seq_close.simps snd_conv step_close.simps Let_def by auto  
 show ?case using C_labels by auto
 qed

(* new begin 
lemma el_conv_closed: 
  fixes C \<tau>
  assumes lab: "is_labeling R l r"
  and s1: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1"
  and ss: "ss \<in> conv R"
  and dec: "\<forall> b \<in> set (map l (snd ss)). (b,l (s,rl1,p1,\<sigma>1,True,t)) \<in> (snd r)"
  shows "\<forall> b \<in> set (map l (snd (conv_close ss C \<tau>))). (b,l (step_close (s,rl1,p1,\<sigma>1,True,t) C \<tau>)) \<in> (snd r)" 
using ss dec
proof (induct "snd ss" arbitrary:"ss")
 case Nil thus ?case by auto
next
 case (Cons step steps) 
 from Cons(2) obtain u where ss_dec: "ss = (u,step # steps)" by (cases ss, auto)
 with Cons(3) obtain rl2 p2 \<sigma>2 v where step_dec: "step = (u,rl2,p2,\<sigma>2,v)" 
  and s2: "(u,v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<or> (v,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2" 
   using conv.cases by blast
 have "(l step, l (s,rl1,p1,\<sigma>1,t)) \<in> (snd r)" using Cons unfolding ss_dec step_dec by auto
 hence step_close: "(l (step_close step C \<tau>), l (step_close (s,rl1,p1,\<sigma>1,t) C \<tau>)) \<in> snd r" 
   using lab s1 s2 unfolding is_labeling_def step_dec Let_def by blast
 hence vs: "(v,steps) \<in> conv R" using Cons unfolding ss_dec step_dec using conv_chop_first by fast
 hence "\<forall>b\<in>set (map l (snd (v,steps))). (b, l (s, rl1, p1, \<sigma>1, t)) \<in> snd r" using Cons unfolding ss_dec step_dec by auto
 hence "\<forall> b \<in> set (map l (snd (conv_close (v,steps) C \<tau>))). (b,l (step_close (s,rl1,p1,\<sigma>1,t) C \<tau>)) \<in> snd r" 
   using Cons(1)[OF _ vs] Cons by auto
 thus ?case using step_close unfolding ss_dec by auto
qed
*)

lemma conv_imp_conv: 
  assumes "ss \<in> conv R" 
  and "set (map l (snd ss)) \<subseteq> ds r S" 
  and "is_labeling R l (r,r')"
  defines "rel \<equiv> \<lambda> c. {(s,t). \<exists> r p \<sigma> b. (s,t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s,r,p,\<sigma>,True,t) = c}"
  shows "(first ss, last ss) \<in> ((\<Union>c \<in> ds r S. (rel c))\<^sup>\<leftrightarrow>)^*"
proof -
  from assms obtain t ts where ss_dec: "ss = (t,ts)" by (metis surjective_pairing)
  from assms(1,2) show ?thesis unfolding ss_dec
  proof (induct)
    case (2 s t rl p \<sigma> ts)
    then have "l (s, rl, p, \<sigma>, True, t) \<in> ds r S" by auto
    then have "(s, t) \<in> \<Union> (rel ` ds r S)" using 2 unfolding rel_def by blast
    then have "(s, t) \<in> ((\<Union>a\<in>ds r S. rel a)\<^sup>\<leftrightarrow>)\<^sup>*" by blast
    with 2 show ?case by (auto simp: get_target_def)
  next
    case (3 s t rl p \<sigma> ts)
    then have "l (s, rl, p, \<sigma>, False, t) \<in> ds r S" by auto
    moreover have "l (s, rl, p, \<sigma>, False, t) = l (s, rl, p, \<sigma>, True, t)"
      using assms(3)[unfolded is_labeling_def, rule_format, of s t rl p \<sigma>, where b = False] by simp  
    ultimately have "l (s, rl, p, \<sigma>, True, t) \<in> ds r S" by auto
    then have "(s, t) \<in> \<Union> (rel ` ds r S)" using 3(1) unfolding rel_def by blast
    then have "(t, s) \<in> ((\<Union>a\<in>ds r S. rel a)\<^sup>\<leftrightarrow>)\<^sup>*" by blast
    with 3 show ?case by (auto simp: get_target_def)
  qed auto
qed

lemma econv_super_closed2:
  assumes step': "(s',t') \<in> rstep_r_p_s R rl' p' \<rho>"
  and lab: "is_labeling R l r"
  and conv: "ss \<in> conv R"
  and dec:"\<forall> b \<in> set (map l (snd ss)). (b, l (s',rl',p',\<rho>, b', t')) \<in> (fst r)"
  shows "\<forall> b \<in> set (map l (snd (conv_close ss C \<sigma>))). (b, l (step_close (s',rl',p',\<rho>, b', t') C \<sigma>)) \<in> (fst r)"
proof -
  obtain s steps where ss:"ss = (s, steps)" by (cases ss, auto)
  from conv[unfolded ss] dec[unfolded ss]
  have "\<forall> b \<in> set (map l (snd (conv_close (s, steps) C \<sigma>))). (b, l (step_close (s',rl',p',\<rho>, b', t') C \<sigma>)) \<in> (fst r)"
  proof (induct)
    case (2 s t rl p \<tau> ts)
    have "\<forall>b\<in>set (map l (snd (t, ts))). (b, l (s', rl', p', \<rho>, b', t')) \<in> fst r" using 2(4) by auto
    from 2(3)[OF this] have ih:"\<forall>b\<in>set (map l (snd (conv_close (t, ts) C \<sigma>))). (b, l (step_close (s', rl', p', \<rho>, b', t') C \<sigma>)) \<in> fst r" .
    have C_label: "(l (s,rl,p,\<tau>,True,t),l (s',rl',p',\<rho>,b',t')) \<in> fst r" using 2(4) unfolding snd_conv by auto
    have C_label2: "(l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r" 
      using 2(1) step' C_label lab[unfolded is_labeling_def Let_def, rule_format, of s t rl p] by blast
    then show ?case  using ih(1) unfolding conv_close.simps snd_conv step_close.simps Let_def by auto
  next
    case (3 t s rl p \<tau> ts)
    have "\<forall>b\<in>set (map l (snd (t, ts))). (b, l (s', rl', p', \<rho>, b', t')) \<in> fst r" using 3(4) by auto
    from 3(3)[OF this] have ih:"\<forall>b\<in>set (map l (snd (conv_close (t, ts) C \<sigma>))). (b, l (step_close (s', rl', p', \<rho>, b', t') C \<sigma>)) \<in> fst r" .
    have C_label: "(l (t,rl,p,\<tau>,False,s), l (s',rl',p',\<rho>,b',t')) \<in> fst r" using 3(4) unfolding snd_conv by auto
    then have C_label2: "(l (step_close (t,rl,p,\<tau>,False,s) C \<sigma>),l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r" 
      using 3(1) step' C_label lab[unfolded is_labeling_def Let_def, rule_format, of t s rl p \<tau> s' t' rl' p' \<rho>] by blast
    then show ?case  using ih(1) unfolding conv_close.simps snd_conv step_close.simps Let_def by auto
  qed auto
  with ss show ?thesis by auto
qed

lemma econv_super_closed3:
  fixes C \<sigma>
  assumes step': "(s',t') \<in> rstep_r_p_s R rl' p' \<rho>"
  and step'': "(s'',t'') \<in> rstep_r_p_s R rl'' p'' \<rho>'"
  and lab: "is_labeling R l r"
  and conv: "ss \<in> conv R"
  and dec:"\<forall> b \<in> set (map l (snd ss)). ((b,l (s',rl',p',\<rho>,b',t')) \<in> fst r \<or> (b,l (s'',rl'',p'',\<rho>',b'',t'')) \<in> fst r)"
  shows "\<forall> b \<in> set (map l (snd (conv_close ss C \<sigma>))). ((b,l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r) 
    \<or> (b,l (step_close (s'',rl'',p'',\<rho>',b'',t'') C \<sigma>)) \<in> fst r"
proof -
  obtain s steps where ss:"ss = (s, steps)" by (cases ss, auto)
  from conv[unfolded ss] dec[unfolded ss]
  have "\<forall> b \<in> set (map l (snd (conv_close (s, steps) C \<sigma>))). ((b,l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r) 
    \<or> (b,l (step_close (s'',rl'',p'',\<rho>',b'',t'') C \<sigma>)) \<in> fst r"
  proof (induct)
    case (2 s t rl p \<tau> ts)
    have "\<forall>b\<in>set (map l (snd (t, ts))). (b, l (s', rl', p', \<rho>, b', t')) \<in> fst r \<or>
      (b, l (s'', rl'', p'', \<rho>', b'', t'')) \<in> fst r" using 2(4) by auto
    from 2(3)[OF this] have ih:"\<forall>b\<in>set (map l (snd (conv_close (t, ts) C \<sigma>))).
     (b, l (step_close (s', rl', p', \<rho>, b', t') C \<sigma>)) \<in> fst r \<or>
     (b, l (step_close (s'', rl'', p'', \<rho>', b'', t'') C \<sigma>)) \<in> fst r" .
    have C_label: "(l (s,rl,p,\<tau>,True,t),l (s',rl',p',\<rho>,b',t')) \<in> fst r \<or>
      (l (s,rl,p,\<tau>,True,t),l (s'',rl'',p'',\<rho>',b'',t'')) \<in> fst r" using 2(4) unfolding snd_conv by auto
    have C_label2: "(l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r \<or>
      (l (step_close (s,rl,p,\<tau>,True,t) C \<sigma>),l (step_close (s'',rl'',p'',\<rho>',b'',t'') C \<sigma>)) \<in> fst r" 
      using 2(1) step' step'' C_label lab[unfolded is_labeling_def Let_def, rule_format, of s t rl p] by blast
    then show ?case  using ih(1) unfolding conv_close.simps snd_conv step_close.simps Let_def by auto
  next
    case (3 t s rl p \<tau> ts)
    have "\<forall>b\<in>set (map l (snd (t, ts))). (b, l (s', rl', p', \<rho>, b', t')) \<in> fst r \<or>
      (b, l (s'', rl'', p'', \<rho>', b'', t'')) \<in> fst r" using 3(4) by auto
    from 3(3)[OF this] have ih:"\<forall>b\<in>set (map l (snd (conv_close (t, ts) C \<sigma>))).
     (b, l (step_close (s', rl', p', \<rho>, b', t') C \<sigma>)) \<in> fst r \<or>
     (b, l (step_close (s'', rl'', p'', \<rho>', b'', t'') C \<sigma>)) \<in> fst r" .
    have C_label: "(l (t,rl,p,\<tau>,False,s), l (s',rl',p',\<rho>,b',t')) \<in> fst r \<or>
      (l (t,rl,p,\<tau>,False,s), l (s'',rl'',p'',\<rho>',b'',t'')) \<in> fst r" using 3(4) unfolding snd_conv by auto
    then have C_label2: "(l (step_close (t,rl,p,\<tau>,False,s) C \<sigma>),l (step_close (s',rl',p',\<rho>,b',t') C \<sigma>)) \<in> fst r \<or>
      (l (step_close (t,rl,p,\<tau>,False,s) C \<sigma>),l (step_close (s'',rl'',p'',\<rho>',b'',t'') C \<sigma>)) \<in> fst r" 
      using 3(1) step' step'' C_label lab[unfolded is_labeling_def Let_def, rule_format, of t s rl p \<tau>] by blast
    then show ?case  using ih(1) unfolding conv_close.simps snd_conv step_close.simps Let_def by auto
  qed auto
  with ss show ?thesis by auto
qed

lemma conv_concat_conv_close: 
  shows "conv_close (conv_concat ts us) C \<tau> = conv_concat (conv_close ts C \<tau>) (conv_close us C \<tau>)"
proof -
  obtain t tq u uq where ts_dec: "ts = (t,tq)" and us_dec: "us = (u,uq)"
    by (cases ts, cases us, auto)
  then show ?thesis unfolding conv_concat_def by auto
qed

lemma conv_concat_labels:
  shows "map l (snd (conv_concat ts us)) = (map l (snd ts)) @ (map l (snd us))"
proof -
  obtain t tq u uq where ts_dec: "ts = (t,tq)" and us_dec: "us = (u,uq)"
    by (cases ts, cases us, auto)
  show ?thesis unfolding conv_concat_def by auto
qed
(* new end *)

lemma eld_conv_closed: 
  fixes C \<tau> 
  assumes d: "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
  and "eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3" 
  and lab: "is_labeling R l r"
  shows "eld_conv l r ((step_close (fst p) C \<tau>),(step_close (snd p) C \<tau>)) 
 (conv_close jl1 C \<tau>)  (seq_close jl2 C \<tau>)  (conv_close jl3 C \<tau>)
 (conv_close jr1 C \<tau>)  (seq_close jr2 C \<tau>)  (conv_close jr3 C \<tau>)" 
    (is "eld_conv _ _ ?P ?JL1 ?JL2 ?JL3 ?JR1 ?JR2 ?JR3") 
proof -
  {
    fix s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u l1 l2 l3 jl1 jl2 jl3 b1 b2
    let ?a = "l (s,rl1,p1,\<sigma>1,True,t)"
    let ?a' = "l (s,rl2,p2,\<sigma>2,True,u)"
    let ?A = "l (step_close (s, rl1, p1, \<sigma>1, True, t) C \<tau>)"
    let ?A' = "l (step_close (s, rl2, p2, \<sigma>2, True, u) C \<tau>)"
    assume
      lstep: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" and
      lstep': "(s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2" and
      ELD_l: "ELD_1 r ?a ?a' (map l (snd jl1)) (map l (snd jl2)) (map l (snd jl3))" and
      L1:"jl1 \<in> conv R" and L2: "jl2 \<in> seq R" and  L3: "jl3 \<in> conv R"
    have "length (snd jl2) \<le> 1" using ELD_l unfolding ELD_1_def by auto
    then have JL: "length (snd (seq_close jl2 C \<tau>)) \<le> 1" using seq_close_length by auto
    from ELD_l have
      ELD1: "\<forall> b \<in> set (map l (snd jl1)). (b, ?a) \<in> fst r" and
      ELD2: "\<forall> b \<in> set (map l (snd jl2)). (b, ?a') \<in> snd r" and
      ELD3: "\<forall> b \<in> set (map l (snd jl3)). ((b, ?a) \<in> fst r \<or> (b, ?a') \<in> fst r)"
      unfolding ELD_1_def ds_def by auto
    let ?sc = "\<lambda>L. conv_close L C \<tau>"
    have L1:"\<forall> b \<in> set (map l (snd (?sc jl1))). (b, ?A) \<in> fst r"
      using econv_super_closed2[OF lstep lab L1] ELD1 unfolding fst_conv by auto
    have  L2:"\<forall> b \<in> set (map l (snd (?sc jl2))). (b,?A') \<in> snd r"
      using el_closed[OF lab _ L2] lstep' ELD2 unfolding snd_conv by auto
    have  L3:"\<forall> b \<in> set (map l (snd (?sc jl3))). ((b, ?A) \<in> fst r \<or> (b, ?A') \<in> fst r)"
      using econv_super_closed3[OF lstep lstep' lab L3] ELD3 unfolding fst_conv by simp
    then have L: "ELD_1 r ?A ?A' (map l (snd (?sc jl1))) (map l (snd (?sc jl2))) (map l (snd (?sc jl3)))"
      unfolding ELD_1_def ds_def using L1 L2 L3 JL by auto
    with L have " ELD_1 r ?A ?A' (map l (snd (?sc jl1))) (map l (snd (?sc jl2))) (map l (snd (?sc jl3)))" by auto
  } note * = this
  from assms have pl:"p \<in> local_peaks R" unfolding ldc_trs_def by auto
  then obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u where p: "p = ((s, rl1, p1, \<sigma>1, True, t),(s, rl2, p2, \<sigma>2, True, u))"
    unfolding local_peaks_def by blast
  have lstep: "(s, t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" using pl unfolding local_peaks_def p by auto
  have lstep': "(s, u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2" using pl unfolding local_peaks_def p by auto
  let ?a = "l (s, rl1, p1, \<sigma>1, True, t)"
  let ?a' = "l (s, rl2, p2, \<sigma>2, True, u)"
  from assms obtain l1 l2 l3 where jl1_dec2: "map l (snd jl1) = l1" and jl2_dec2: "map l (snd jl2) = l2" 
   and jl3_dec2: "map l (snd jl3) = l3" and LD_l: "ELD_1 r ?a ?a' (map l (snd jl1)) (map l (snd jl2)) (map l (snd jl3))"
    unfolding eld_conv_def unfolding p by auto
  have jl1:"jl1 \<in> conv R" and jl2: "jl2 \<in> seq R" and jl3: "jl3 \<in> conv R" using d unfolding ldc_trs_def by auto
  from assms obtain r1 r2 r3 where jr1_dec2: "map l (snd jr1) = r1" and jr2_dec2: "map l (snd jr2) = r2" 
   and jr3_dec2: "map l (snd jr3) = r3" and LD_r: "ELD_1 r ?a' ?a (map l (snd jr1)) (map l (snd jr2)) (map l (snd jr3))"
    unfolding eld_conv_def unfolding p by auto
  have jr1:"jr1 \<in> conv R" and jr2: "jr2 \<in> seq R" and jr3: "jr3 \<in> conv R" using d unfolding ldc_trs_def by auto
  from *[OF lstep lstep' LD_l jl1 jl2 jl3] *[OF lstep' lstep LD_r jr1 jr2 jr3] show ?thesis
  unfolding eld_conv_def p by auto
qed

lemma eld_closed:
  fixes C \<tau>
  assumes "eldc R l r p"
  and lab: "is_labeling R l r"
  shows "eldc R l r (step_close (fst p) C \<tau>,step_close (snd p) C \<tau>)" 
proof -
  from assms(1) obtain jl1 jl2 jl3 jr1 jr2 jr3 where d: "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
 and D: "eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3" unfolding eldc_def by auto
  have C_d:"ldc_trs R (step_close (fst p) C \<tau>,step_close (snd p) C \<tau>) 
  (conv_close jl1 C \<tau>) (seq_close jl2 C \<tau>) (conv_close jl3 C \<tau>)
  (conv_close jr1 C \<tau>) (seq_close jr2 C \<tau>) (conv_close jr3 C \<tau>)" 
    (is "ldc_trs R ?p ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3") using ldc_trs_closed[OF d] by fast 
  have "eld_conv l r ?p ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3" using eld_conv_closed[OF d D lab] by auto
  then show ?thesis using C_d unfolding eldc_def by fast
qed

lemma critical:
  assumes "function_peak R p"
  and cp:"\<forall> (b, p) \<in> critical_peaks ren R. eldc R l r p"
  and lab: "is_labeling R l r"
  shows "eldc R l r p" 
proof -
  from function_peak_inst_of_critical_peak[OF assms(1)] obtain C \<delta> b cp where
    "(b, cp) \<in> critical_peaks ren R" and
    inst: "p = (step_close (fst cp) C \<delta>, step_close (snd cp) C \<delta>)"
    by blast
  then have eldc: "eldc R l r cp" using cp by auto
  then show ?thesis using eld_closed[OF eldc] trans eldc lab inst by fast
qed

lemma left:
  assumes "variable_peak R p \<or> function_peak R p"
  and cps: "\<forall> (b, p) \<in> critical_peaks ren R. eldc R l r p"
  and lab: "compatible R l r"
  shows "eldc R l r p" 
proof (cases "variable_peak R p")
  case True then show ?thesis using lab unfolding compatible_def by fast 
next
  case False then have "function_peak R p" using assms by auto
  then show ?thesis using critical lab cps unfolding eldc_def compatible_def by fast
qed

(*
lemma mirror_eld_seq: assumes "eld_seq l r (fst p, snd p) jl jr"
shows "eld_seq l r (snd p, fst p) jr jl" proof -
 from assms obtain \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3 where "map l (snd jl) = \<sigma>1 @ \<sigma>2 @ \<sigma>3 \<and> map l (snd jr) = \<tau>1 @ \<tau>2 @ \<tau>3 \<and> ELD_1 r (l (fst (fst p, snd p))) (l (snd (fst p, snd p))) \<sigma>1 \<sigma>2 \<sigma>3 \<and> ELD_1 r (l (snd (fst p, snd p))) (l (fst (fst p, snd p))) \<tau>1 \<tau>2 \<tau>3"
 unfolding eld_seq_def by auto
 hence "map l (snd jr) = \<tau>1 @ \<tau>2 @ \<tau>3 \<and> map l (snd jl) = \<sigma>1 @ \<sigma>2 @ \<sigma>3 \<and> ELD_1 r (l (fst (snd p, fst p))) (l (snd (snd p, fst p))) \<tau>1 \<tau>2 \<tau>3 \<and> ELD_1 r (l (snd (snd p, fst p))) (l (fst (snd p, fst p))) \<sigma>1 \<sigma>2 \<sigma>3" by auto
 thus ?thesis unfolding eld_seq_def by fast
qed
*)

lemma eld_mirror: assumes "eldc (R :: (_,_ :: infinite)trs) l r p" shows "eldc R l r (snd p,fst p)" proof -
  from assms obtain jl1 jl2 jl3 jr1 jr2 jr3 where d: "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
  and D: "eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3" unfolding eldc_def by auto
  from d have  d: "ldc_trs R (snd p,fst p) jr1 jr2 jr3 jl1 jl2 jl3" unfolding ldc_trs_def by (metis fst_conv mirror snd_conv) 
  from D have D: "eld_conv l r (snd p,fst p) jr1 jr2 jr3 jl1 jl2 jl3" unfolding eld_conv_def by auto 
  show ?thesis using d D unfolding eldc_def by fast
qed

lemma main_eld:
  assumes cps:"\<forall> (b, p) \<in> critical_peaks ren R. eldc R l r p"
  and lab: "compatible R l r" 
  shows "\<forall> p \<in> local_peaks R. eldc R l r p" 
proof
  fix p 
  assume A: "p \<in> local_peaks R" 
  show "eldc R l r p" 
  proof -
    show ?thesis using local_peaks_cases[OF A]
    proof (cases "parallel_peak R p")
      case True 
      show ?thesis using True lab unfolding compatible_def by fast
    next
      case False note po = this
      then show ?thesis using local_peaks_cases[OF A] 
      proof (cases "variable_peak R p \<or> function_peak R p")
        case True 
        show ?thesis using left[OF True cps lab] by auto
      next
        case False 
        then have F: "variable_peak R (snd p,fst p) \<or> function_peak R (snd p,fst p)" 
          using local_peaks_cases[OF A] po by auto
        then have "eldc R l r (snd p, fst p)" using left[OF F cps lab] by auto
        then show ?thesis using eld_mirror by (metis fst_conv snd_conv surjective_pairing)
      qed
    qed
  qed
qed

lemma trivial_peak_eld:
  assumes eq: "t1 = t2"
  and "((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) \<in> local_peaks R"
  shows "eld R lab r ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2))" (is "eld _ _ _ ?p")
unfolding eld_def
proof (intro exI conjI)
  show "eld_conv lab r ?p (t1,[]) (t1, []) (t1,[]) (t2,[]) (t2, []) (t2,[])"
   unfolding eld_conv_def ELD_1_def  by auto
  show "ld_trs R ?p (t1,[]) (t1, []) (t1,[]) (t2,[]) (t2,[]) (t2,[])"
    using assms conv.intros(1) seq.intros(1) unfolding get_target_def ld_trs_def by auto
qed

lemma trivial_peak_eld_fan:
  assumes eq: "t1 = t2"
  and "((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2)) \<in> local_peaks R"
  shows "eld_fan R lab r ((s1,r1,p1,\<sigma>1,True,t1),(s2,r2,p2,\<sigma>2,True,t2))" (is "eld_fan _ _ _ ?p")
unfolding eld_fan_def
proof (intro exI conjI)
  show "eld_conv lab r ?p (t1,[]) (t1, []) (t1,[]) (t2,[]) (t2, []) (t2,[])"
   unfolding eld_conv_def ELD_1_def  by auto
  show "ldc_trs R ?p (t1,[]) (t1, []) (t1,[]) (t2,[]) (t2,[]) (t2,[])"
    using assms conv.intros(1) seq.intros(1) unfolding get_target_def ldc_trs_def by auto
  show "fan R ?p (t1,[]) (t1, []) (t1,[]) (t2,[]) (t2,[]) (t2,[])" 
    unfolding fan_def get_source_def by auto
qed

(* connect TRS with labeled ARS *)
lemma rstep_is_rstep_r_p_s: "rstep R = (\<Union> (rl,p,\<sigma>). rstep_r_p_s R rl p \<sigma>)"  proof 
 show "rstep R \<subseteq> (\<Union>(rl, p, \<sigma>). rstep_r_p_s R rl p \<sigma>)" proof 
  fix s t assume A:"(s, t) \<in> rstep R" show "(s,t) \<in> (\<Union>(rl, p, \<sigma>). rstep_r_p_s R rl p \<sigma>)" proof -
  obtain rl p \<sigma> where "(s,t) \<in> rstep_r_p_s R rl p \<sigma>" using A rstep_iff_rstep_r_p_s by metis
  then show ?thesis by blast
  qed
 qed
 next 
 show "(\<Union>(rl, p, \<sigma>). rstep_r_p_s R rl p \<sigma>) \<subseteq> rstep R" proof 
  fix s t assume A: "(s,t) \<in> (\<Union>(rl, p, \<sigma>). rstep_r_p_s R rl p \<sigma>)" show "(s,t) \<in> rstep R" proof -
  from A obtain l r p \<sigma> where "(s, t) \<in> rstep_r_p_s R (l, r) p \<sigma>" by auto
  then show ?thesis using rstep_iff_rstep_r_p_s by metis
  qed
 qed
qed

lemma rstep_is_rstep_r_p_s_ast: "(\<Union> (rl,p,\<sigma>). rstep_r_p_s R rl p \<sigma>)^* = (rstep R)^*" using rstep_is_rstep_r_p_s by metis

(*labeled steps*)
definition rlstep_r_p_s :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> ('f,'v) rule \<Rightarrow> pos \<Rightarrow> ('f,'v) subst \<Rightarrow> 'a \<Rightarrow> ('f,'v) term rel"
 where "rlstep_r_p_s R l rl p \<sigma> = (\<lambda>a. {(s,t). (s,t) \<in> rstep_r_p_s R rl p \<sigma> \<and> a = l (s,rl,p,\<sigma>,True,t)})"

abbreviation label_trs :: "('f,'v) trs \<Rightarrow> ('f,'v,'a) labeling \<Rightarrow> 'a \<Rightarrow> ('f,'v) term rel" where
 "label_trs R l \<equiv> \<lambda>a. \<Union> (rl,p,\<sigma>) \<in> UNIV. rlstep_r_p_s R l rl p \<sigma> a"

lemma local_peak_introduce:
  assumes "(s,t) \<in> rlstep_r_p_s R l rl1 p1 \<sigma>1 a" and "(s,u) \<in> rlstep_r_p_s R l rl2 p2 \<sigma>2 b"
  shows "((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u)) \<in> local_peaks R" and "a = l (s,rl1,p1,\<sigma>1,True,t)" and "b = l (s,rl2,p2,\<sigma>2,True,u)"
using assms unfolding local_peaks_def rlstep_r_p_s_def apply auto using surjective_pairing by metis

lemma R_step_imp_lars_step:
  assumes "(s,t) \<in> rstep_r_p_s R rl p \<sigma>"
  shows "(s,t) \<in> label_trs R l (l (s,rl,p,\<sigma>,True,t))"
using assms unfolding rlstep_r_p_s_def by blast

lemma seq_imp_ast: assumes "ss \<in> seq R" and "set (map l (snd ss)) \<subseteq> ds r S" 
defines "rel \<equiv> \<lambda> c. {(s,t). \<exists> r p \<sigma>. (s,t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s,r,p,\<sigma>,True,t) = c}"
shows "(first ss,last ss) \<in> (\<Union>c \<in> ds r S. rel c)^*"
proof -
 from assms obtain t ts where ss_dec: "ss = (t,ts)" by (metis surjective_pairing)
 from assms  show ?thesis unfolding ss_dec proof (induct ts arbitrary:t rule:list.induct)
 case Nil then have "first (t,[]) = last (t,[])" by auto 
 then show ?case by auto
next
 case (Cons x xs) 
  from Cons(2) obtain rl p \<sigma> u where  x_dec: "x = (t,rl,p,\<sigma>,True,u)" by (cases, auto)
  have step: "(t,u) \<in> rstep_r_p_s R rl p \<sigma>" using seq_chop_first Cons(2) unfolding x_dec by fast
  have seq: "(u,xs) \<in> seq R"  using seq_chop_first Cons(2) unfolding x_dec by fast
  have lab: "l (t,rl,p,\<sigma>,True,u) \<in> ds r S" using step Cons(3) x_dec by auto
  then have step: "(t,u) \<in> \<Union> (rel ` ds r S)" using step unfolding rel_def by fast 
  from Cons(1)[OF seq] Cons(3) have steps:"(first (u, xs), Decreasing_Diagrams2.last (u, xs)) \<in> (\<Union> (rel ` ds r S))\<^sup>*" unfolding x_dec rel_def by auto
  then show ?case using step unfolding x_dec unfolding first.simps last.simps get_target_def apply auto by (metis converse_rtrancl_into_rtrancl local.step)
 qed
qed

lemma seq_imp_refl: assumes "ss \<in> seq R" and "length (snd ss) \<le> 1" and "set (map l (snd ss)) \<subseteq> ds r S" 
defines "rel \<equiv> \<lambda> c. {(s,t). \<exists> r p \<sigma>. (s,t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s,r,p,\<sigma>,True,t) = c}"
shows "(first ss,last ss) \<in> (\<Union>c \<in> ds r S. rel c)^=" proof (cases "snd ss")
 case Nil then have "first ss = last ss" by (cases "ss", auto) 
  then show ?thesis by auto
 next
 case (Cons x xs) then have ss_dec: "ss = (fst ss, x#xs)" using assms by (metis (erased, opaque_lifting) surjective_pairing)
  then have seq:"(fst ss, x#xs) \<in> seq R" using assms by auto
  then obtain t rl p \<sigma> u where  x_dec: "x = (t,rl,p,\<sigma>,True,u)" by (cases, auto)
  then have xs_dec: "xs = []" using assms Cons by auto
  then have k: "(fst ss,(t,rl,p,\<sigma>,True,u)#[]) \<in> seq R" using ss_dec seq unfolding x_dec by auto
  then have eq1: "fst ss = t" using seq.cases by (cases, auto)
  then have ss_dec: "ss = (t,[x])" using ss_dec xs_dec by auto
  from k have "(t,(t,rl,p,\<sigma>,True,u)#[]) \<in> seq R" by (cases, auto)
  then have step: "(t,u) \<in> rstep_r_p_s R rl p \<sigma>" using seq_chop_first by fast
  have lab: "l (t,rl,p,\<sigma>,True,u) \<in> ds r S" using assms ss_dec unfolding x_dec by (metis (erased, opaque_lifting) insert_iff list.simps(9) local.Cons set_simps(2) subsetCE x_dec)
  have eq2: "last ss = u" unfolding ss_dec x_dec xs_dec last.simps get_target_def by auto
 show ?thesis using step lab unfolding ss_dec first.simps last.simps x_dec get_target_def snd_conv rel_def by fastforce
qed



lemma eld_imp_fars_eld_step:
  assumes la: "l (x,rl1,p1,s1,True,y) = a" and lb: "l (x,rl2,p2,s2,True,z) = b" 
  and eld: "eldc R l r ((x,rl1,p1,s1,True,y),(x,rl2,p2,s2,True,z))" (is "eldc R l r ?p")
  and lab: "is_labeling R l r"
  defines "rel \<equiv> \<lambda> c. {(s,t). \<exists> r p \<sigma>. (s,t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s,r,p,\<sigma>,True,t) = c}"
  shows "(\<exists>y1 y2 z1 z2 v. 
    (y, y1) \<in> ((\<Union>c\<in>ds (fst r) {a}. rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and>
    (y1, y2) \<in> (\<Union>c\<in>ds (snd r) {b}. rel c)\<^sup>= \<and>
    (y2, v) \<in> ((\<Union>c\<in>ds (fst r) {a, b}. rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and>
    (z, z1) \<in> ((\<Union>c\<in>ds (fst r) {b}. rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and>
    (z1, z2) \<in> (\<Union>c\<in>ds (snd r) {a}. rel c)\<^sup>= \<and>
    (z2, v) \<in> ((\<Union>c\<in>ds (fst r) {a, b}. rel c)\<^sup>\<leftrightarrow>)\<^sup>* )"
proof -
 from eld obtain jl1 jl2 jl3 jr1 jr2 jr3 where d: "ldc_trs R ((x, rl1, p1, s1,True, y), x, rl2, p2, s2,True, z) jl1 jl2 jl3 jr1 jr2 jr3" 
   and eld: "eld_conv l r ((x, rl1, p1, s1,True, y), x, rl2, p2, s2,True, z) jl1 jl2 jl3 jr1 jr2 jr3" unfolding eldc_def by auto
 from d eld have jl1: "jl1 \<in> conv R" and fsty: "first jl1 = y" unfolding ldc_trs_def get_target_def by auto
 then obtain \<sigma>1 \<sigma>2 \<sigma>3
   where ml1: "map l (snd jl1) = \<sigma>1" and ml2: "map l (snd jl2) = \<sigma>2 " and ml3: "map l (snd jl3) = \<sigma>3"
  and l1: "jl1 \<in> conv R" and l2: "jl2 \<in> seq R" and l3: "jl3 \<in> conv R"
  and eld1: "ELD_1 r (l (fst ?p)) (l (snd ?p)) \<sigma>1 \<sigma>2 \<sigma>3" using eld d unfolding ldc_trs_def eld_conv_def by auto
 have len2: "length (snd jl2) \<le> 1" using eld1 ml2 unfolding ELD_1_def using length_map by auto
 then have eq_l1: "first jl1 = y" using fsty by blast
 have m1: "set (map l (snd jl1)) \<subseteq> ds (fst r) {a}" using ml1 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb by auto
 have l1: "(first jl1,last jl1) \<in> ((\<Union>c \<in> ds (fst r) {a}. rel c)\<^sup>\<leftrightarrow>)^*" using conv_imp_conv[OF l1 m1] lab unfolding rel_def by (cases r) auto
  have m2: "set (map l (snd jl2)) \<subseteq> ds (snd r) {b}" using ml2 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb by auto 
 have l2: "(first jl2,last jl2) \<in> (\<Union>c \<in> ds (snd r) {b}. rel c)^=" using seq_imp_refl[OF l2 len2 m2] eld unfolding rel_def by fast
    have m3: "set (map l (snd jl3)) \<subseteq> ds (fst r) {a,b}"  using ml3 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb ds_def by auto 
 have l3: "(first jl3,last jl3) \<in> ((\<Union>c \<in> ds (fst r) {a,b}. rel c)\<^sup>\<leftrightarrow>)^*" using conv_imp_conv[OF l3 m3] eld lab unfolding rel_def by (cases r) auto 

(* merge with upper twin *)
 from d eld have jr1: "jr1 \<in> conv R" and fstz: "first jr1 = z" unfolding ldc_trs_def get_target_def by auto
 then obtain \<tau>1 \<tau>2 \<tau>3
   where mr1: "map l (snd jr1) = \<tau>1" and mr2: "map l (snd jr2) = \<tau>2" and mr3: "map l (snd jr3) = \<tau>3" 
  and r1: "jr1 \<in> conv R" and r2: "jr2 \<in> seq R" and r3: "jr3 \<in> conv R"
 and eld1: "ELD_1 r (l (snd ?p)) (l (fst ?p)) \<tau>1 \<tau>2 \<tau>3" using eld d unfolding ldc_trs_def eld_conv_def by auto
 have len2: "length (snd jr2) \<le> 1" using eld1 mr2 unfolding ELD_1_def using length_map by auto 
have m1: "set (map l (snd jr1)) \<subseteq> ds (fst r) {b}" using mr1 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb by auto
 have r1: "(first jr1,last jr1) \<in> ((\<Union>c \<in> ds (fst r) {b}. rel c)\<^sup>\<leftrightarrow>)^*" using conv_imp_conv[OF r1 m1] eld lab unfolding rel_def by (cases r) auto 
  have m2: "set (map l (snd jr2)) \<subseteq> ds (snd r) {a}" using mr2 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb by auto 
 have r2: "(first jr2,last jr2) \<in> (\<Union>c \<in> ds (snd r) {a}. rel c)^=" using seq_imp_refl[OF r2 len2 m2] eld unfolding rel_def by fast 
    have m3: "set (map l (snd jr3)) \<subseteq> ds (fst r) {a,b}"  using mr3 using eld1 unfolding ELD_1_def fst_conv snd_conv la lb ds_def by auto 
 have r3: "(first jr3,last jr3) \<in> ((\<Union>c \<in> ds (fst r) {a,b}. rel c)\<^sup>\<leftrightarrow>)^*" using conv_imp_conv[OF r3 m3] eld lab unfolding rel_def by (cases r) auto 

 have eq: "last jl1 = first jl2" "last jl2 = first jl3" 
          "last jr1 = first jr2" "last jr2 = first jr3"
          "last jl3 = last jr3" using d unfolding ldc_trs_def by auto 
 show ?thesis using l1 l2 l3 r1 r2 r3 unfolding eq using fsty fstz by blast
qed

lemma eld_imp_fars_eld:  
  assumes lp: "\<forall> p \<in> local_peaks R. eldc R l r p"
  and lab: "is_labeling R l r" 
  shows "fars_eld (fst r) (snd r) (\<lambda> c. {(s,t). \<exists> r p \<sigma>. (s,t) \<in> (rstep_r_p_s R r p \<sigma>) \<and> l (s,r,p,\<sigma>,True,t) = c})" (is "fars_eld _ _ ?rel") 
proof -
  { fix a b x y z
    assume "(x, y) \<in> {(s, t). \<exists>r p \<sigma>. (s, t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s, r, p, \<sigma>, True, t) = a}"
      and "(x, z) \<in> {(s, t). \<exists>r p \<sigma>. (s, t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s, r, p, \<sigma>, True, t) = b}"
    then obtain rl1 p1 s1 rl2 p2 s2 where 
      "(x,y) \<in> rstep_r_p_s R rl1 p1 s1" and la:"l (x,rl1,p1,s1, True,y) = a" and
      "(x,z) \<in> rstep_r_p_s R rl2 p2 s2" and lb:"l (x,rl2,p2,s2, True,z) = b" 
      by auto
    then have lp_mem: "((x,rl1,p1,s1, True,y),(x,rl2,p2,s2, True,z)) \<in> local_peaks R" (is "?p \<in> _") 
      unfolding local_peaks_def by fast
    then have eld: "eldc R l r ?p" using lp by auto
    have "(\<exists>y1 y2 z1 z2 v.  (y, y1) \<in> ((\<Union>c\<in>ds (fst r) {a}. ?rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and> (y1, y2) \<in> (\<Union>c\<in>ds (snd r) {b}. ?rel c)\<^sup>= \<and> (y2, v) \<in> ((\<Union>c\<in>ds (fst r) {a, b}. ?rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and>
      (z, z1) \<in> ((\<Union>c\<in>ds (fst r) {b}. ?rel c)\<^sup>\<leftrightarrow>)\<^sup>* \<and> (z1, z2) \<in> (\<Union>c\<in>ds (snd r) {a}. ?rel c)\<^sup>= \<and> (z2, v) \<in> ((\<Union>c\<in>ds (fst r) {a, b}. ?rel c)\<^sup>\<leftrightarrow>)\<^sup>* )" 
      using eld_imp_fars_eld_step[OF la lb eld lab] unfolding rel_def by auto
  }
  then show ?thesis unfolding fars_eld_def rel_def unfolding ds_to_under
    apply (intro allI)
    subgoal premises p for x y z a b using p[of x y a z b] by blast
  done
qed

lemma main:
  assumes "rel_props (fst r) (snd r)" 
  and lab: "compatible R l r" 
  and dec: "\<forall> (b, p) \<in> critical_peaks ren R. eldc R l r p" 
  shows "CR (rstep R)" 
proof -
  let ?rel = "\<lambda> c. {(s,t). \<exists> r p \<sigma>. ((s,t) \<in> rstep_r_p_s R r p \<sigma> \<and> l (s,r,p,\<sigma>,True,t) = c)}"
  from assms have i: "irrefl (fst r)" unfolding rel_props_def by (metis irrefl_def wf_not_sym)
  have lp: "\<forall>p \<in> local_peaks R. eldc R l r p" using main_eld[OF dec lab] by fast
  have eq: "(\<Union>c\<in>UNIV. ?rel c) = (rstep R)" (is "?l = _") unfolding rstep_is_rstep_r_p_s using assms apply auto by blast
  then have fars_eld: "fars_eld (fst r) (snd r) ?rel" using eld_imp_fars_eld[OF lp] lab[unfolded compatible_def] by auto
 then show ?thesis using fars_eld_imp_cr[OF assms(1) fars_eld] eq by auto
qed

(* Section: Applications *)
(* towards concrete labelings *)

lemma parallel_peak_close: 
assumes "parallel_peak R p"
shows "\<exists> s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u v.(
 p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u)) \<and>
 (s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1 \<and>
 (s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and>
 (t,v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and>
 (u,v) \<in> rstep_r_p_s R rl1 p1 \<sigma>1
)" proof -
 from assms(1) obtain r1 p1 s1 t s r2 p2 s2 u where p: "p \<in> local_peaks R" and p_dec: "p = ((s,r1,p1,s1,True,t),(s,r2,p2,s2,True,u))" and b:"parallel_pos p1 p2" unfolding parallel_peak_def local_peaks_def Let_def by fast
 then have s1: "(s,t) \<in> rstep_r_p_s R r1 p1 s1" and s2: "(s,u) \<in> rstep_r_p_s R r2 p2 s2" unfolding local_peaks_def by auto
 obtain v where j1: "(t,v) \<in> rstep_r_p_s R r2 p2 s2" and j2:"(u,v) \<in> rstep_r_p_s R r1 p1 s1" using parallel_steps[OF _ _ b] s1 s2 surj_pair by metis
 then show ?thesis using s1 s2 p_dec by fast
qed

lemma local_peaks_intros: 
  assumes "parallel_peak R p" 
  shows "p \<in> local_peaks R" 
using assms unfolding parallel_peak_def by auto

lemma diamond_trs_and_weld_seq_imp_eld: 
  assumes "diamond_trs R p jl jr" 
  and weld_seq: "weld_seq l r p jl jr" 
  shows "eldc R l r p" 
proof -
 from assms have ldc_trs: "ldc_trs R p (get_target (fst p),[]) jl (last jl,[]) (get_target (snd p),[]) jr (last jr,[])" 
  (is "ldc_trs _ _ ?jl1 _ ?jl3 ?jr1 _ ?jr3") unfolding ldc_trs_def diamond_trs_def by auto
 have "eld_conv l r p ?jl1 jl ?jl3 ?jr1 jr ?jr3" proof -
  have "\<forall>a\<in>set (map l (snd jl)). (a, l (snd p)) \<in> snd r" using assms unfolding weld_seq_def labels_def ds_def by auto 
  then have l: "ELD_1 r (l (fst p)) (l (snd p)) [] (map l (snd jl)) []" using assms unfolding diamond_trs_def weld_seq_def ELD_1_def ds_def by auto
  have lx: "map l (snd jl) = [] @ map l (snd jl) @ []" by auto
  have "\<forall>a\<in>set (map l (snd jr)). (a, l (fst p)) \<in> snd r" using assms unfolding weld_seq_def labels_def ds_def by auto 
  then have r: "ELD_1 r (l (snd p)) (l (fst p)) [] (map l (snd jr)) []" using assms unfolding diamond_trs_def weld_seq_def ELD_1_def ds_def by auto
  have rx: "map l (snd jr) = [] @ map l (snd jr) @ []" by auto
  show ?thesis using l lx r rx unfolding eld_conv_def get_target_def by auto
 qed
 then show ?thesis using ldc_trs unfolding eldc_def by fast
qed

 (** rule labeling **)
fun rule_labeling :: "(('f,'v) rule \<Rightarrow> nat) \<Rightarrow> ('f,'v) step \<Rightarrow> nat"
 where "rule_labeling i (s,rl,p,\<sigma>,t) = i rl"

lemma rl_is_labeling: "is_labeling R (rule_labeling i) r" unfolding is_labeling_def by auto 

lemma rl_parallel:
  assumes r: "refl (snd r)" 
  and "parallel_peak R p"
  shows  "eldc R (rule_labeling i) r p" 
proof -
 obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u v where
 p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))" (is "p = ?p") and
 steps: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1 \<and>
 (s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and>
 (t,v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and>
 (u,v) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" using parallel_peak_close[OF assms(2)] by fast
 have lp: "p \<in> local_peaks R" using local_peaks_intros[OF assms(2)] by auto
 from steps have jl: "(t,[(t,rl2,p2,\<sigma>2,True,v)]) \<in> seq R" (is "?jl \<in> _") using seq.intros by fast
 from steps have jr: "(u,[(u,rl1,p1,\<sigma>1,True,v)]) \<in> seq R" (is "?jr \<in> _") using seq.intros by fast
 have diamond_trs: "diamond_trs R ?p ?jl ?jr" using lp jl jr conv.intros unfolding p_dec ldc_trs_def last.simps get_target_def diamond_trs_def by auto
 have weld_seq: "weld_seq (rule_labeling i) r ?p ?jl ?jr" unfolding weld_seq_def labels_def ds_def apply auto using r apply (metis UNIV_I refl_on_def) using r by (metis UNIV_I refl_on_def)
 then show ?thesis using diamond_trs_and_weld_seq_imp_eld[OF diamond_trs weld_seq] unfolding p_dec by metis
qed

lemma rl_variable:
  assumes r: "refl (snd r)" 
  and vp: "variable_peak R p" 
  and lin: "linear_trs R"
  shows "eldc R (rule_labeling i) r p" 
proof -
 from assms have p: "p \<in> local_peaks R" unfolding variable_peak_def by auto
 from assms variable_peak_decompose[OF vp] obtain s t u l1 r1 p1 \<sigma>1 l2 r2 p2 \<sigma>2 q q1 q2 w where
   p_dec: "p = ((s, (l1, r1), p1, \<sigma>1,True, t), s, (l2, r2), p2, \<sigma>2,True, u)" and 
   s1: "(s, t) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1" and s2: "(s, u) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2" and
   rest: "p1 @ q = p2" "q1 @ q2 = q" "q1 \<in> poss l1" "l1 |_ q1 = Var w" by fast
 let ?\<sigma>3 = "(\<lambda>y. if y = w then (ctxt_of_pos_term q2 (\<sigma>1 y))\<langle>r2 \<cdot> \<sigma>2\<rangle> else \<sigma>1 y)"
 let ?v = "(ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> ?\<sigma>3\<rangle>"
 from lin have linl1: "linear_term l1" and linl2: "linear_term r1" using s1 s2 unfolding rstep_r_p_s_def linear_trs_def Let_def by auto 
 from variable_steps_lin[OF s1 s2 rest linl1] linl2 have
 sr: "(u, ?v) \<in> rstep_r_p_s R (l1, r1) p1 ?\<sigma>3" and
 sl: "t = ?v \<or> (\<exists>q. q \<in> poss r1 \<and> r1 |_ q = Var w \<and> (t, ?v) \<in> rstep_r_p_s R (l2, r2) (p1 @ q @ q2) \<sigma>2)" unfolding linear_trs_def by auto
 have jr: "(u,[(u,(l1,r1),p1,?\<sigma>3,True,?v)]) \<in> seq R" (is "?jr \<in> _") using rstep_is_seq[OF sr] by auto
 show ?thesis proof (cases "t = ?v") 
  case True then have jl: "(t,[]) \<in> seq R" (is "?jl \<in> _") using seq.intros by auto
  have "last ?jl = get_target (fst p)" unfolding p_dec last.simps get_target_def by auto
  then have diamond_trs: "diamond_trs R p ?jl ?jr" using p jl jr True unfolding diamond_trs_def ldc_trs_def p_dec get_target_def apply auto
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   by (simp add: get_target_def)
  have weld_seq: "weld_seq (rule_labeling i) r p ?jl ?jr" unfolding weld_seq_def labels_def p_dec ds_def apply auto using r by (metis (poly_guards_query) UNIV_I refl_on_def)
  then show ?thesis using diamond_trs_and_weld_seq_imp_eld[OF diamond_trs weld_seq] by fast
 next
  case False then obtain q where sl: "(t, ?v) \<in> rstep_r_p_s R (l2, r2) (p1 @ q @ q2) \<sigma>2" using sl by auto
  then have jl: "(t,[(t,(l2,r2),p1@q@q2,\<sigma>2,True,?v)]) \<in> seq R" (is "?jl \<in> _") using rstep_is_seq[OF sl] by auto
  then have diamond_trs: "diamond_trs R p ?jl ?jr" using p jl jr False unfolding diamond_trs_def ldc_trs_def p_dec get_target_def apply auto
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
  by (auto simp add: get_target_def)
  have weld_seq: "weld_seq (rule_labeling i) r p ?jl ?jr" unfolding weld_seq_def labels_def p_dec ds_def apply auto using r apply (metis UNIV_I refl_on_def) using r by (metis UNIV_I refl_on_def)  
  then show ?thesis using diamond_trs_and_weld_seq_imp_eld[OF diamond_trs weld_seq] by fast
 qed
qed

lemma rule_labeling_is_compatible:
  assumes r: "refl (snd r)" 
  and lin: "linear_trs R"
  shows "compatible R (rule_labeling i) r" 
unfolding compatible_def using assms rl_is_labeling rl_variable[OF r _ lin] rl_parallel by blast

lemma rule_labeling_has_rel_props:
  defines "r \<equiv> ({(n,m). n < (m::nat)},{(n,m). n \<le> (m::nat)})"
  shows "rel_props (fst r) (snd r)" 
proof -
 have r:  "refl (snd r)" using r_def apply auto by (simp add: refl_on_def)
 have t1: "trans (fst r)" using r_def apply auto by (metis less_trans transp_def transp_trans) 
 have t2: "trans (snd r)" using r_def apply auto by (metis order_trans transp_def transp_trans)
 have wf: "wf (fst r)" using r_def apply auto by (metis wf_less) 
 have compat: "snd r O fst r O snd r \<subseteq> fst r" unfolding r_def by auto 
 have "rel_props (fst r) (snd r)" unfolding rel_props_def using t1 t2 wf r compat by auto
 then show ?thesis by auto
qed 
 
corollary rule_labeling_is_sound:
  defines "r \<equiv> ({(n,m). n < (m::nat)},{(n,m). n \<le> (m::nat)})"
  assumes lin: "linear_trs R"
  and dec: "\<forall> (b,p) \<in> critical_peaks ren R. eldc R (rule_labeling i) r p" (is "\<forall> (b,p) \<in> _ . eldc _ ?l ?r _")
  shows "CR (rstep R)" 
proof -
 have r:  "refl (snd r)" using r_def apply auto by (simp add: refl_on_def)
 have lab: "compatible R (rule_labeling i) ?r" using rule_labeling_is_compatible[OF r lin]  by auto
 have props: "rel_props (fst r) (snd r)" using rule_labeling_has_rel_props r_def by fast
 show ?thesis using main[OF props lab dec] by auto
qed

(** source labeling **)
fun source_labeling :: "('f,'v) step \<Rightarrow> ('f,'v) term"
 where "source_labeling (s,rl,p,\<sigma>,t) = s"
 
fun sl_rel :: "('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> (('f,'v) term) relp"
 where "sl_rel R S = (((relto (rstep R) (rstep S))^+)\<inverse>,((rstep S \<union> rstep R)^* )\<inverse>)"

lemma sl_is_labeling:
  "is_labeling (R\<union>S) source_labeling (sl_rel R S)"
 proof -
 {fix s a b t u C \<rho> \<sigma>1 aa p1 ba v \<sigma>2 p2 
 assume        C:"(u, s) \<in> ((rstep S)\<^sup>* O rstep R O (rstep S)\<^sup>* )\<^sup>+" (is "_ \<in> ?rel^+") 
 then obtain n where n1: "n > 0" and n:"(u,s) \<in> ?rel^^n" by (metis trancl_power) 
 from n have "(C\<langle>u \<cdot> \<rho>\<rangle>, C\<langle>s \<cdot> \<rho>\<rangle>) \<in> ?rel^^n"  proof (induct n arbitrary:u)
  case 0 then show ?case by auto
  next
  case (Suc n) then obtain v where step: "(u,v) \<in> ?rel" and steps: "(v,s) \<in> ?rel^^n" by (metis relpow_Suc_E2)
  from step obtain u' v' where "(u,u') \<in> (rstep S)^*" and "(u',v') \<in> rstep R" and "(v',v) \<in> (rstep S)^*" by auto 
  then obtain u' v' where "(C\<langle>u\<cdot>\<rho>\<rangle>,C\<langle>u'\<cdot>\<rho>\<rangle>) \<in> (rstep S)^*" and "(C\<langle>u'\<cdot>\<rho>\<rangle>,C\<langle>v'\<cdot>\<rho>\<rangle>) \<in> rstep R" and "(C\<langle>v'\<cdot>\<rho>\<rangle>,C\<langle>v\<cdot>\<rho>\<rangle>) \<in> (rstep S)^*"
   by (metis rstep_ctxt rstep_subst rsteps_closed_ctxt rsteps_closed_subst)
  then have 1:"(C\<langle>u\<cdot>\<rho>\<rangle>,C\<langle>v\<cdot>\<rho>\<rangle>) \<in> ?rel" by auto
  from steps have 2:"(C\<langle>v\<cdot>\<rho>\<rangle>,C\<langle>s\<cdot>\<rho>\<rangle>) \<in> ?rel^^n" using Suc by auto
  show ?case using 1 2 by (metis relpow_Suc_I2)
  qed
  then have "((C\<langle>u \<cdot> \<rho>\<rangle>, C\<langle>s \<cdot> \<rho>\<rangle>) \<in> ?rel^+)" using n1 by (metis trancl_power)
 } note A = this
 {fix s a b t u C \<rho> \<sigma>1 aa p1 ba v \<sigma>2 p2
  assume "(u, s) \<in> (rstep S \<union> rstep R)\<^sup>*"
   then have "(C\<langle>u \<cdot> \<rho>\<rangle>, C\<langle>s \<cdot> \<rho>\<rangle>) \<in> (rstep S \<union> rstep R)\<^sup>*" by (metis rstep_union rsteps_closed_ctxt rsteps_closed_subst)
 }
 then show ?thesis using A unfolding is_labeling_def step_close.simps by auto
qed

lemma sl_par:
  assumes pp: "parallel_peak (R\<union>S) p"
  shows "weld (R\<union>S) source_labeling (sl_rel R S) p" (is "weld _ _ ?r _") 
proof -
 obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u v where
 p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))"  and
 steps: "(s,t) \<in> rstep_r_p_s (R\<union>S) rl1 p1 \<sigma>1 \<and>
 (s,u) \<in> rstep_r_p_s (R\<union>S) rl2 p2 \<sigma>2 \<and>
 (t,v) \<in> rstep_r_p_s (R\<union>S) rl2 p2 \<sigma>2 \<and>
 (u,v) \<in> rstep_r_p_s (R\<union>S) rl1 p1 \<sigma>1" using parallel_peak_close[OF assms] by fast
 have lp: "p \<in> local_peaks (R\<union>S)" using local_peaks_intros[OF assms] by auto
 from steps have jl: "(t,[(t,rl2,p2,\<sigma>2,True,v)]) \<in> seq (R\<union>S)" (is "?jl \<in> _") using seq.intros by fast
 from steps have jr: "(u,[(u,rl1,p1,\<sigma>1,True,v)]) \<in> seq (R\<union>S)" (is "?jr \<in> _") using seq.intros by fast
 have diamond_trs: "diamond_trs (R\<union>S) p ?jl ?jr" using lp jl jr unfolding p_dec diamond_trs_def ldc_trs_def last.simps get_target_def 
 apply auto 
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) by blast
 from steps have s1:"(s,t) \<in> rstep (R \<union> S)" using rstep_r_p_s_imp_rstep by fast
 from steps have s2:"(s,u) \<in> rstep (R \<union> S)" using rstep_r_p_s_imp_rstep by fast
 have weld_seq: "weld_seq source_labeling ?r p ?jl ?jr" unfolding weld_seq_def labels_def p_dec ds_def apply auto
  using s1 s2 unfolding ds_def by auto
 show ?thesis using diamond_trs weld_seq unfolding weld_def ld2_trs_def diamond_trs_def by fast
qed

lemma sl_evar:
  assumes vp: "variable_peak (R\<union>S) p" (is "variable_peak ?R _")
  and lin: "linear_trs (R\<union>S)"
  shows "weld (R\<union>S) source_labeling (sl_rel R S) p"
proof -
 from assms have p: "p \<in> local_peaks ?R" unfolding variable_peak_def by auto
 from assms variable_peak_decompose[OF vp] obtain s t u l1 r1 p1 \<sigma>1 l2 r2 p2 \<sigma>2 q q1 q2 w where
   p_dec: "p = ((s, (l1, r1), p1, \<sigma>1,True, t), s, (l2, r2), p2, \<sigma>2,True, u)" and 
   s1: "(s, t) \<in> rstep_r_p_s ?R (l1, r1) p1 \<sigma>1" and s2: "(s, u) \<in> rstep_r_p_s ?R (l2, r2) p2 \<sigma>2" and
   rest: "p1 @ q = p2" "q1 @ q2 = q" "q1 \<in> poss l1" "l1 |_ q1 = Var w" by fast
 let ?\<sigma>3 = "(\<lambda>y. if y = w then (ctxt_of_pos_term q2 (\<sigma>1 y))\<langle>r2 \<cdot> \<sigma>2\<rangle> else \<sigma>1 y)"
 let ?v = "(ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> ?\<sigma>3\<rangle>"
 from s1 lin have l:"linear_term l1 \<and> linear_term r1" unfolding rstep_r_p_s_def Let_def linear_trs_def by auto
 from variable_steps_lin[OF s1 s2 rest] l have
 sr: "(u, ?v) \<in> rstep_r_p_s ?R (l1, r1) p1 ?\<sigma>3" and
 sl: "t = ?v \<or> (\<exists>q. q \<in> poss r1 \<and> r1 |_ q = Var w \<and> (t, ?v) \<in> rstep_r_p_s ?R (l2, r2) (p1 @ q @ q2) \<sigma>2)" by auto
 have jr: "(u,[(u,(l1,r1),p1,?\<sigma>3,True,?v)]) \<in> seq ?R" (is "?jr \<in> _") using rstep_is_seq[OF sr] by auto
 show ?thesis proof (cases "t = ?v") 
  case True then have jl: "(t,[]) \<in> seq ?R" (is "?jl \<in> _") using seq.intros by auto
  have "last ?jl = get_target (fst p)" unfolding p_dec last.simps get_target_def by auto
  then have diamond_trs: "diamond_trs ?R p ?jl ?jr" using p jl jr True unfolding diamond_trs_def ldc_trs_def p_dec apply auto 
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
by (auto simp add: get_target_def)
  have "weld_seq source_labeling (sl_rel R S) p ?jl ?jr" 
  unfolding weld_seq_def labels_def p_dec ds_def apply auto using s2 
   by (metis (erased, opaque_lifting) inf_sup_aci(5) r_into_rtrancl rstep_r_p_s_imp_rstep rstep_union)
   then show ?thesis using diamond_trs unfolding weld_def diamond_trs_def ld2_trs_def by fast
 next
  case False then obtain q where sl: "(t, ?v) \<in> rstep_r_p_s ?R (l2, r2) (p1 @ q @ q2) \<sigma>2" using sl by auto
  then have jl: "(t,[(t,(l2,r2),p1@q@q2,\<sigma>2,True,?v)]) \<in> seq ?R" (is "?jl \<in> _") using rstep_is_seq[OF sl] by auto
  then have diamond_trs: "diamond_trs ?R p ?jl ?jr" using p jl jr unfolding diamond_trs_def ldc_trs_def p_dec get_target_def apply auto
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   using conv.intros(1) apply blast
   by (auto simp add: get_target_def)
  have r: "refl (snd (sl_rel R S))" by (auto intro: refl_rtrancl)
  have weld_seq: "weld_seq source_labeling (sl_rel R S) p ?jl ?jr"
   unfolding weld_seq_def labels_def p_dec ds_def apply auto 
   using s1  apply (metis (erased, opaque_lifting) inf_sup_aci(5) r_into_rtrancl rstep_r_p_s_imp_rstep rstep_union)
   using s2 by (metis (erased, opaque_lifting) inf_sup_aci(5) r_into_rtrancl rstep_r_p_s_imp_rstep rstep_union)
    then show ?thesis using diamond_trs unfolding weld_def diamond_trs_def ld2_trs_def by fast
 qed
qed

lemma source_labeling_is_weakly_compatible:
  assumes lin: "linear_trs (R \<union> S)"
  shows "weakly_compatible (R \<union> S) source_labeling (sl_rel R S)" 
using sl_is_labeling sl_par sl_evar lin 
unfolding weakly_compatible_def weld_def eld_def eld_conv_def weld_seq_def 
by fast

definition rel_rstep :: "('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> (('f,'v) term) rel"
 where "rel_rstep R S = relto (rstep R) (rstep S)"
 
lemma S_RS: 
  assumes "(s,t) \<in> (rstep S)^*"
  and "(t,u) \<in> relto (rstep R) (rstep S)" 
  shows "(s,u) \<in> relto (rstep R) (rstep S)" 
using assms(2) rtrancl_trans[OF assms(1)] by auto

lemma S_RS_trancl: 
  assumes "(s,t) \<in> (rstep S)^*"
  and "(t,u) \<in> (relto (rstep R) (rstep S))^+"
  shows "(s,u) \<in> (relto (rstep R) (rstep S))^+" (is "_ \<in> ?R^+")
proof -
 from assms obtain m where "(t,m) \<in> ?R" and mu:"(m,u) \<in> ?R^*" by (auto dest!: tranclD)
 then have "(s,m) \<in> ?R" using assms(1) S_RS by metis
 then show ?thesis using mu by auto
qed

lemma RS_S:
  assumes "(t, u) \<in> relto (rstep R) (rstep S)"
  and "(u, v) \<in> (rstep S)\<^sup>*"
  shows "(t, v) \<in> relto (rstep R) (rstep S)"
using assms by force 

lemma RS_S_trancl: 
  assumes "(t,u) \<in> (relto (rstep R) (rstep S))^+" 
  and "(u,v) \<in> (rstep S)^*" 
  shows "(t,v) \<in> (relto (rstep R) (rstep S))^+" (is "_ \<in> ?R")
proof -
  from assms obtain m where "(t,m) \<in> ?R^*" and "(m,u) \<in> ?R" by blast
  then show ?thesis using assms RS_S rtrancl_into_trancl1 tranclD2 by metis
qed

lemma rel_compat:
  assumes "(s,t) \<in> (rstep S \<union> rstep R)^*"
  and "(t,u) \<in> (rel_rstep R S)^+"
  and "(u,v) \<in> (rstep S \<union> rstep R)^*"
  shows "(s,v) \<in> (rel_rstep R S)^+"
proof -
  have k: "(rstep S \<union> rstep R)^* \<subseteq> ((rstep S)^* \<union> (relto (rstep R) (rstep S))^*)" by regexp
  from k have ab: "(s,t) \<in> (relto (rstep R) (rstep S))^* \<or> (s,t) \<in> (rstep S)^*" (is "?a \<or> ?b") using assms by auto
  from k have cd:"(u,v) \<in> (relto (rstep R) (rstep S))^* \<or> (u,v) \<in> (rstep S)^*" (is "?c \<or> ?d") using assms by auto
  have su: "(s,u) \<in> (relto (rstep R) (rstep S))^+"
  proof (cases "?a")
    case True then show ?thesis using assms unfolding rel_rstep_def by (metis rtrancl_trancl_trancl)
  next
    case False then have "?b" using ab by auto
    then show ?thesis using assms(2) unfolding rel_rstep_def using S_RS_trancl by metis
  qed
  then show ?thesis
  proof (cases "?c")
    case True then show ?thesis unfolding rel_rstep_def using su by (metis True trancl_rtrancl_trancl)
  next
    case False then have "?d" using cd by auto
    then show ?thesis using su unfolding rel_rstep_def using RS_S_trancl by metis
  qed
qed

corollary source_labeling_and_SN_is_sound:
  fixes R S
  defines "r \<equiv> sl_rel R S"
  assumes lin: "linear_trs (R\<union>S)" (is "linear_trs ?R")
  and SN: "SN (rstep (R\<union>S))"
  and dec: "\<forall>(b,p) \<in> critical_peaks ren (R\<union>S). eldc (R\<union>S) source_labeling r p" 
  shows "CR (rstep (R\<union>S))"
proof -
  have lab: "compatible ?R source_labeling r" 
    using  source_labeling_is_weakly_compatible[OF lin] using linear_and_weakly_compatible_is_compatible[OF lin]
    unfolding r_def by auto  
  have t1: "trans (fst r)" unfolding r_def sl_rel.simps by auto
  have t2: "trans (snd r)" unfolding r_def sl_rel.simps by (auto intro: trans_rtrancl)
  have SN_R:"SN (rstep R)" and SN_S:"SN (rstep S)" using SN apply (metis SN_subset Un_left_absorb rstep_union subset_Un_eq) 
    by (metis (erased, opaque_lifting) SN SN_subset le_sup_iff rstep_union subset_refl)
  have "SN_rel (rstep R) (rstep S)"
  proof -
    have "SN_rel_on_alt (rstep (R \<union> S)) {} (Collect top)" by (metis SN SN_rel_empty2 SN_rel_on_conv top_set_def)
    then have "\<exists>x\<^sub>1. SN_rel_on_alt x\<^sub>1 {} (Collect top) \<and> rstep R \<subseteq> x\<^sub>1 \<and> rstep S \<subseteq> x\<^sub>1" using rstep_union by auto
    then show "SN_rel (rstep R) (rstep S)" by (metis (no_types) SN_rel_mono' SN_rel_on_conv sup_bot.right_neutral top_set_def)
  qed
  then have "SN ((fst r)\<inverse>)" using SN_R by (auto simp: r_def SN_imp_SN_trancl SN_rel_on_def) 
  then have wf: "wf (fst r)" using r_def SN_iff_wf by auto
  have r: "refl (snd r)" using r_def by (auto intro: refl_rtrancl)
  have compat: "snd r O fst r O snd r \<subseteq> fst r" unfolding r_def apply auto 
    using rel_compat unfolding rel_rstep_def by metis
  have rel_props:"rel_props (fst r) (snd r)" unfolding rel_props_def
    using t1 t2 wf r compat r_def by auto
  from lin have ll: "left_linear_trs (R\<union>S)" unfolding left_linear_trs_def linear_trs_def by auto
  show ?thesis using main[OF rel_props lab dec] by fast
qed

(* rule labeling left-linear case *)

lemma rl_variable2:
  assumes r: "refl (snd r)"
  and vp: "variable_peak R p" 
  and ll: "left_linear_trs R"
  shows "weld R (rule_labeling i) r p"
proof -
  from assms have p: "p \<in> local_peaks R" unfolding variable_peak_def by auto
  from assms variable_peak_decompose[OF vp] obtain s t u l1 r1 p1 \<sigma>1 l2 r2 p2 \<sigma>2 q q1 q2 w where
    p_dec: "p = ((s, (l1, r1), p1, \<sigma>1,True, t), s, (l2, r2), p2, \<sigma>2,True, u)" and 
    s1: "(s, t) \<in> rstep_r_p_s R (l1, r1) p1 \<sigma>1" and s2: "(s, u) \<in> rstep_r_p_s R (l2, r2) p2 \<sigma>2" and
    rest: "p1 @ q = p2" "q1 @ q2 = q" "q1 \<in> poss l1" "l1 |_ q1 = Var w" by fast
  let ?\<sigma>3 = "(\<lambda>y. if y = w then (ctxt_of_pos_term q2 (\<sigma>1 y))\<langle>r2 \<cdot> \<sigma>2\<rangle> else \<sigma>1 y)"
  let ?v = "(ctxt_of_pos_term p1 s)\<langle>r1 \<cdot> ?\<sigma>3\<rangle>"
  from ll have ll1: "linear_term l1" using s1 s2 unfolding rstep_r_p_s_def left_linear_trs_def Let_def by auto 
  show ?thesis
  proof (cases "linear_term r1")
    case False
    from variable_steps_left_lin[OF s1 s2 rest ll1] obtain steps where
      sr: "(u, ?v) \<in> rstep_r_p_s R (l1, r1) p1 ?\<sigma>3" and
      sl: "\<forall>i<length steps. fst (steps ! i) = (l2, r2)" "(t, steps, ?v) \<in> par_rstep2 R" unfolding linear_trs_def by auto
    have jr: "(u,[(u,(l1,r1),p1,?\<sigma>3,True,?v)]) \<in> seq R" (is "?jr \<in> _") using rstep_is_seq[OF sr] by auto
    obtain jl where "jl \<in> seq R" and "first jl = t" and "last jl = ?v"
      and jl_lab: "\<forall>i < length (snd jl). fst (snd (snd jl ! i)) = (l2,r2)"
      using par_rstep2_imp_seq sl unfolding get_rule_def by force
    then have d: "ldc_trs R p (get_target (fst p),[]) (get_target (fst p),[]) jl (get_target (snd p),[]) (get_target (snd p),[]) ?jr" 
      using p jr by (auto intro: conv.intros seq.intros seq_imp_conv simp: get_target_def  ldc_trs_def p_dec)
    then have d2: "ld2_trs R p jl ?jr" using False unfolding ld2_trs_def p_dec get_rule_def ldc_trs_def 
      using \<open>jl \<in> seq R\<close> jr by (auto intro: conv.intros simp: get_target_def)
    have  "weld_seq (rule_labeling i) r p jl ?jr" unfolding weld_seq_def p_dec labels_def using jl_lab r
      unfolding ds_def apply auto apply (metis UNIV_I fst_conv in_set_conv_nth refl_onD snd_conv)
      by (metis UNIV_I refl_onD)
    then show ?thesis unfolding weld_def using d2 by fast
  next
    case True
    then have l: "linear_term r1" by auto
    from variable_steps_lin[OF s1 s2 rest ll1] l have
      sr: "(u, ?v) \<in> rstep_r_p_s R (l1, r1) p1 ?\<sigma>3" and
      sl: "t = ?v \<or> (\<exists>q. q \<in> poss r1 \<and> r1 |_ q = Var w \<and> (t, ?v) \<in> rstep_r_p_s R (l2, r2) (p1 @ q @ q2) \<sigma>2)"
      unfolding linear_trs_def by auto
    have jr: "(u,[(u,(l1,r1),p1,?\<sigma>3,True,?v)]) \<in> seq R" (is "?jr \<in> _") using rstep_is_seq[OF sr] by auto
    show ?thesis
    proof (cases "t = ?v") 
      case True
      then have jl: "(t,[]) \<in> seq R" (is "?jl \<in> _") using seq.intros by auto
      have "?jl \<in> seq R" using jl by auto
      moreover have "length (snd ?jl) \<le> 1" by auto
      moreover have "first ?jl = t" by auto
      moreover have lastl: "last ?jl = ?v" using True by auto
      ultimately have jl: "?jl \<in> seq R \<and> length (snd ?jl) \<le> 1 \<and> first ?jl = t \<and> last ?jl = ?v" by auto
      have "p \<in> local_peaks R" using s1 s2 unfolding p_dec local_peaks_def by auto
      then have "ldc_trs R p (t,[]) ?jl (last ?jl,[]) (u,[]) (u,[]) ?jr" 
       using jl jr lastl unfolding last.simps ldc_trs_def  unfolding p_dec ldc_trs_def local_peaks_def get_target_def 
        apply (simp add: seq.intros(1)) by (simp add: conv.intros(1) seq_imp_conv)
      then have d2: "ld2_trs R p ?jl ?jr" using jl jr unfolding ld2_trs_def get_target_def apply auto
     unfolding get_target_def apply auto by (simp add: ldc_trs_def p_dec)
      have  "weld_seq (rule_labeling i) r p ?jl ?jr" unfolding weld_seq_def p_dec labels_def using r
        unfolding ds_def apply auto using assms(1) by (metis UNIV_I refl_onD)
      then show ?thesis using d2 unfolding weld_def by fast
    next
      case False
      then obtain q where sl: "(t, ?v) \<in> rstep_r_p_s R (l2, r2) (p1 @ q @ q2) \<sigma>2" using sl by auto
      then have jl: "(t,[(t,(l2,r2),p1@q@q2,\<sigma>2,True,?v)]) \<in> seq R" (is "?jl \<in> _") using rstep_is_seq[OF sl] by auto
      then have diamond_trs: "diamond_trs R p ?jl ?jr" 
        using p jl jr by (auto intro: conv.intros simp: get_target_def diamond_trs_def ldc_trs_def p_dec)
      then have d2: "ld2_trs R p ?jl ?jr" using p jl jr unfolding p_dec get_target_def diamond_trs_def ldc_trs_def ld2_trs_def by auto
      have  "weld_seq (rule_labeling i) r p ?jl ?jr" unfolding weld_seq_def p_dec labels_def using r
        unfolding ds_def apply auto using assms(1) by (metis UNIV_I refl_on_def)+
      then show ?thesis using d2 unfolding weld_def by fast
    qed
  qed
qed

lemma rule_labeling_parallel2:
  assumes "refl (snd r)" 
  and "parallel_peak R p"
  shows "weld R (rule_labeling i) r p"
proof -
  from assms parallel_peak_close obtain s t u v rl1 p1 \<sigma>1 rl2 p2 \<sigma>2
    where p_dec: "p = ((s, rl1, p1, \<sigma>1,True, t), s, rl2, p2, \<sigma>2,True, u)" and x: "(s, t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1 \<and>
    (s, u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and> (t, v) \<in> rstep_r_p_s R rl2 p2 \<sigma>2 \<and> (u, v) \<in> rstep_r_p_s R rl1 p1 \<sigma>1"
    by fast
  from x have 1:"(s,[(s,rl1,p1,\<sigma>1,True,t)]) \<in> seq R" by (metis rstep_is_seq)
  from x have 2:"(s,[(s,rl2,p2,\<sigma>2,True,u)]) \<in> seq R" by (metis rstep_is_seq)
  from x have 3:"(t,[(t,rl2,p2,\<sigma>2,True,v)]) \<in> seq R" (is "?jl \<in> _") by (metis rstep_is_seq)
  from x have 4:"(u,[(u,rl1,p1,\<sigma>1,True,v)]) \<in> seq R" (is "?jr \<in> _") by (metis rstep_is_seq)
  from p_dec x have "p \<in> local_peaks R" (is "?p \<in> _") unfolding local_peaks_def by fast
  then have "ldc_trs R p (first ?jl,[]) ?jl (last ?jl,[]) (first ?jr,[]) ?jr (last ?jr,[])" using 3 4 conv.simps unfolding last.simps get_target_def snd_conv first.simps p_dec unfolding ldc_trs_def get_target_def apply auto 
   unfolding get_target_def by auto
  then have x1: "ld2_trs R p ?jl ?jr" unfolding ld2_trs_def by (simp add: ldc_trs_def)
  have x2: "weld_seq (rule_labeling i) r p ?jl ?jr"  
    unfolding weld_seq_def p_dec labels_def ds_def apply auto using assms
    apply (metis UNIV_I refl_on_def) by (metis UNIV_I assms(1) refl_on_def)
  then show ?thesis using x1 unfolding weld_def by auto
qed
 
(* rule labeling (left linear case) *)
lemma rule_labeling_is_weakly_compatible:
  assumes "refl (snd r)" 
  and "left_linear_trs R"
  shows "weakly_compatible R (rule_labeling i) r"
proof -
  have c: "is_labeling R (rule_labeling i) r" using rl_is_labeling by fast
  {
    fix p
    assume "variable_peak R p \<or> parallel_peak R p" and "left_linear_trs R"
    then have "weld R (rule_labeling i) r p" using rl_variable2[OF assms(1) _ assms(2)] rule_labeling_parallel2[OF assms(1)] by metis
  }
  then show ?thesis unfolding weakly_compatible_def using c by fast
qed
 
definition R_d :: "('f,'v) trs \<Rightarrow> ('f,'v) trs"
 where "R_d R = {rl \<in> R. \<not> linear_term (snd rl)}"
 
definition R_nd :: "('f,'v) trs \<Rightarrow> ('f,'v) trs"
 where "R_nd R = {rl \<in> R. linear_term (snd rl)}"
  
definition lex_r :: "'a relp \<Rightarrow> 'b relp \<Rightarrow> ('a \<times> 'b) relp"
 where "lex_r r1 r2 = (lex_two (fst r1) (snd r1) (fst r2),
                       lex_two (fst r1) (snd r1) (snd r2))" 

lemma map_dec: 
  assumes "map f xs = ys1@ys2"
  shows "\<exists> xs1 xs2. xs = xs1@xs2 \<and> map f xs1 = ys1 \<and> map f xs2 = ys2"
using assms
proof (induct ys1 arbitrary: ys2 xs)
  case (Cons y ys)
  then obtain x' xs' where xs_dec: "xs = x'#xs'" by (metis append_Cons list.distinct(1) list.exhaust list.simps(8)) 
  then have map1: "map f xs' = ys@ys2" using Cons by auto
  then obtain xs1 xs2 where xs'_dec: "xs' = xs1 @ xs2" and map:" map f xs1 = ys \<and> map f xs2 = ys2" using Cons(1)[of xs' ys2] by fast
  then have "xs = (x'#xs1)@xs2" and "map f (x'#xs1) = (f x')#ys" and "map f xs2 = ys2" unfolding xs_dec by auto
  then show ?case by (metis Cons.prems append_Cons list.sel(1) list.simps(9))
qed auto

lemma R_d_union_R_nd: "R_d R \<union> R_nd R = R" unfolding R_d_def R_nd_def by auto

lemma l_sl:
  fixes l r R
  assumes "(s,t) \<in> (rstep R)^*"
  shows "(t,s) \<in> (snd (sl_rel (R_d R) (R_nd R)))"
using assms unfolding sl_rel.simps apply auto using R_d_union_R_nd by (metis inf_sup_aci(5) rstep_union) 
  
lemma l_imp_ll:
  fixes l r R
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  assumes "l step  \<in> ds (fst r) {l step', l step''}" 
  and "(get_source step',get_source step) \<in> (rstep R)^*"
  and "(get_source step'',get_source step) \<in> (rstep R)^*"
  shows "ll step \<in> ds (fst rr) {ll step', ll step''}"
proof - 
  from assms obtain s rl p \<sigma> t where step_dec: "step = (s,rl,p,\<sigma>,t)" by (metis (erased, opaque_lifting) source_labeling.cases)
  show ?thesis
  proof (cases "l step \<in> ds (fst r) {l step'}")
    case True
    from assms obtain s' rl' p' \<sigma>' t' where step'_dec: "step' = (s',rl',p',\<sigma>',t')"
      by (metis (erased, opaque_lifting) source_labeling.cases)
    have "(source_labeling step',source_labeling step) \<in> (rstep R)^*" using assms unfolding step_dec step'_dec
      unfolding get_source_def by auto
    then have l2: "(source_labeling step,source_labeling step') \<in> (snd (sl_rel (R_d R) (R_nd R)))" using l_sl by auto
    then have l1: "(l step,l step') \<in> (fst r)" using True unfolding ds_def by auto
    then have "(ll step,ll step') \<in> fst rr" using l2 unfolding lex_r_def ll_def rr_def by auto
    then show ?thesis unfolding ds_def by auto
  next
    case False (* symmetric case *)
    from assms obtain s' rl' p' \<sigma>' t' where step''_dec: "step'' = (s',rl',p',\<sigma>',t')"
      by (metis (erased, opaque_lifting) source_labeling.cases)
    have "(source_labeling step'',source_labeling step) \<in> (rstep R)^*"
      using assms unfolding step_dec step''_dec unfolding get_source_def by auto
    then have l2: "(source_labeling step,source_labeling step'') \<in> (snd (sl_rel (R_d R) (R_nd R)))" using l_sl by auto
    then have l1: "(l step,l step'') \<in> (fst r)" using False assms unfolding ds_def by auto
    then have "(ll step,ll step'') \<in> fst rr" using l2 unfolding lex_r_def ll_def rr_def by auto
    then show ?thesis unfolding ds_def by auto
  qed
qed

lemma l_imp_ll_seq:
  fixes l r R
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  assumes "set (map l ss) \<subseteq> ds (fst r) {l step',l step''}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
  and "\<forall>i < length ss. (get_source step'',get_source (ss !i)) \<in> (rstep R)^*"
  shows "set (map ll ss) \<subseteq> ds (fst rr) {ll step',ll step''}"
using assms(3-5)
proof (induct ss)
  case (Cons t ts)  
  then have step:"l t \<in> ds (fst r) {l step',l step''}" and steps:"set (map l ts) \<subseteq> ds (fst r) {l step', l step''}" by auto
  from Cons have c1: "\<forall>i<length ts. (get_source step', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  from Cons have c2: "\<forall>i<length ts. (get_source step'', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  then have 2: "set (map ll ts) \<subseteq> ds (fst rr) {ll step', ll step''}" using Cons(1)[OF steps c1 c2] by auto
  have r1: "(get_source step', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto
  have r2: "(get_source step'', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto 
  have 1: "ll t \<in> ds (fst rr) {ll step', ll step''}" using l_imp_ll[OF step r1 r2] unfolding ll_def rr_def by auto 
  show ?case using 1 2 by auto
qed auto
 
lemma l_imp_ll_eq: (* symmetric to l_imp_ll *)
  fixes l r R
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  assumes "l step  \<in> ds (snd r) {l step'}" 
  and "(get_source step',get_source step) \<in> (rstep R)^*"
  shows "ll step \<in> ds (snd rr) {ll step'}"
proof - 
  from assms obtain s rl p \<sigma> t where step_dec: "step = (s,rl,p,\<sigma>,t)" by (metis (erased, opaque_lifting) source_labeling.cases)
  from assms obtain s' rl' p' \<sigma>' t' where step'_dec: "step' = (s',rl',p',\<sigma>',t')" by (metis (erased, opaque_lifting) source_labeling.cases)
  have "(source_labeling step',source_labeling step) \<in> (rstep R)^*" using assms unfolding step_dec step'_dec unfolding get_source_def by auto
  then have l2: "(source_labeling step,source_labeling step') \<in> (snd (sl_rel (R_d R) (R_nd R)))" using l_sl by auto
  then have l1: "(l step,l step') \<in> (snd r)" using assms unfolding ds_def by auto
  then have "(ll step,ll step') \<in> snd rr" using l2 unfolding lex_r_def ll_def rr_def by auto
  then show ?thesis unfolding ds_def by auto
qed

lemma l_imp_ll_seq_eq: (* symmetric to l_imp_ll_seq *)
  fixes l r R
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  assumes "set (map l ss) \<subseteq> ds (snd r) {l step'}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
  shows "set (map ll ss) \<subseteq> ds (snd rr) {ll step'}"
using assms(3-4)
proof (induct ss)
  case (Cons t ts)  
  then have step:"l t \<in> ds (snd r) {l step'}" and steps:"set (map l ts) \<subseteq> ds (snd r) {l step'}" by auto
  from Cons have c1: "\<forall>i<length ts. (get_source step', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  then have 2: "set (map ll ts) \<subseteq> ds (snd rr) {ll step'}" using Cons(1)[OF steps c1] by auto
  have r1: "(get_source step', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto
  have 1: "ll t \<in> ds (snd rr) {ll step'}" using l_imp_ll_eq[OF step r1] unfolding ll_def rr_def by auto 
  show ?case using 1 2 by auto
qed auto
 
lemma r_ast_seq_imp_r_ast: 
  assumes "(s,t) \<in> (rstep R)^*" and "t = first ss" and "ss \<in> seq R" 
  shows "\<forall>i < length (snd ss). (s,get_source ((snd ss)!i)) \<in> (rstep R)^*"
proof -
  from assms obtain ts where ss_dec: "ss = (t,ts)" by (metis first.elims)
  from assms have ?thesis unfolding ss_dec apply auto
  proof (induct ts arbitrary: t )
    case (Cons step steps) 
    from Cons(3) obtain rl p \<sigma> u where step_dec: "step = (t,rl,p,\<sigma>,True,u)"
      using seq.cases by blast
    then have "(t,u) \<in> rstep_r_p_s R rl p \<sigma>" using Cons by (metis (poly_guards_query) seq_chop_first(2))
    then have ast:"(s,u) \<in> (rstep R)^*" by (metis (poly_guards_query) Cons.prems(1) rstep_r_p_s_imp_rstep rtrancl.rtrancl_into_rtrancl)
    then have rst:"(u,steps) \<in> seq R" by (metis Cons.prems(2) seq_chop_first(1) step_dec)
    from Cons(1)[OF ast rst] have 2: "\<forall>i < length steps.(s, get_source (steps ! i)) \<in> (rstep R)\<^sup>*" by auto
    have 1: "(s,get_source (step)) \<in> (rstep R)^*" unfolding step_dec get_source_def using Cons by auto
    show ?case using 1 2 by (metis (erased, opaque_lifting) Cons.prems(3) One_nat_def add.commute add_Suc_right diff_Suc_Suc diff_zero gr0_conv_Suc list.size(4) monoid_add_class.add.right_neutral nat_add_left_cancel_less nth_Cons_pos nth_non_equal_first_eq)
  qed auto
  then show ?thesis unfolding ss_dec by auto
qed

lemma len_append: "\<forall> i < length xs. (xs ! i = (xs @ ys) ! i)" by (metis nth_append)

lemma source_labeling_eld_seq_imp_eld_seq:
  assumes ldc_trs: "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
  and "eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3"
  and fan: "fan R p jl1 jl2 jl3 jr1 jr2 jr3"
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  shows "eld_conv ll rr p jl1 jl2 jl3 jr1 jr2 jr3"
proof -
  {
    fix lp rp ss1 ss2 ss3
    assume  A2:"ELD_1 r (l lp) (l rp) (map l (snd ss1)) (map l (snd ss2)) (map l (snd ss3))"
      and A3a: "ss1 \<in> conv R" and A3b: "ss2 \<in> seq R" and A3c: "ss3 \<in> conv R" and
          A4: "(get_source lp, first ss1) \<in> (rstep R)^*" and A5: "get_source lp = get_source rp"
      and s1: "\<forall>i < length (snd ss1). (get_source lp,get_source ((snd ss1)!i)) \<in> (rstep R)^*"
      and s2: "\<forall>i<length (snd ss2). (get_source rp, get_source (snd ss2 ! i)) \<in> (rstep R)\<^sup>*"
      and s3: "\<forall>i<length (snd ss3). (get_source lp, get_source (snd ss3 ! i)) \<in> (rstep R)\<^sup>*"
    from A2 have l:"length (map l (snd ss2)) \<le> 1" unfolding ELD_1_def by auto
    
    then have 1: "set (map l (snd ss1)) \<subseteq> ds (fst r) {l lp,l lp}" and 
          2: "set (map l (snd ss2)) \<subseteq> ds (snd r) {l rp}" and
          3: "set (map l (snd ss3)) \<subseteq> ds (fst r) {l rp,l lp}" 
      using A2 unfolding ELD_1_def by auto
   
    have s3': "\<forall>i<length (snd ss3). (get_source rp, get_source (snd ss3 ! i)) \<in> (rstep R)\<^sup>*" using s3 A5 by auto 
    have "set (map ll (snd ss1)) \<subseteq> ds (fst rr) {ll lp}" 
      and "set (map ll (snd ss2)) \<subseteq> ds (snd rr) {ll rp}" 
      and "set (map ll (snd ss3)) \<subseteq> ds (fst rr) {ll rp,ll lp}"
      using l_imp_ll_seq[OF 1 s1 s1] using l_imp_ll_seq_eq[OF 2 s2] using l_imp_ll_seq[OF 3 s3' s3] unfolding ll_def rr_def by auto
    then have "ELD_1 rr (ll lp) (ll rp) (map ll (snd ss1)) (map ll (snd ss2)) (map ll (snd ss3))"
       unfolding ELD_1_def using l by auto
  } note F = this
   from assms obtain s rl q \<sigma> t rl2 q2 \<sigma>2 t2 where p_dec: "p = ((s,rl,q,\<sigma>,True,t),(s,rl2,q2,\<sigma>2,True,t2))" 
    and step1: "(s,t) \<in> rstep_r_p_s R rl q \<sigma>" and step2: "(s,t2) \<in> rstep_r_p_s R rl2 q2 \<sigma>2"
    using assms unfolding ldc_trs_def local_peaks_def get_source_def get_target_def by auto
  from assms have ELDl: "ELD_1 r (l (fst p)) (l (snd p)) (map l (snd jl1)) (map l (snd jl2)) (map l (snd jl3))" 
  (*and seql: "jl \<in> seq R"*) unfolding ldc_trs_def eld_conv_def by auto
  have "(get_source (fst p),get_target (fst p)) \<in> rstep R" using step1
    unfolding p_dec get_source_def get_target_def apply auto by (metis rstep_r_p_s_imp_rstep)
  obtain jl where jl: "jl = seq_concat jl1 (seq_concat jl2 jl3)" by auto

   have stepl: "(get_source (fst p), first jl1) \<in> (rstep R)\<^sup>*" using assms unfolding ldc_trs_def 
by (metis (no_types, lifting) \<open>(get_source (fst p), get_target (fst p)) \<in> rstep R\<close> first.simps r_into_rtrancl seq_concat_def) 
  have "(get_source (snd p),get_target (snd p)) \<in> rstep R" using step2
    unfolding p_dec get_source_def get_target_def apply auto by (metis rstep_r_p_s_imp_rstep)
  obtain jr where jr:"jr = seq_concat jr1 (seq_concat jr2 jr3)" by auto

  have stepr: "(get_source (snd p), first jr1) \<in> (rstep R)\<^sup>*" using assms unfolding ldc_trs_def
by (metis (no_types, lifting) \<open>(get_source (snd p), get_target (snd p)) \<in> rstep R\<close> first.simps r_into_rtrancl seq_concat_def)

from assms have ELDr: "ELD_1 r (l (snd p)) (l (fst p)) (map l (snd jr1)) (map l (snd jr2)) (map l (snd jr3))"
  (* and seqr: "jr \<in> seq R"*) unfolding ldc_trs_def eld_conv_def by fast
  have A5: "get_source (fst p) = get_source (snd p)" using ldc_trs unfolding ldc_trs_def local_peaks_def get_source_def by auto

 show ?thesis using ldc_trs unfolding ldc_trs_def local_peaks_def eld_def
    using F[OF ELDl _ _ _ stepl A5] using  F[OF ELDr _ _ _ stepr A5[symmetric]] using assms unfolding ldc_trs_def fan_def
by (simp add: A5 eld_conv_def)
qed
 
(* eld for l implies eld for (l_sn \<times> l) *)
lemma source_labeling_eld_imp_eld:
  assumes "eld_fan R l r p"
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)"
  shows "eldc R ll rr p"
proof -
  from assms obtain jl1 jl2 jl3 jr1 jr2 jr3 where d:"ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3"
 and ELD:"eld_conv l r p jl1 jl2 jl3 jr1 jr2 jr3"
 and fan:"fan R p jl1 jl2 jl3 jr1 jr2 jr3" unfolding eld_fan_def by auto
  show ?thesis using d source_labeling_eld_seq_imp_eld_seq[OF d ELD fan] unfolding ll_def rr_def eldc_def by fast
qed

lemma rel_props_lex:
  assumes "rel_props (fst r1) (snd r1)"
  and   "rel_props (fst r2) (snd r2)"
  defines "r \<equiv> lex_r r1 r2"
  shows  "rel_props (fst r) (snd r)"
proof -
  have t1: "trans (fst r1)"
    and t1': "trans (snd r1)"
    and t2: "trans (fst r2)" 
    and t2': "trans (snd r2)"
    using assms unfolding rel_props_def by auto
  (* transitivity1 *)
  {
    fix x1 x2 y1 y2 z1 z2 
    assume A: "((x1,x2),(y1,y2)) \<in> fst r" and B: "((y1,y2),(z1,z2)) \<in> fst r"
    have "((x1,x2),(z1,z2)) \<in> fst r"
    proof (cases "(x1,y1) \<in> fst r1")
      case True note T1 = this
      then have "(x1,z1) \<in> fst r1"
      proof (cases "(y1,z1) \<in> fst r1")
        case True
        then show ?thesis using T1 t1 trans_def by metis
      next
        case False
        then have T2: "(y1,z1) \<in> snd r1" using B unfolding r_def lex_r_def by auto
        have "(x1,x1) \<in> snd r1" using assms(1) unfolding rel_props_def by (metis UNIV_I refl_on_def)
        then show ?thesis using T1 assms(1) T2 unfolding rel_props_def r_def lex_r_def t1 by auto
      qed
      then show ?thesis unfolding r_def lex_r_def by auto
    next
      case False
      then have T1: "(x1,y1) \<in> snd r1" and T2: "(x2,y2) \<in> fst r2" using A unfolding r_def lex_r_def by auto
      then show ?thesis
      proof (cases "(y1,z1) \<in> fst r1")
      next
        case True
        have T3: "(z1,z1) \<in> snd r1" using assms(1) unfolding rel_props_def by (metis UNIV_I refl_on_def)
        then show ?thesis using T1 True T3 assms(1-2) unfolding rel_props_def r_def lex_r_def by auto
      next
        case False
        then have T3: "(y1,z1) \<in> snd r1" and T4: "(y2,z2) \<in> fst r2" using B unfolding r_def lex_r_def by auto
        have "(x1,z1) \<in> snd r1" using T1 T3 t1' unfolding trans_def by metis
        moreover have "(x2,z2) \<in> fst r2" using T2 T4 t2 unfolding trans_def by metis
        ultimately show ?thesis unfolding  r_def lex_r_def by auto
      qed
    qed
  }
  then have tA: "trans (fst r)" unfolding trans_def by (metis prod.collapse)
  (* transitivity2 *)
  {
    fix x1 x2 y1 y2 z1 z2 (* symmetric of above *) 
    assume A: "((x1,x2),(y1,y2)) \<in> snd r" and B: "((y1,y2),(z1,z2)) \<in> snd r"
    have "((x1,x2),(z1,z2)) \<in> snd r"
    proof (cases "(x1,y1) \<in> fst r1")
      case True note T1 = this
      then have "(x1,z1) \<in> fst r1"
      proof (cases "(y1,z1) \<in> fst r1")
        case True 
        then show ?thesis using T1 t1 unfolding trans_def  by metis 
      next
        case False
        then have T2: "(y1,z1) \<in> snd r1" using B unfolding r_def lex_r_def by auto
        have "(x1,x1) \<in> snd r1" using assms(1) unfolding rel_props_def by (metis UNIV_I refl_on_def)
        then show ?thesis using T1 assms(1) T2 unfolding rel_props_def r_def lex_r_def t1 by auto
      qed
      then show ?thesis unfolding r_def lex_r_def by auto
    next
      case False
      then have T1: "(x1,y1) \<in> snd r1" and T2: "(x2,y2) \<in> snd r2" using A unfolding r_def lex_r_def by auto
      then show ?thesis
      proof (cases "(y1,z1) \<in> fst r1")
        case True
        have T3: "(z1,z1) \<in> snd r1" using assms(1) unfolding rel_props_def by (metis UNIV_I refl_on_def)
        then show ?thesis using T1 True T3 assms(1-2) unfolding rel_props_def r_def lex_r_def by auto
      next
        case False
        then have T3: "(y1,z1) \<in> snd r1" and T4: "(y2,z2) \<in> snd r2" using B unfolding r_def lex_r_def by auto
        have "(x1,z1) \<in> snd r1" using T1 T3 t1' unfolding trans_def by metis
        moreover have "(x2,z2) \<in> snd r2" using T2 T4 t2' unfolding trans_def by metis
        ultimately show ?thesis unfolding  r_def lex_r_def by auto
      qed
    qed
  }
  then have tB: "trans (snd r)"  unfolding trans_def by (metis prod.collapse)
  (* termination *)
  let ?s1 = "(fst r1)\<inverse>"
  let ?ns1 = "(snd r1)\<inverse>"
  let ?s2 = "(fst r2)\<inverse>"
  have SN1: "SN ?s1" using assms unfolding rel_props_def by (metis SN_iff_wf converse_converse)
  have SN2: "SN ?s2" using assms unfolding rel_props_def by (metis SN_iff_wf converse_converse)
  have compat: "?ns1 O ?s1 \<subseteq> ?s1" using assms unfolding rel_props_def refl_on_def by auto
  have SN: "SN (lex_two ?s1 ?ns1 ?s2)" (is "SN ?R") using lex_two[OF compat SN1 SN2] by auto
  then have "?R = ((fst r)\<inverse>)" unfolding r_def lex_r_def by auto
  then have "SN ((fst r)\<inverse>)" using SN unfolding r_def lex_r_def by auto 
  then have wf: "wf ((fst r))" by (metis SN_iff_wf converse_converse)
  (* reflexivity *)
  {
    fix x1 x2
    assume "(x1,x1) \<in> snd r1" and "(x2,x2) \<in> snd r2"
    then have "((x1,x2),(x1,x2)) \<in> snd r" unfolding r_def lex_r_def by auto 
  } note r_key = this
  have r1: "\<forall> x1 \<in> UNIV. (x1,x1) \<in> snd r1"
    using assms unfolding rel_props_def by (metis UNIV_I refl_on_def)
  have r2: "\<forall> x2 \<in> UNIV. (x2,x2) \<in> snd r2"
    using assms unfolding rel_props_def by (metis  UNIV_I refl_on_def)
  have r: "\<forall> (x1,x2) \<in> UNIV. ((x1,x2),x1,x2) \<in> snd r" using r_key r1 r2 by auto 
  then have r: "refl (snd r)" using refl_on_def' by fast 
  (* compatibility *)
  {
    fix x1 x2 y1 y2 z1 z2 v1 v2 
    assume A: "((x1,x2),(y1,y2)) \<in> snd r" and B: "((y1,y2),(z1,z2)) \<in> fst r" and C: "((z1,z2),(v1,v2)) \<in> snd r"
    have D: "((x1,x2),(z1,z2)) \<in> fst r"
    proof (cases "(x1,y1) \<in> fst r1") 
      case True note T1 = this
      show ?thesis
      proof (cases "(y1,z1) \<in> fst r1")
        case True
        then have "(x1,z1) \<in> fst r1" using T1 t1 unfolding trans_def by metis
        then show ?thesis unfolding r_def lex_r_def by auto
      next
        case False
        then have "(y1,z1) \<in> snd r1" using B unfolding r_def lex_r_def by auto
        moreover have "(x1,x1) \<in> snd r1" using assms unfolding rel_props_def by (metis UNIV_I r1)
        ultimately have "(x1,z1) \<in> fst r1" using T1 assms unfolding rel_props_def by auto
        then show ?thesis unfolding r_def lex_r_def by auto
      qed
    next
      case False
      then have T2: "(x1,y1) \<in> snd r1" and W1:"(x2,y2) \<in> snd r2" using A unfolding r_def lex_r_def by auto
      then show ?thesis
      proof (cases "(y1,z1) \<in> fst r1")
        case True
        have "(z1,z1) \<in> snd r1" using assms unfolding rel_props_def by (metis UNIV_I r1)
        then have "(x1,z1) \<in> fst r1" using T2 True assms unfolding rel_props_def by auto
        then show ?thesis unfolding r_def lex_r_def by auto
      next
        case False
        then have "(y1,z1) \<in> snd r1" and W2:"(y2,z2) \<in> fst r2" using B unfolding r_def lex_r_def by auto
        then have k1: "(x1,z1) \<in> snd r1" using T2 t1' unfolding trans_def by metis
        then have "(z2,z2) \<in> snd r2" using assms unfolding rel_props_def by (metis UNIV_I r2)
        then have "(x2,z2) \<in> fst r2" using W1 W2 assms unfolding rel_props_def by auto
        then show ?thesis using k1 unfolding r_def lex_r_def by auto
      qed
    qed
    have "((x1,x2),(v1,v2)) \<in> fst r"
    proof (cases "(x1,z1) \<in> fst r1") 
      case True note T1 = this
      then show ?thesis
      proof (cases "(z1,v1) \<in> fst r1")
        case True
        then have "(x1,v1) \<in> fst r1" using T1 t1 unfolding trans_def by metis
        then show ?thesis unfolding r_def lex_r_def by auto
      next
        case False
        then have T2: "(z1,v1) \<in> snd r1" using C unfolding r_def lex_r_def by auto
        have "(x1,x1) \<in> snd r1" using assms unfolding rel_props_def by (metis UNIV_I r1)
        then have "(x1,v1) \<in> fst r1" using T1 T2 assms unfolding rel_props_def by auto
        then show ?thesis unfolding r_def lex_r_def by auto
      qed
    next
      case False
      then have T1: "(x1,z1) \<in> snd r1" and W0: "(x2,z2) \<in> fst r2" using D unfolding r_def lex_r_def by auto
      then show ?thesis
      proof (cases "(z1,v1) \<in> fst r1")
        case True 
        have "(v1,v1) \<in> snd r1" using assms unfolding rel_props_def by (metis UNIV_I r1)
        then have "(x1,v1) \<in> fst r1" using assms T1 True unfolding rel_props_def by auto
        then show ?thesis unfolding r_def lex_r_def by auto
      next
        case False
        have W2: "(x2,x2) \<in> snd r2" using assms unfolding rel_props_def using UNIV_I r2 by metis
        from False have "(z1,v1) \<in> snd r1" and W1: "(z2,v2) \<in> snd r2" using C unfolding r_def lex_r_def by auto
        then have "(x1,v1) \<in> snd r1" using T1 t1' unfolding trans_def by metis
        moreover have "(x2,v2) \<in> fst r2" using W0 W1 W2 using assms unfolding rel_props_def by auto
        ultimately show ?thesis unfolding r_def lex_r_def by auto
      qed
    qed
  }
  then have compat: "snd r O fst r O snd r \<subseteq> fst r" by auto
  show ?thesis using tA tB wf r compat unfolding rel_props_def by simp
qed
  
lemma SN_rel_has_rel_props:
  assumes SN: "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
  defines "r \<equiv> (sl_rel (R_d R) (R_nd R))" 
  shows "rel_props (fst r) (snd r)"
proof -
  have t1: "trans (fst r)" unfolding r_def sl_rel.simps fst_conv by (metis trans_on_converse trans_trancl)
  have t2: "trans (snd r)" unfolding r_def sl_rel.simps snd_conv by (metis trans_on_converse trans_rtrancl)
  have "SN (((rstep (R_nd R))\<^sup>* O rstep (R_d R) O (rstep (R_nd R))\<^sup>*))" using SN unfolding r_def sl_rel.simps fst_conv by (metis SN_rel_on_def)
  then have wf: "wf (fst r)" unfolding r_def sl_rel.simps fst_conv by (metis SN_iff_wf wf_converse_trancl)
  have r: "refl (snd r)" unfolding r_def sl_rel.simps by (auto intro: refl_rtrancl)
  have compat: "snd r O fst r O snd r \<subseteq> fst r" unfolding r_def apply auto by (metis rel_compat rel_rstep_def)
  show ?thesis unfolding rel_props_def using t1 t2 wf r compat by auto
qed

lemma is_labeling_lex:
  assumes "is_labeling R l1 r1"
  and "is_labeling R l2 r2"
  shows "is_labeling R (\<lambda> step. (l1 step,l2 step)) (lex_r r1 r2)"
using assms unfolding is_labeling_def Let_def lex_r_def by auto

lemma SN_rel_is_labeling:
  "is_labeling R source_labeling (sl_rel (R_d R) (R_nd R))" (is "is_labeling ?R ?l ?r")
proof -
  have eq: "R = (R_d R) \<union> (R_nd R)" unfolding R_d_def R_nd_def by auto 
  show ?thesis using sl_is_labeling eq by metis
qed

 (* similar to l_imp_ll_eq*)
lemma l_imp_ll_eq3:
  fixes l1 l2 r1 r2 R
  defines "ll \<equiv> (\<lambda> step. (l1 step,l2 step))"
  and "rr \<equiv> (lex_r r1 r2)"
  assumes "l1 step \<in> ds (snd r1) {l1 step'}"
  and "l2 step \<in> ds (snd r2) {l2 step'}" 
  and "(get_source step',get_source step) \<in> (rstep R)^*"
  shows "ll step \<in> ds (snd rr) {ll step'}"
unfolding ll_def rr_def using assms unfolding lex_r_def ds_def by auto 
 
 (* similar to ll_imp_ll_seq_eq *)
lemma l_imp_ll_seq_eq3: (* symmetric to l_imp_ll_seq *)
  fixes l1 l r1 r R
  defines "ll \<equiv> (\<lambda> step. (l step,l1 step))"
  and "rr \<equiv> (lex_r r r1)"
  assumes "set (map l ss) \<subseteq> ds (snd r) {l step'}"
  and "set (map l1 ss) \<subseteq> ds (snd r1) {l1 step'}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
  shows "set (map ll ss) \<subseteq> ds (snd rr) {ll step'}"
using assms(3-5)
proof (induct ss)
  case Nil then show ?case by auto
next
  case (Cons t ts)  
  then have step:"l t \<in> ds (snd r) {l step'}" and steps:"set (map l ts) \<subseteq> ds (snd r) {l step'}" by auto
  from Cons have step':"l1 t \<in> ds (snd r1) {l1 step'}" and steps':"set (map l1 ts) \<subseteq> ds (snd r1) {l1 step'}" by auto
  from Cons have c1: "\<forall>i<length ts. (get_source step', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  then have 2: "set (map ll ts) \<subseteq> ds (snd rr) {ll step'}" using Cons(1)[OF steps steps' c1] by auto
  have r1: "(get_source step', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto
  have 1: "ll t \<in> ds (snd rr) {ll step'}" using l_imp_ll_eq3[OF step step' r1] unfolding ll_def rr_def by blast 
  show ?case using 1 2 by auto
qed
 
lemma l_imp_ll3:
  fixes l l1 r r1 R
  defines "ll \<equiv> (\<lambda> step. (l step,l1 step))"
  and "rr \<equiv> (lex_r r r1)"
  assumes "l step  \<in> ds (fst r) {l step', l step''}"
  and "(get_source step',get_source step) \<in> (rstep R)^*"
  and "(get_source step'',get_source step) \<in> (rstep R)^*"
  shows "ll step \<in> ds (fst rr) {ll step', ll step''}"
using assms unfolding ds_def ll_def rr_def lex_r_def by auto
 
 (* similar to l_imp_ll_seq *)
lemma l_imp_ll_seq3:
  fixes l1 l r1 r R
  defines "ll \<equiv> (\<lambda> step. (l step,l1 step))"
  and "rr \<equiv> (lex_r r r1)"
  assumes "set (map l ss) \<subseteq> ds (fst r) {l step',l step''}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
  and "\<forall>i < length ss. (get_source step'',get_source (ss !i)) \<in> (rstep R)^*"
  shows "set (map ll ss) \<subseteq> ds (fst rr) {ll step',ll step''}"
using assms(3-)
proof (induct ss)
  case Nil then show ?case by auto
next
  case (Cons t ts)  
  then have step:"l t \<in> ds (fst r) {l step',l step''}" and steps:"set (map l ts) \<subseteq> ds (fst r) {l step', l step''}" by auto
  from Cons have c1: "\<forall>i<length ts. (get_source step', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  from Cons have c2: "\<forall>i<length ts. (get_source step'', get_source (ts ! i)) \<in> (rstep R)\<^sup>*" by auto
  then have 2: "set (map ll ts) \<subseteq> ds (fst rr) {ll step', ll step''}" using Cons(1)[OF steps (* steps'*) c1 c2] by auto
  have r1: "(get_source step', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto
  have r2: "(get_source step'', get_source t) \<in> (rstep R)\<^sup>*" using Cons assms by auto 
  have 1: "ll t \<in> ds (fst rr) {ll step', ll step''}" using l_imp_ll3[OF step  r1 r2] unfolding ll_def rr_def by fast
  show ?case using 1 2 by auto
qed

(* new begin*)
lemma conv_concat_map:
assumes "conv_concat ss1 ss2 = ss" 
shows "map l (snd ss1)@map l (snd ss2) = map l (snd ss)" proof -
from assms obtain x xs y ys where ss1_dec: "(x,xs) = ss1" and ss2_dec: "(y,ys) = ss2" using prod.collapse by blast
show ?thesis unfolding assms[symmetric] conv_concat_def ss1_dec[symmetric] ss2_dec[symmetric] by auto
qed

lemma conv_concat_left_empty:
shows "conv_concat (first ss2,[]) ss2 = ss2" proof -
obtain y ys where ss2_dec: "(y,ys) = ss2" using prod.collapse by blast
show ?thesis unfolding conv_concat_def unfolding ss2_dec[symmetric] first.simps by auto
qed

lemma eld_seq_and_weld_seq_imp_eld_seq2:
  assumes diamond_trs: "diamond_trs R p jl jr" 
  and eld_conv: "eld_conv l1 r1 p (first jl,[]) jl (last jl,[]) (first jr,[]) jr (last jr,[])" (is "eld_conv _ _ _ ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3")
  and weld_seq: "weld_seq l2 r2 p jl jr"
  shows "eld_conv (\<lambda> step. (l1 step,l2 step)) (lex_r r1 r2) p (first jl,[]) jl (last jl,[]) (first jr,[]) jr (last jr,[])" 
  (is "eld_conv ?l ?r p  _ _ _ _ _ _")  proof -
 have a: "ELD_1 r1 (l1 (fst p)) (l1 (snd p)) (map l1 (snd ?jl1)) (map l1 (snd ?jl2)) (map l1 (snd ?jl3))" using eld_conv unfolding eld_conv_def by auto 
 have b: "ELD_1 r2 (l2 (fst p)) (l2 (snd p)) (map l2 (snd ?jl1)) (map l2 (snd ?jl2)) (map l2 (snd ?jl3))" using weld_seq unfolding weld_seq_def 
  by (metis (no_types, lifting) ELD_1_def Nil_is_map_conv a bot_least labels_def length_map list.set(1) snd_conv subsetI)
 have 1: "ELD_1 (lex_r r1 r2) (l1 (fst p), l2 (fst p)) (l1 (snd p), l2 (snd p)) (map ?l (snd ?jl1)) (map ?l (snd ?jl2)) (map ?l (snd ?jl3))"
 proof -
  have x1: "length (map (\<lambda>step. (l1 step, l2 step)) (snd jl)) \<le> 1"
    using eld_conv weld_seq unfolding eld_conv_def weld_seq_def by (metis (mono_tags, lifting) diamond_trs diamond_trs_def length_map)
  have x2: "set (map (\<lambda>step. (l1 step, l2 step)) (snd jl)) \<subseteq> ds (snd (lex_r r1 r2)) {(l1 (snd p), l2 (snd p))}"
    using eld_conv weld_seq unfolding eld_conv_def weld_seq_def proof (cases "length (snd jl) = 0")
     case True then show ?thesis using eld_conv weld_seq eld_conv_def weld_seq_def by auto
     next
     case False then have length: "length (snd jl) = 1" using diamond_trs unfolding diamond_trs_def using Decreasing_Diagrams2.seq.simps One_nat_def ldc_trs_def le_antisym le_numeral_extra(4) length_0_conv list.size(4) prod.collapse trans_le_add2 by linarith
     then obtain elt elts where "(snd jl) = elt#elts" by (metis (mono_tags, lifting) False last.elims length_0_conv snd_conv)
     then have elt: "(snd jl) = [elt]" using length by auto
      have 1: "l1 elt \<in> under (snd r1) (l1 (snd p))" using eld_conv unfolding ELD_1_def eld_conv_def elt by auto
      have "(\<forall>a\<in>labels l2 jl. a \<in> ds (snd r2) {l2 (snd p)})" using weld_seq unfolding weld_seq_def by auto
      then have "(l2 elt) \<in> {y. \<exists>x\<in>{l2 (snd p)}. (y, x) \<in> snd r2}" unfolding under_def ds_def unfolding labels_def elt by auto 
      then have 2: "l2 elt \<in> under (snd r2) (l2 (snd p))" unfolding under_def ds_def unfolding labels_def elt by auto 
      then show ?thesis using 1 unfolding elt ds_def under_def apply auto unfolding lex_r_def by auto 
     qed
 show ?thesis using x1 x2 unfolding ELD_1_def by auto
qed
(* ugly copy *)
 have a: "ELD_1 r1 (l1 (snd p)) (l1 (fst p)) (map l1 (snd ?jr1)) (map l1 (snd ?jr2)) (map l1 (snd ?jr3))" using eld_conv unfolding eld_conv_def by blast
 have b: "ELD_1 r2 (l2 (snd p)) (l2 (fst p)) (map l2 (snd ?jr1)) (map l2 (snd ?jr2)) (map l2 (snd ?jr3))" using weld_seq unfolding weld_seq_def
  by (metis ELD_1_def a bot_least labels_def length_map list.map_disc_iff list.set(1) snd_conv subsetI)
 have 2: "ELD_1 (lex_r r1 r2) (l1 (snd p), l2 (snd p)) (l1 (fst p), l2 (fst p)) (map ?l (snd ?jr1)) (map ?l (snd ?jr2)) (map ?l (snd ?jr3))"
 proof -
  have x1: "length (map (\<lambda>step. (l1 step, l2 step)) (snd jr)) \<le> 1"
    using eld_conv weld_seq unfolding eld_conv_def weld_seq_def by (metis (mono_tags, lifting) diamond_trs diamond_trs_def length_map)
  have x2: "set (map (\<lambda>step. (l1 step, l2 step)) (snd jr)) \<subseteq> ds (snd (lex_r r1 r2)) {(l1 (fst p), l2 (fst p))}"
    using eld_conv weld_seq unfolding eld_conv_def weld_seq_def proof (cases "length (snd jr) = 0")
     case True then show ?thesis using eld_conv weld_seq eld_conv_def weld_seq_def by auto
     next
     case False then have length: "length (snd jr) = 1" using diamond_trs unfolding diamond_trs_def using Decreasing_Diagrams2.seq.simps One_nat_def ldc_trs_def le_antisym le_numeral_extra(4) length_0_conv list.size(4) prod.collapse trans_le_add2 by linarith
     then obtain elt elts where "(snd jr) = elt#elts" by (metis (mono_tags, lifting) False last.elims length_0_conv snd_conv)
     then have elt: "(snd jr) = [elt]" using length by auto
      have 1: "l1 elt \<in> under (snd r1) (l1 (fst p))" using eld_conv unfolding ELD_1_def eld_conv_def elt by auto
      have "(\<forall>a\<in>labels l2 jr. a \<in> ds (snd r2) {l2 (fst p)})" using weld_seq unfolding weld_seq_def by auto
      then have "(l2 elt) \<in> {y. \<exists>x\<in>{l2 (fst p)}. (y, x) \<in> snd r2}" unfolding under_def ds_def unfolding labels_def elt by auto 
      then have 2: "l2 elt \<in> under (snd r2) (l2 (fst p))" unfolding under_def ds_def unfolding labels_def elt by auto 
      then show ?thesis using 1 unfolding elt ds_def under_def apply auto unfolding lex_r_def by auto 
     qed
 show ?thesis using x1 x2 unfolding ELD_1_def by auto
 qed
then show ?thesis using 1 2 unfolding eld_conv_def by auto
qed

(* new end*)

lemma eld_seq_and_weld_seq_imp_eld_seq:
  assumes "ld2_trs R p jl jr"
  and eld_conv: "eld_conv l1 r1 p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])" (is "eld_conv _ _ _ ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3")
  and weld_seq: "weld_seq l2 r2 p jl jr"
  shows "eld_conv (\<lambda> step. (l1 step,l2 step)) (lex_r r1 r2) p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])" (is "eld_conv ?l ?r _ _ _ _ _ _ _")
proof -
 from assms have l1: "ELD_1 r1 (l1 (fst p)) (l1 (snd p)) (map l1 (snd ?jl1)) (map l1 (snd ?jl2)) (map l1 (snd ?jl3))"unfolding eld_conv_def by auto
  
  then have f1:"ELD_1 ?r (?l (fst p)) (?l (snd p)) (map ?l (snd ?jl1)) (map ?l (snd ?jl2)) (map ?l (snd ?jl3))" using assms(3) unfolding
  weld_seq_def ELD_1_def apply auto unfolding lex_r_def under_def ds_def by auto

  from assms have x: "ELD_1 r1 (l1 (snd p)) (l1 (fst p)) (map l1 (snd ?jr1)) (map l1 (snd ?jr2)) (map l1 (snd ?jr3))" unfolding eld_conv_def by auto
  from assms have "length (snd jr) \<le> 1" unfolding ld2_trs_def by auto


  (*ugly copy 2*)
 have a: "ELD_1 r1 (l1 (snd p)) (l1 (fst p)) (map l1 (snd ?jr1)) (map l1 (snd ?jr2)) (map l1 (snd ?jr3))" using eld_conv unfolding eld_conv_def by blast
 have b: "ELD_1 r2 (l2 (snd p)) (l2 (fst p)) (map l2 (snd ?jr1)) (map l2 (snd ?jr2)) (map l2 (snd ?jr3))" using weld_seq unfolding weld_seq_def
  by (metis ELD_1_def a bot_least labels_def length_map list.map_disc_iff list.set(1) snd_conv subsetI)
 have 2: "ELD_1 (lex_r r1 r2) (l1 (snd p), l2 (snd p)) (l1 (fst p), l2 (fst p)) (map ?l (snd ?jr1)) (map ?l (snd ?jr2)) (map ?l (snd ?jr3))"
 proof -
  have x1: "length (map (\<lambda>step. (l1 step, l2 step)) (snd jr)) \<le> 1" using assms unfolding ld2_trs_def by auto

  have x2: "set (map (\<lambda>step. (l1 step, l2 step)) (snd jr)) \<subseteq> ds (snd (lex_r r1 r2)) {(l1 (fst p), l2 (fst p))}"
    using eld_conv weld_seq unfolding eld_conv_def weld_seq_def proof (cases "length (snd jr) = 0")
     case True then show ?thesis using eld_conv weld_seq eld_conv_def weld_seq_def by auto
     next
     case False then have length: "length (snd jr) = 1" using x1 using One_nat_def \<open>length (snd jr) \<le> 1\<close> dual_order.antisym last.elims le_numeral_extra(4) length_0_conv list.size(4) snd_conv trans_le_add2 by linarith

     then obtain elt elts where "(snd jr) = elt#elts" by (metis (mono_tags, lifting) False last.elims length_0_conv snd_conv)
     then have elt: "(snd jr) = [elt]" using length by auto
      have 1: "l1 elt \<in> under (snd r1) (l1 (fst p))" using eld_conv unfolding ELD_1_def eld_conv_def elt by auto
      have "(\<forall>a\<in>labels l2 jr. a \<in> ds (snd r2) {l2 (fst p)})" using weld_seq unfolding weld_seq_def by auto
      then have "(l2 elt) \<in> {y. \<exists>x\<in>{l2 (fst p)}. (y, x) \<in> snd r2}" unfolding under_def ds_def unfolding labels_def elt by auto 
      then have 2: "l2 elt \<in> under (snd r2) (l2 (fst p))" unfolding under_def ds_def unfolding labels_def elt by auto 
      then show ?thesis using 1 unfolding elt ds_def under_def apply auto unfolding lex_r_def by auto 
     qed
 show ?thesis using x1 x2 unfolding ELD_1_def by auto
 qed
  then have f2:"ELD_1 ?r (?l (snd p)) (?l (fst p)) (map ?l (snd ?jr1)) (map ?l (snd ?jr2)) (map ?l (snd ?jr3))" using assms(3) unfolding
  weld_seq_def ELD_1_def by auto
 from f1 f2 show ?thesis unfolding eld_conv_def by auto
qed
 
(* (* this direction is currently not used *) 
 (* similar to l_imp_ll_seq *)
lemma l_imp_ll_seq2:
 fixes l1 l r1 r R
 defines "ll \<equiv> (\<lambda> step. (l1 step,l step))"
 and "rr \<equiv> (lex_r r1 r)"
 assumes "set (map l ss) \<subseteq> ds (fst r) {l step',l step''}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
  and "\<forall>i < length ss. (get_source step'',get_source (ss !i)) \<in> (rstep R)^*"
 shows "set (map ll ss) \<subseteq> ds (fst rr) {ll step',ll step''}" s o r r y
 
  (* similar to ll_imp_ll_seq_eq *)
lemma l_imp_ll_seq_eq2: (* symmetric to l_imp_ll_seq *)
 fixes l1 l r1 r R
 defines "ll \<equiv> (\<lambda> step. (l1 step,l step))"
 and "rr \<equiv> (lex_r r1 r)"
 assumes "set (map l ss) \<subseteq> ds (snd r) {l step'}"
  and "\<forall>i < length ss. (get_source step' ,get_source (ss !i)) \<in> (rstep R)^*"
   shows "set (map ll ss) \<subseteq> ds (snd rr) {ll step'}" s o r r y


 
lemma weld_seq_and_eld_seq_imp_eld_seq:
 assumes "ld2_trs R p jl jr" "eld_seq l2 r2 p jl jr" and "weld_seq l1 r1 p jl jr"
 shows "eld_seq (\<lambda> step. (l1 step,l2 step)) (lex_r r1 r2) p jl jr" (is "eld_seq ?l ?r _ _ _") proof -
 (* from eld_seq_imp_eld_seq *)
  {fix l1 l2 r1 r2 jl \<sigma>1 \<sigma>2 \<sigma>3 lp rp ss
    assume A1: "map l2 (snd ss) = \<sigma>1@\<sigma>2@\<sigma>3" and A2:"ELD_1 r2 (l2 lp) (l2 rp) \<sigma>1 \<sigma>2 \<sigma>3"
     and A3: "ss \<in> seq R" and A4: "(get_source lp, first ss) \<in> (rstep R)^*" and A5: "get_source lp = get_source rp"

   from A2 have l:"length \<sigma>2 \<le> 1" unfolding ELD_1_def by auto
    let ?l = "\<lambda>step. (l1 step, l2 step)"
  from A1 obtain ss1 ss2 ss3 where ss_dec:"snd ss = ss1@ss2@ss3" and dec1: "map l2 ss1 = \<sigma>1" and dec2: "map l2 ss2 = \<sigma>2"  and dec3:"map l2 ss3 = \<sigma>3" 
   using map_dec by metis
  hence 1: "set (map l2 ss1) \<subseteq> ds (fst r2) {l2 lp,l2 lp}" and 2: "set (map l2 ss2) \<subseteq> ds (snd r2) {l2 rp}" and 3: "set (map l2 ss3) \<subseteq> ds (fst r2) {l2 rp,l2 lp}" 
   using A2 unfolding ELD_1_def by auto
   
  hence ll_dec: "map ?l (snd ss) = (map ?l ss1)@(map ?l ss2)@(map ?l ss3)" using ss_dec by (metis map_append)
  have l: "length (map ?l ss2) \<le> 1" using l dec2 by auto
  
  have seq:"\<forall>i < length (snd ss). (get_source lp,get_source ((snd ss)!i)) \<in> (rstep R)^*" using r_ast_seq_imp_r_ast[OF A4 _ A3] by fast
  have s1: "\<forall>i<length ss1. (get_source lp, get_source (ss1 ! i)) \<in> (rstep R)\<^sup>*" apply auto proof - 
   fix i assume A: "i < length ss1" 
    hence eq: "((ss1@ss2@ss3)!i) = (ss1!i)" using nth_append by metis
    thus "(get_source lp, get_source (ss1 !i)) \<in> (rstep R)^*" using seq unfolding ss_dec A unfolding get_source_def eq 
     apply auto by (metis (erased, opaque_lifting) A add.commute len_append trans_less_add2)
  qed
  have s2: "\<forall>i<length ss2. (get_source rp, get_source (ss2 ! i)) \<in> (rstep R)\<^sup>*" apply auto proof -
   fix i assume A: "i < length ss2"
   hence eq: "((ss1@ss2@ss3)!(length ss1+i)) =  (ss2!i)" by (metis len_append nth_append_length_plus)
       thus "(get_source rp, get_source (ss2 !i)) \<in> (rstep R)^*" using seq unfolding ss_dec A A5 unfolding get_source_def eq 
     apply auto by (metis (erased, opaque_lifting) A eq le_add1 less_le_trans nat_add_left_cancel_less)
  qed
  have s3: "\<forall>i<length ss3. (get_source lp, get_source (ss3 ! i)) \<in> (rstep R)\<^sup>*" apply auto proof -
   fix i assume A: "i < length ss3"
   hence eq: "((ss1@ss2@ss3)!(length (ss1@ss2)+i)) =  (ss3!i)" using List.append_assoc[symmetric] by (metis len_append nth_append_length_plus append_assoc)
       thus "(get_source lp, get_source (ss3 !i)) \<in> (rstep R)^*" using seq unfolding ss_dec A unfolding get_source_def eq List.append_assoc[symmetric]
       by (metis (erased, opaque_lifting) A length_append nat_add_left_cancel_less)
  qed
  have s3': "\<forall>i<length ss3. (get_source rp, get_source (ss3 ! i)) \<in> (rstep R)\<^sup>*" using s3 A5 by auto 


  have "set (map (\<lambda>step. (l1 step, l2 step)) ss1) \<subseteq> ds (fst (lex_r r1 r2)) {(\<lambda>step. (l1 step, l2 step)) lp,(\<lambda>step. (l1 step, l2 step)) lp}" using l_imp_ll_seq2[OF 1 s1 s1] by fast
  hence "set (map ?l ss1) \<subseteq> ds (fst (lex_r r1 r2)) {?l lp}" by auto
  moreover have "set (map ?l ss2) \<subseteq> ds (snd (lex_r r1 r2)) {?l rp}" using l_imp_ll_seq_eq2[OF 2 s2] by fast
  moreover have "set (map ?l ss3) \<subseteq> ds (fst (lex_r r1 r2)) {?l rp,?l lp}" using l_imp_ll_seq2[OF 3 s3' s3] by metis
  ultimately have "\<exists> s1 s2 s3. (map ?l (snd ss) = s1@s2@s3 \<and> ELD_1 (lex_r r1 r2) (?l lp) (?l rp) s1 s2 s3)"  unfolding ll_dec ELD_1_def using l by fast
 } note F = this
  from assms obtain s rl q \<sigma> t rl2 q2 \<sigma>2 t2 where p_dec: "p = ((s,rl,q,\<sigma>,t),(s,rl2,q2,\<sigma>2,t2))" 
   and step1: "(s,t) \<in> rstep_r_p_s R rl q \<sigma>" and step2: "(s,t2) \<in> rstep_r_p_s R rl2 q2 \<sigma>2" using assms unfolding ld2_trs_def ldc_trs_def local_peaks_def get_source_def get_target_def by auto
  from assms obtain \<sigma>1 \<sigma>2 \<sigma>3 where decl: "map l2 (snd jl) = \<sigma>1@\<sigma>2@\<sigma>3" 
   and ELDl: "ELD_1 r2 (l2 (fst p)) (l2 (snd p)) \<sigma>1 \<sigma>2 \<sigma>3" and seql: "jl \<in> seq R" unfolding ld2_trs_def ldc_trs_def eld_seq_def by fast
  have "(get_source (fst p),get_target (fst p)) \<in> rstep R" using step1 unfolding p_dec get_source_def get_target_def apply auto by (metis rstep_r_p_s_imp_rstep)
  hence stepl: "(get_source (fst p), first jl) \<in> (rstep R)\<^sup>*" using assms unfolding ld2_trs_def ldc_trs_def by auto
  have "(get_source (snd p),get_target (snd p)) \<in> rstep R" using step2 unfolding p_dec get_source_def get_target_def apply auto by (metis rstep_r_p_s_imp_rstep)
  hence stepr: "(get_source (snd p), first jr) \<in> (rstep R)\<^sup>*" using assms unfolding ld2_trs_def ldc_trs_def by auto
  from assms obtain \<tau>1 \<tau>2 \<tau>3 where decr: "map l2 (snd jr) = \<tau>1@\<tau>2@\<tau>3" 
   and ELDr: "ELD_1 r2 (l2 (snd p)) (l2 (fst p)) \<tau>1 \<tau>2 \<tau>3" and seqr: "jr \<in> seq R" unfolding ld2_trs_def ldc_trs_def eld_seq_def by fast
 have A5: "get_source (fst p) = get_source (snd p)" using assms unfolding ld2_trs_def ldc_trs_def local_peaks_def get_source_def by auto
   show ?thesis unfolding ldc_trs_def local_peaks_def eld_seq_def 
   using F[OF decl ELDl seql stepl A5] F[OF decr ELDr seqr stepr A5[symmetric]] by fast
 qed
  *)
 
lemma SN_rel_diamond_trs_imp_eld_seq:
  assumes "diamond_trs R p jl jr"
  shows "eld_conv source_labeling (sl_rel (R_d R) (R_nd R)) p (get_target (fst p),[]) jl (last jl,[]) (get_target (snd p),[]) jr (last jr,[])" (is "eld_conv ?l ?r _ ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3")
proof -
  have "ldc_trs R p ?jl1 ?jl2 ?jl3 ?jr1 ?jr2 ?jr3" and l1: "length (snd jl) \<le> 1" and l2: "length (snd jr) \<le> 1"
    using assms unfolding diamond_trs_def by auto
  obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u where p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))"
    using assms unfolding local_peaks_def diamond_trs_def ldc_trs_def by blast
  have st: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" and su: "(s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2"
    using assms unfolding local_peaks_def diamond_trs_def ldc_trs_def p_dec by auto
  have jl: "jl \<in> seq R" and jr: "jr \<in> seq R" using assms unfolding ldc_trs_def diamond_trs_def by auto
  have eq: "fst jl = first jl" by (metis first.simps prod.collapse)
  have step: "(s,t) \<in> (rstep R)^*" using st by (metis r_into_rtrancl rstep_r_p_s_imp_rstep)
  then have ast:"(s,fst jl) \<in> (rstep R)^*" using assms
    unfolding diamond_trs_def ldc_trs_def p_dec get_target_def eq[symmetric] by auto
  have "\<forall>i < length (snd jl). (s,get_source ((snd jl)!i)) \<in> (rstep R)^*"
    using r_ast_seq_imp_r_ast[OF ast eq jl] by auto
  then have la: "set (map ?l (snd jl)) \<subseteq> ds (snd ?r) {?l (snd p)}"
    unfolding p_dec ds_def get_source_def apply auto 
    by (metis (no_types, opaque_lifting) R_d_union_R_nd fst_conv in_set_conv_nth inf_sup_aci(5) rstep_union)
  have 1: "ELD_1 ?r (?l (fst p)) (?l (snd p)) [] (map ?l (snd jl)) []"
    using la l1 unfolding ELD_1_def by auto
  (* symmetric *)
  have eq: "fst jr = first jr" by (metis first.simps prod.collapse)
  have step: "(s,u) \<in> (rstep R)^*" using su by (metis r_into_rtrancl rstep_r_p_s_imp_rstep)
  then have ast:"(s,fst jr) \<in> (rstep R)^*"
    using assms unfolding diamond_trs_def ldc_trs_def p_dec get_target_def eq[symmetric] by auto
  have "\<forall>i < length (snd jr). (s,get_source ((snd jr)!i)) \<in> (rstep R)^*"
    using r_ast_seq_imp_r_ast[OF ast eq jr] by auto
  then have lb: "set (map ?l (snd jr)) \<subseteq> ds (snd ?r) {?l (fst p)}"
    unfolding p_dec ds_def get_source_def apply auto 
    by (metis (no_types, opaque_lifting) R_d_union_R_nd fst_conv in_set_conv_nth inf_sup_aci(5) rstep_union)
  have 2: "ELD_1 ?r (?l (snd p)) (?l (fst p)) [] (map ?l (snd jr)) []"
    using lb l2 unfolding ELD_1_def by auto
  show ?thesis using 1 2 assms unfolding eld_conv_def diamond_def using list.simps(8) snd_conv by auto
qed

lemma SN_rel_ld2_trs_imp_eld_seq: 
  assumes "ld2_trs R p jl jr" "length (snd jl) > 1"
  and "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
  shows "eld_conv source_labeling (sl_rel (R_d R) (R_nd R)) p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])"
 (is "eld_conv ?l ?r _ _ _ _ _ _ _")
proof - 
  show ?thesis proof (cases "diamond_trs R p jl jr")
    case True then show ?thesis using assms(2) unfolding diamond_trs_def by auto 
  next
    case False 
    {
      fix p
      assume d2: "ld2_trs R p jl jr" 
      (* copy from SN_rel_diamond_trs_imp_eld_seq *)
      obtain s rl1 p1 \<sigma>1 t rl2 p2 \<sigma>2 u where p_dec: "p = ((s,rl1,p1,\<sigma>1,True,t),(s,rl2,p2,\<sigma>2,True,u))"
        using d2 unfolding ld2_trs_def local_peaks_def diamond_trs_def ldc_trs_def by blast
      have st: "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" and su: "(s,u) \<in> rstep_r_p_s R rl2 p2 \<sigma>2"
        using d2 unfolding ld2_trs_def local_peaks_def diamond_trs_def ldc_trs_def p_dec by auto
      have jl: "jl \<in> seq R" and jr: "jr \<in> seq R" using d2 unfolding ld2_trs_def ldc_trs_def diamond_trs_def
        by auto
      have l1: "length (snd jr) \<le> 1" using d2 unfolding ld2_trs_def by auto
      have eq: "fst jr = first jr" by (metis first.simps prod.collapse)
      have step: "(s,u) \<in> (rstep R)^*" using su by (metis r_into_rtrancl rstep_r_p_s_imp_rstep)
      then have ast:"(s,fst jr) \<in> (rstep R)^*" using d2
        unfolding ld2_trs_def diamond_trs_def ldc_trs_def p_dec get_target_def eq[symmetric] by auto
      have "\<forall>i < length (snd jr). (s,get_source ((snd jr)!i)) \<in> (rstep R)^*"
        using r_ast_seq_imp_r_ast[OF ast eq jr] by auto
      then have la: "set (map ?l (snd jr)) \<subseteq> ds (snd ?r) {?l (fst p)}"
        unfolding p_dec ds_def get_source_def apply auto 
        by (metis (no_types, opaque_lifting) R_d_union_R_nd fst_conv in_set_conv_nth inf_sup_aci(5) rstep_union)
      have 1: "ELD_1 ?r (?l (snd p)) (?l (fst p)) [] (map ?l (snd jr)) []"
        using la l1 unfolding ELD_1_def by auto
      have 2: "ELD_1 ?r (?l (fst p)) (?l (snd p)) (map ?l (snd jl)) [] []"
      proof (cases "length (snd jl) \<le> 1")
        case True then show ?thesis using assms(2) unfolding diamond_trs_def by auto
(*
        have eq: "fst jl = first jl" by (metis first.simps prod.collapse)
        have step: "(s,t) \<in> (rstep R)^*" using st by (metis r_into_rtrancl rstep_r_p_s_imp_rstep)
        hence ast:"(s,fst jl) \<in> (rstep R)^*" using d2 unfolding ld2_trs_def diamond_trs_def ldc_trs_def p_dec get_target_def eq[symmetric] by auto
        have "\<forall>i < length (snd jl). (s,get_source ((snd jl)!i)) \<in> (rstep R)^*" using r_ast_seq_imp_r_ast[OF ast eq jl] by auto
        hence la: "set (map ?l (snd jl)) \<subseteq> ds (snd ?r) {?l (snd p)}" unfolding p_dec ds_def get_source_def apply auto 
          by (metis (no_types, opaque_lifting) R_d_union_R_nd fst_conv in_set_conv_nth inf_sup_aci(5) rstep_union)
        have "ELD_1 ?r (?l (fst p)) (?l (snd p)) [] (map ?l (snd jl)) []" using la True unfolding ELD_1_def by (metis empty_subsetI length_map list.set(1))
        thus ?thesis by (metis append_Nil append_Nil2)
*)
      next
        case False then have nl: "\<not> linear_term (snd (get_rule (fst p)))" using d2 unfolding ld2_trs_def by auto
        have "(s,t) \<in> rstep_r_p_s R rl1 p1 \<sigma>1" using st by auto
        then have x: "(s,t) \<in> rstep_r_p_s (R_d R \<union> R_nd R) rl1 p1 \<sigma>1" unfolding R_d_def R_nd_def by (metis R_d_def R_d_union_R_nd R_nd_def)
        then have "(s,t) \<in> rstep_r_p_s (R_d R) rl1 p1 \<sigma>1"
        proof (cases "rl1 \<in> R_d R")
          case True then show ?thesis using x unfolding R_d_def rstep_r_p_s_def by auto
        next
          case False 
          have "rl1 \<in> R" using st unfolding rstep_r_p_s_def apply auto by metis  
          then have "rl1 \<in> R_nd R" using False unfolding R_d_def R_nd_def by auto
          then show ?thesis using nl unfolding p_dec get_rule_def R_nd_def by auto
        qed
        then have st2: "(s,t) \<in> rstep (R_d R)" by (metis rstep_r_p_s_imp_rstep)
        then have "(t,s) \<in> fst ?r" unfolding sl_rel.simps by auto
        from st2 have st3: "(s,t) \<in> (relto (rstep (R_d R)) (rstep (R_nd R)))^+" by auto
        have uu: "(t,t) \<in> (rstep R)^*" by auto
        have eq: "t = first jl" using d2 unfolding ld2_trs_def ldc_trs_def unfolding p_dec get_target_def by auto 
        from r_ast_seq_imp_r_ast[OF uu eq jl] have y: "\<forall>i<length (snd jl). (t, get_source (snd jl ! i)) \<in> (rstep R)\<^sup>*" by auto
        {
          fix i assume A: "i < length (snd jl)"
          have "(t,get_source (snd jl !i)) \<in> (rstep R)^*" (is "(t,?v) \<in> _") using A y by auto
          then have l: "(t,?v) \<in> (rstep (R_d R) \<union> rstep (R_nd R))^*" by (metis R_d_union_R_nd rstep_union)
          have k: "(rstep (R_d R) \<union> rstep (R_nd R))^* \<subseteq> ((rstep (R_nd R))^* \<union> (relto (rstep (R_d R)) (rstep (R_nd R)))^*)" by regexp
          then have "(t,?v) \<in> (relto (rstep (R_d R)) (rstep (R_nd R)))^* \<or> (t,?v) \<in> (rstep (R_nd R))^*" using l by auto 
          then have "(?v, s) \<in> fst (sl_rel (R_d R) (R_nd R))" using st3 apply auto by (metis RS_S_trancl)
        } 
        then have "\<forall>i<length (snd jl). (get_source (snd jl ! i),s) \<in> (fst ?r)"  using y by auto
        then have "set (map ?l (snd jl)) \<subseteq> ds (fst ?r) {?l (fst p)}" unfolding p_dec get_source_def ds_def apply auto by (metis fst_conv in_set_idx)
        then show ?thesis unfolding ELD_1_def by auto 
      qed
(*
      { assume ?two1
        then have "eld_conv source_labeling ?r p (first jl,[]) jl (last jl,[]) (last jr,[]) jr (last jr,[])" (is "?a") 
         using 1 unfolding eld_conv_def by auto
      } note T1 = this
      { assume ?two2
        then have "eld_conv source_labeling ?r p  jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])" (is "?b")
         using 1 unfolding eld_conv_def by auto
      } note T2 = 
*)
     have "eld_conv source_labeling ?r p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])" 
     using 1 2 unfolding eld_conv_def by auto 
    } note * = this
    from assms have ld2_trs: "ld2_trs R p jl jr" unfolding ld2_trs_def by auto
    show ?thesis using *[OF ld2_trs] by (simp add: eld_conv_def)
  qed
qed

lemma SN_rel_compatible:
  assumes wll: "weakly_compatible R l r" 
  and SN: "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
  and ll: "left_linear_trs R"
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)" (is "_ \<equiv> lex_r ?r1 _")
  shows "compatible R ll rr"
unfolding compatible_def
proof
  from wll show "is_labeling R ll rr" unfolding ll_def rr_def weakly_compatible_def
    using is_labeling_lex SN_rel_is_labeling by blast
  show "\<forall>p. variable_peak R p \<or> parallel_peak R p \<longrightarrow> eldc R ll rr p"
  proof (intro allI impI)
    fix p
    assume A: "variable_peak R p \<or> parallel_peak R p"
    then have "weld R l r p" using wll ll unfolding weakly_compatible_def by blast
    then obtain jl jr where d2: "ld2_trs R p jl jr" and weld_seq:"weld_seq l r p jl jr"
      unfolding weld_def by blast
    (*new start*)
    have cases: "length (snd jl) \<le> 1 \<or> 1 < length (snd jl)" (is "?case1 \<or> ?case2")  by auto
    { assume ?case1
      then have diamond: "diamond_trs R p jl jr" using d2 unfolding diamond_trs_def ld2_trs_def by auto
      have eld: "eld_conv source_labeling (sl_rel (R_d R) (R_nd R)) p (first jl, []) jl (last jl, []) (first jr, []) jr (last jr, [])"
        using SN_rel_diamond_trs_imp_eld_seq[OF diamond] diamond unfolding diamond_trs_def ldc_trs_def by auto
      have "eld_conv ll rr p (first jl,[]) jl (last jl,[]) (first jr,[]) jr (last jr,[])" 
      using eld_seq_and_weld_seq_imp_eld_seq2[OF diamond eld weld_seq] unfolding ll_def rr_def by auto
    } note 1 = this
    { assume case2: ?case2
      have eld_conv: "eld_conv source_labeling (sl_rel (R_d R) (R_nd R)) p jl (last jl, []) (last jl, []) (first jr, []) jr (last jr, [])"
        using SN_rel_ld2_trs_imp_eld_seq[OF d2 case2 SN] by auto
      have "eld_conv ll rr p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])" 
        using eld_seq_and_weld_seq_imp_eld_seq[OF d2 eld_conv weld_seq] unfolding ll_def rr_def by auto
    } note 2 = this
    (*new end*)
    from d2 have "ldc_trs R p  jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[])"
      by (simp add: ldc_trs_def seq.intros(1) seq_imp_conv ld2_trs_def)
    moreover have "ldc_trs R p (first jl,[]) jl (last jl,[]) (first jr,[]) jr (last jr,[])"
      using d2 unfolding ld2_trs_def ldc_trs_def by auto
    moreover have "eld_conv ll rr p jl (last jl,[]) (last jl,[]) (first jr,[]) jr (last jr,[]) \<or> 
      eld_conv ll rr p (first jl,[]) jl (last jl,[]) (first jr,[]) jr (last jr,[])"
      using 1 2 cases by auto
    ultimately show "eldc R ll rr p" unfolding eldc_def by blast
  qed
qed

lemma SN_rel_lex:
  assumes wll: "weakly_compatible R l r"
  and rp: "rel_props (fst r) (snd r)"
  and SN: "SN_rel (rstep (R_d R)) (rstep (R_nd R))" 
  and dec: "\<forall> (b,p) \<in> critical_peaks ren R. eld_fan R l r p"
  and ll: "left_linear_trs R"
  defines "ll \<equiv> (\<lambda> step. (source_labeling step,l step))"
  and "rr \<equiv> (lex_r (sl_rel (R_d R) (R_nd R)) r)" (is "_ \<equiv> lex_r ?r1 ?r2")
  shows "rel_props (fst rr) (snd rr)"
  and "compatible R ll rr"
  and  "\<forall> (b,p) \<in> critical_peaks ren R. eldc R ll rr p"
proof -
  show "rel_props (fst rr) (snd rr)"
    using rel_props_lex rp SN_rel_has_rel_props SN unfolding rr_def by blast
  show "compatible R ll rr" using assms SN_rel_compatible by fast
  show "\<forall>(b, p)\<in>critical_peaks ren R. eldc R ll rr p"
    using source_labeling_eld_imp_eld dec unfolding ll_def rr_def by fast
qed

(* new begin *)
lemma rule_labeling_conv_is_sound_ll:
  defines "r \<equiv> ({(n,m). n < (m::nat)},{(n,m). n \<le> (m::nat)})"
  assumes ll: "left_linear_trs R"
  and SN: "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
  and dec: "\<forall> (b,p) \<in> critical_peaks ren R. eld_fan R (rule_labeling i) r p"
  shows "CR (rstep R)"
proof -
  have r: "refl (snd r)" unfolding r_def refl_on_def by simp
  have rp: "rel_props (fst r) (snd r)" using rule_labeling_has_rel_props unfolding r_def by fast
  have el: "weakly_compatible R (rule_labeling i) r"
    using rule_labeling_is_weakly_compatible[OF r ll] by auto
  from SN_rel_lex[OF el rp SN dec ll] show ?thesis using main by blast
qed
(* new end *)

lemma ld_trs_implies_ldc_trs:
 assumes "ld_trs R p jl1 jl2 jl3 jr1 jr2 jr3"
 shows "ldc_trs R p jl1 jl2 jl3 jr1 jr2 jr3" 
using assms unfolding ld_trs_def ldc_trs_def using seq_imp_conv by blast

thm seq.induct

lemma seq_imp_ast2: 
assumes "jl \<in> seq R"
shows "(first jl, last jl) \<in> (rstep R)\<^sup>*"
proof - 
  obtain s ss where jl:"jl = (s, ss)" by (cases jl, auto)
  from assms[unfolded jl] have "(first (s, ss), last (s, ss)) \<in> (rstep R)\<^sup>*"
  proof (induct rule: seq.induct)
    case (2 s t r p \<sigma> ts)
    then have "(s, t) \<in> rstep R" using rstep_r_p_s_imp_rstep by blast
    with 2 show ?case by (auto simp: get_target_def r_into_rtrancl)
  qed auto
  then show ?thesis unfolding jl by auto
qed

lemma seq_comp2:
  assumes jl: "jl \<in> seq R" and "(s,first jl) \<in> (rstep R)\<^sup>*"
  shows "(s,last jl) \<in> (rstep R)\<^sup>*"
proof -
  have "(first jl, last jl) \<in> (rstep R)\<^sup>* " using assms seq_imp_ast2[OF jl] by auto
  then show ?thesis using assms using rtrancl_trans by auto
qed

lemma seq_comp:
 assumes "jl \<in> seq R" and "(s,first jl) \<in> (rstep R)\<^sup>*"
 shows "\<forall>i < length (snd jl). (s, get_source (snd jl ! i)) \<in>  (rstep R)\<^sup>*" proof -
 {fix i
 assume A: "i < length (snd jl)"
 from A have "(s, get_source (snd jl ! i)) \<in> (rstep R)\<^sup>*" using assms(1) assms(2) r_ast_seq_imp_r_ast by blast
} then show ?thesis by auto
qed

lemma ld_trs_implies_fan:
 assumes ld_trs: "ld_trs R p jl1 jl2 jl3 jr1 jr2 jr3"
 shows   "fan R p jl1 jl2 jl3 jr1 jr2 jr3" 
proof -
  have eq: "get_source (fst p) = get_source (snd p)" using ld_trs unfolding ld_trs_def local_peaks_def get_source_def by auto
  have jl1: "jl1 \<in> seq R" and jl2: "jl2 \<in> seq R" and jl3: "jl3 \<in> seq R"
    and eq_jl12: "last jl1 = first jl2" and eq_jl23: "last jl2 = first jl3"
    and jr1: "jr1 \<in> seq R" and jr2: "jr2 \<in> seq R" and jr3: "jr3 \<in> seq R"
    and eq_jr12: "last jr1 = first jr2" and eq_jr23: "last jr2 = first jr3"
    using ld_trs unfolding ld_trs_def by auto
  from assms  have "(get_source (fst p),first jl1) \<in> rstep R" 
    using ld_trs unfolding ld_trs_def local_peaks_def get_source_def get_target_def 
    using rstep_r_p_s_imp_rstep by force
  then have L1: "(get_source (fst p),first jl1) \<in> (rstep R)\<^sup>*" by auto
  have L2: "(get_source (fst p),first jl2) \<in> (rstep R)\<^sup>*" using seq_comp2[OF jl1 L1] eq_jl12 by auto  
  have L3: "(get_source (fst p),first jl3) \<in> (rstep R)\<^sup>*" using seq_comp2[OF jl2 L2] eq_jl23 by auto
  from assms have "(get_source (snd p), first jr1) \<in> rstep R" 
    using ld_trs unfolding ld_trs_def local_peaks_def get_source_def get_target_def 
    using rstep_r_p_s_imp_rstep by force
  then have R1: "(get_source (snd p),first jr1) \<in> (rstep R)\<^sup>*" by auto
  have R2: "(get_source (snd p),first jr2) \<in> (rstep R)\<^sup>*" using seq_comp2[OF jr1 R1] eq_jr12 by auto
  have R3: "(get_source (snd p),first jr3) \<in> (rstep R)\<^sup>*" using seq_comp2[OF jr2 R2] eq_jr23 by auto
  from seq_comp[OF jl1 L1] seq_comp[OF jl2 L2] seq_comp[OF jl3 L3]
    seq_comp[OF jr1 R1] seq_comp[OF jr2 R2] seq_comp[OF jr3 R3]
  show ?thesis unfolding fan_def using eq by auto
qed

lemma rule_labeling_is_sound_ll:
  defines "r \<equiv> ({(n,m). n < (m::nat)},{(n,m). n \<le> (m::nat)})"
  assumes ll: "left_linear_trs R"
  and SN: "SN_rel (rstep (R_d R)) (rstep (R_nd R))"
  and dec: "\<forall> (b,p) \<in> critical_peaks ren R. eld R (rule_labeling i) r p"
  shows "CR (rstep R)" 
proof -
  have "\<forall> (b,p) \<in> critical_peaks ren R. eld_fan R (rule_labeling i) r p" 
  proof
    fix b p assume A: "(b,p) \<in> critical_peaks ren R"
    from A dec have eld: "eld R (rule_labeling i) r p" by auto
    have "eld_fan R (rule_labeling i) r p" using eld unfolding eld_fan_def eld_def
      using ld_trs_implies_ldc_trs ld_trs_implies_fan by metis
    then show "eld_fan R (rule_labeling i) r p" by auto
  qed
  then show ?thesis using SN ll r_def rule_labeling_conv_is_sound_ll by auto
qed 

hide_const (open) last

end
