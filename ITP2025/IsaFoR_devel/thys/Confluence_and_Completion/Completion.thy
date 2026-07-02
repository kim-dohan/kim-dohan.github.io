(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Completion
  imports
    First_Order_Rewriting.Critical_Pairs
    Equational_Reasoning
    Ord.Reduction_Pair
    Knuth_Bendix_Order.Lexicographic_Extension
    Auxx.Multiset2
begin

type_synonym
  ('f, 'v) completion_state = "('f, 'v) equations \<times> ('f, 'v) trs"

type_synonym
  ('f, 'v) completion_run = "nat \<times> (nat \<Rightarrow> ('f, 'v) completion_state)"

lemma conversion_imp_conversion_subset:
  assumes conversion: "\<And> s t. (s, t) \<in> E - E' \<Longrightarrow> (s, t) \<in> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(rstep E)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"
  unfolding subsumes_def[symmetric]
  unfolding subsumes_via_rule_conversion
proof (clarify)
  fix s t
  assume mem: "(s, t) \<in> E"
  show "(s, t) \<in> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"
  proof (cases "(s, t) \<in> E'")
    case False
    with mem have "(s, t) \<in> E - E'" by simp
    from assms[OF this]
    show ?thesis unfolding estep_sym_closure_conv by auto
  qed auto
qed

lemma conversion_imp_conversion_id:
  assumes conversion1: "\<And> s t. (s, t) \<in> E - E' \<Longrightarrow> (s, t) \<in> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"
    and conversion2: "\<And> s t. (s, t) \<in> E' - E \<Longrightarrow> (s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(rstep E)\<^sup>\<leftrightarrow>\<^sup>* = (rstep E')\<^sup>\<leftrightarrow>\<^sup>*" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
    by (rule conversion_imp_conversion_subset[OF conversion1])
next
  show "?r \<subseteq> ?l"
    by (rule conversion_imp_conversion_subset[OF conversion2])
qed

locale completion = redpair_order S NS + mono_redpair S NS
  for S NS :: "('f, 'v) trs"
begin

inductive_set comp_step :: "('f, 'v) completion_state rel" where 
  deduce: "(u, s) \<in> rstep R \<Longrightarrow> (u, t) \<in> rstep R \<Longrightarrow> ((E, R), (E \<union> {(s, t)}, R)) \<in> comp_step"
| orientl: "(s, t) \<in> S \<Longrightarrow> ((E \<union> {(s, t)}, R), (E, R \<union> {(s, t)})) \<in> comp_step"
| orientr: "(t, s) \<in> S \<Longrightarrow> ((E \<union> {(s, t)}, R), (E, R \<union> {(t, s)})) \<in> comp_step"
| simplifyl: "(s, u) \<in> rstep R \<Longrightarrow> ((E \<union> {(s, t)}, R), (E \<union> {(u, t)}, R)) \<in> comp_step"
| simplifyr: "(t, u) \<in> rstep R \<Longrightarrow> ((E \<union> {(s, t)}, R), (E \<union> {(s, u)}, R)) \<in> comp_step"
| delete: "((E \<union> {(s, s)}, R), (E, R)) \<in> comp_step"
| compose: "(t, u) \<in> rstep R \<Longrightarrow> ((E, R \<union> {(s, t)}), (E, R \<union> {(s, u)})) \<in> comp_step"
| collapse: "(s, u) \<in> rstep R \<Longrightarrow> ((E, R \<union> {(s, t)}), (E \<union> {(u, t)}, R)) \<in> comp_step"

definition completion_run :: "('f, 'v) completion_run \<Rightarrow> bool"
  where "completion_run crun \<equiv>
    (case crun of (n, ERi) \<Rightarrow> (\<forall> i < n. (ERi i, ERi (Suc i)) \<in> comp_step))"

definition full_completion_run :: "('f, 'v) equations \<Rightarrow> ('f, 'v) completion_run \<Rightarrow> bool"
  where "full_completion_run E crun \<equiv>
    completion_run crun \<and> (case crun of (n, ERi) \<Rightarrow> ERi 0 = (E, {}) \<and> fst (ERi n) = {})"

definition result :: "('f, 'v) completion_run \<Rightarrow> ('f, 'v) trs"
  where "result crun \<equiv> snd (snd crun (fst crun))"

definition eqns :: "('f, 'v) completion_state \<Rightarrow> ('f, 'v) equations"
  where "eqns ER \<equiv> fst ER \<union> snd ER"

lemma completion_run_conversion:
  assumes "completion_run (n, ERi)"
    and "i \<le> n"
  shows "(rstep (eqns (ERi 0)))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (eqns (ERi i)))\<^sup>\<leftrightarrow>\<^sup>*"
  using \<open>i \<le> n\<close>
proof (induct i)
  case 0
  show ?case by simp
next
  case (Suc i)
  obtain E R where ERi: "ERi i = (E, R)" by force
  obtain E' R' where ERsi: "ERi (Suc i) = (E', R')" by force
  from Suc assms have "(ERi i, ERi (Suc i)) \<in> comp_step" unfolding
      completion_run_def by auto
  then have step: "((E, R),(E', R')) \<in> comp_step" unfolding ERi ERsi  .
  from Suc have "(rstep (eqns (ERi 0)))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (eqns (ERi i)))\<^sup>\<leftrightarrow>\<^sup>*" by simp
  also have "... = (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*" unfolding ERi eqns_def by simp
  also have "... = (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*" (is "?l = ?r")
    using step
  proof (cases rule: comp_step.cases)
    case (delete s)
    show ?thesis unfolding delete
      by (rule conversion_imp_conversion_id, auto)
  next
    case (deduce u s t)    
    from deduce(3) have "(s, u) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" by auto
    also have "(u, t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" using deduce(4) by auto
    finally have conv: "(s, t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show ?thesis unfolding deduce 
      by (rule conversion_imp_conversion_id, insert conv, auto)
  next
    case (orientl s t)
    show ?thesis unfolding orientl
      by (rule conversion_imp_conversion_id, auto)
  next
    case (orientr s t)
    show ?thesis unfolding orientr
      by (rule conversion_imp_conversion_id, auto)
  next
    case (simplifyl s u F t)
    from simplifyl(4) have "(s, u) \<in> (rstep (F \<union> R \<union> {(u, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(u, t) \<in> (rstep (F \<union> R \<union> {(u, t)}))\<^sup>\<leftrightarrow>" by auto
    finally have st: "(s, t) \<in> (rstep (F \<union> R \<union> {(u, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from simplifyl(4) have "(u, s) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(s, t) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    finally have ut: "(u, t) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show ?thesis unfolding simplifyl
      by (rule conversion_imp_conversion_id, insert st ut, auto)
  next
    case (simplifyr t u F s)
    have "(s, u) \<in> (rstep (F \<union> R \<union> {(s, u)}))\<^sup>\<leftrightarrow>" by auto
    also have "(u, t) \<in> (rstep (F \<union> R \<union> {(s, u)}))\<^sup>\<leftrightarrow>" using simplifyr(4) by auto
    finally have st: "(s, t) \<in> (rstep (F \<union> R \<union> {(s, u)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    have "(s, t) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(t, u) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>" using simplifyr(4) by auto
    finally have su: "(s, u) \<in> (rstep (F \<union> R \<union> {(s, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show ?thesis unfolding simplifyr
      by (rule conversion_imp_conversion_id, insert st su, auto)
  next
    case (compose t u Q s)
    have "(s, u) \<in> (rstep (E \<union> Q \<union> {(s, u)}))\<^sup>\<leftrightarrow>" by auto
    also have "(u, t) \<in> (rstep (E \<union> Q \<union> {(s, u)}))\<^sup>\<leftrightarrow>" using compose(4) by auto
    finally have st: "(s, t) \<in> (rstep (E \<union> Q \<union> {(s, u)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    have "(s, t) \<in> (rstep (E \<union> Q \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(t, u) \<in> (rstep (E \<union> Q \<union> {(s, t)}))\<^sup>\<leftrightarrow>" using compose(4) by auto
    finally have su: "(s, u) \<in> (rstep (E \<union> Q \<union> {(s, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show ?thesis unfolding compose
      by (rule conversion_imp_conversion_id, insert st su , auto)
  next
    case (collapse s u t)    
    from collapse(3) have "(s, u) \<in> (rstep (E \<union> R' \<union> {(u, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(u, t) \<in> (rstep (E \<union> R' \<union> {(u, t)}))\<^sup>\<leftrightarrow>" by auto
    finally have st: "(s, t) \<in> (rstep (E \<union> R' \<union> {(u, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from collapse(3) have "(u, s) \<in> (rstep (E \<union> R' \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    also have "(s, t) \<in> (rstep (E \<union> R' \<union> {(s, t)}))\<^sup>\<leftrightarrow>" by auto
    finally have ut: "(u, t) \<in> (rstep (E \<union> R' \<union> {(s, t)}))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show ?thesis unfolding collapse
      by (rule conversion_imp_conversion_id, insert st ut, auto)
  qed
  finally  show ?case unfolding ERsi eqns_def by simp
qed

lemma completion_run_orientation: 
  assumes "completion_run (n, ERi)"
    and "snd (ERi 0) \<subseteq> S"
    and "i \<le> n"
  shows "snd (ERi i) \<subseteq> S"
  using \<open>i \<le> n\<close>
proof (induct i)
  case 0 show ?case using assms by simp
next
  case (Suc i)
  obtain E R where ERi: "ERi i = (E, R)" by force
  obtain E' R' where ERsi: "ERi (Suc i) = (E', R')" by force
  from Suc assms have "(ERi i, ERi (Suc i)) \<in> comp_step" unfolding
      completion_run_def by auto
  then have step: "((E, R),(E', R')) \<in> comp_step" unfolding ERi ERsi  .
  from Suc have "snd (ERi i) \<subseteq> S" by simp
  then have or: "R \<subseteq> S" unfolding ERi by simp
  have "R' \<subseteq> S" using step
  proof (cases rule: comp_step.cases)
    case (delete s) 
    then show ?thesis using or by auto
  next
    case (deduce u s t)
    then show ?thesis using or by auto
  next
    case (orientl s t)
    then show ?thesis using or by auto
  next
    case (orientr s t)
    then show ?thesis  using or by auto
  next
    case (simplifyl s u F t)
    then show ?thesis using or by auto
  next
    case (simplifyr t u F s)
    then show ?thesis using or by auto
  next
    case (compose t u Q s)
    note t = or[unfolded compose] compose(4)
    from rstep_subset[OF ctxt_S subst_S] t(1) have "rstep Q \<subseteq> S" by simp
    with t(2) have tu: "(t, u) \<in> S" ..
    have "(s, u) \<in> S" by (rule trans_S_point[OF _ tu], insert t(1), auto)
    then show ?thesis using or compose(4) unfolding compose by auto
  next
    case (collapse s u t)    
    then show ?thesis using or by auto
  qed
  then show ?case unfolding ERsi by simp
qed

lemma full_completion_run:
  assumes full: "full_completion_run E crun"
  shows "(rstep E)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (result crun))\<^sup>\<leftrightarrow>\<^sup>* \<and> SN (rstep (result crun))"
proof -
  obtain n ERi where crun: "crun = (n, ERi)" by force
  note full = full[unfolded crun full_completion_run_def split]
  from full have run: "completion_run (n, ERi)" by simp
  from completion_run_conversion[OF run, of n]
  have conv: "(rstep E)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (result crun))\<^sup>\<leftrightarrow>\<^sup>*"
    using full unfolding crun result_def eqns_def by auto
  from completion_run_orientation[OF run, of n]
  have "result crun \<subseteq> S" using full unfolding crun result_def eqns_def by auto
  from manna_ness[OF this] conv show ?thesis by simp
qed

end

type_synonym
  ('f, 'v) comp_conversion_terms = "nat \<Rightarrow> ('f, 'v) term"

type_synonym
  ('f, 'v) comp_conversion_rules = "nat \<Rightarrow> ('f, 'v) rule \<times> bool option"

type_synonym
  ('f, 'v) comp_conversion = "nat \<times> ('f, 'v) comp_conversion_terms \<times> ('f, 'v) comp_conversion_rules"

locale full_completion_run = completion S NS
  for S NS :: "('f, 'v :: infinite) trs" + 
  fixes ren :: "'v renaming2" 
    and E :: "nat \<Rightarrow> ('f, 'v) equations"
    and R :: "nat \<Rightarrow> ('f, 'v) trs"
    and E0 :: "('f, 'v) equations"
    and n :: nat
  assumes frun: "full_completion_run E0 (n, \<lambda> i. (E i, R i))"
    and fair: "\<And> b l r. (b, l, r) \<in> critical_pairs ren (R n) (R n) \<Longrightarrow> 
     (\<exists> i. i \<le> n \<and> (l, r) \<in> E i) \<or> (l, r) \<in> (rstep (R n))\<^sup>\<down>"
begin

lemma E0_Rn_conversion: "(rstep E0)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>*"
  using full_completion_run[OF frun] unfolding result_def by simp

lemma Rn_SN: "SN (rstep (R n))" 
  using full_completion_run[OF frun] unfolding result_def by simp

definition R_all where "R_all \<equiv> \<Union> {R i | i. i \<le> n}"
definition E_all where "E_all \<equiv> \<Union> {E i | i. i \<le> n}"

fun valid_step :: "('f, 'v) term \<Rightarrow> ('f, 'v) rule \<times> bool option \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where "valid_step s (lr, None) t = (lr \<in> E_all \<and> (s, t) \<in> (rstep {lr})\<^sup>\<leftrightarrow>)"
  | "valid_step s (lr, Some True) t = (lr \<in> R_all \<and> (s, t) \<in> rstep {lr})"
  | "valid_step s (lr, Some False) t = (lr \<in> R_all \<and> (s, t) \<in> (rstep {lr})\<inverse>)"

fun comp_conversion :: "('f, 'v) term \<Rightarrow> ('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where "comp_conversion s (m, si, ri) t \<longleftrightarrow>
    s = si 0 \<and> t = si m \<and> (\<forall> i < m. valid_step (si i) (ri i) (si (Suc i)))"

fun rewrite_conversion :: "('f, 'v) comp_conversion \<Rightarrow> bool"
  where "rewrite_conversion (m, _, ri) \<longleftrightarrow>
    (\<forall> i < m. fst (ri i) \<in> R n) \<and> (\<exists> k \<le> m. (\<forall> i < k. snd (ri i) = Some True) \<and>
    (\<forall> i. k \<le> i \<longrightarrow> i < m \<longrightarrow> snd (ri i) = Some False))"

lemma forward_step:
  assumes "snd r = Some True" and "valid_step s r t"
  shows "(s, t) \<in> (rstep (R_all \<inter> {fst r}))"
proof -
  from assms(1) obtain lr where r: "r = (lr, Some True)" by (cases r, auto)
  note valid = assms(2)[unfolded r, simplified]
  from valid show ?thesis unfolding r fst_conv
    by auto
qed

lemma backward_step:
  assumes "snd r = Some False" and "valid_step s r t"
  shows "(s, t) \<in> (rstep (R_all \<inter> {fst r}))\<inverse>"
proof -
  from assms(1) obtain lr where r: "r = (lr, Some False)" by (cases r, auto)
  note valid = assms(2)[unfolded r, simplified]
  from valid show ?thesis unfolding r fst_conv
    by auto
qed

lemma equation_step:
  assumes "snd r = None" and "valid_step s r t"
  shows "(s, t) \<in> (rstep (E_all \<inter> {fst r}))\<^sup>\<leftrightarrow>"
proof -
  from assms(1) obtain lr where r: "r = (lr, None)" by (cases r, auto)
  note valid = assms(2)[unfolded r, simplified]
  from valid show ?thesis unfolding r fst_conv
    by auto
qed

lemma rewrite_conversion_imp_join:
  assumes conv: "comp_conversion s conv t"
    and rewr: "rewrite_conversion conv"
  shows "(s, t) \<in> (rstep (R n))\<^sup>\<down>"
proof -
  obtain m si ri where c: "conv = (m, si, ri)" by (cases conv, auto)
  note rewr = rewr[unfolded c, simplified]
  from rewr obtain k where km: "k \<le> m" and 
    forward: "\<And> i. i < k \<Longrightarrow> snd (ri i) = Some True"
    and backward: "\<And> i. k \<le> i \<Longrightarrow> i < m \<Longrightarrow> snd (ri i) = Some False"
    by auto
  note conv = conv[unfolded c, simplified]
  from forward km
  have forward: "(s, si k) \<in> (rstep (R n))\<^sup>*"
  proof (induct k)
    case 0
    show ?case using conv by simp
  next
    case (Suc k)
    then have steps: "(s, si k) \<in> (rstep (R n))\<^sup>*" by auto
    from Suc(2) have snd: "snd (ri k) = Some True" by simp
    with conv Suc(3) have valid: "valid_step (si k) (ri k) (si (Suc k))" by simp
    from Suc(3) rewr have Rn: "fst (ri k) \<in> R n" by auto
    from set_mp[OF rstep_mono forward_step[OF snd valid], of "R n"]
    have "(si k, si (Suc k)) \<in> rstep (R n)" using Rn by auto
    with steps show ?case by auto
  qed
  let ?R = "((rstep (R n))\<inverse>)"
  {
    fix i
    assume i: "k + i \<le> m"
    from i have "(si k, si (k + i)) \<in> ?R\<^sup>*"
    proof (induct i)
      case 0
      show ?case by simp
    next
      case (Suc i)
      let ?i = "k + i"
      from Suc have steps: "(si k, si ?i) \<in> ?R\<^sup>*" by auto
      from Suc(2) have ki: "?i < m" by simp
      from backward[OF _ this] have snd: "snd (ri ?i) = Some False" by simp
      from conv ki have "valid_step (si ?i) (ri ?i) (si (Suc ?i))" by simp
      from backward_step[OF snd this] 
      have step: "(si ?i, si (Suc ?i)) \<in> (rstep (R_all \<inter> {fst (ri ?i)}))\<inverse>" by auto
      from rewr ki have fst: "fst (ri ?i) \<in> R n" by simp
      have "(si ?i, si (Suc ?i)) \<in> ?R" unfolding rstep_converse [symmetric]
        by (rule set_mp[OF rstep_mono step[unfolded rstep_converse [symmetric]]],
            insert fst, auto)
      with steps show ?case by (auto simp flip: rstep_converse)
    qed
  }
  from this[of "m - k"] km have "(si k, si m) \<in> ?R\<^sup>*" by auto
  with conv have "(t, si k) \<in> (?R\<^sup>*)\<inverse>" by simp
  then have backward: "(t, si k) \<in> (rstep (R n))\<^sup>*" unfolding rtrancl_converse by simp
  show ?thesis
    by (rule, rule forward, rule backward)
qed

definition orule :: "('f, 'v) rule \<Rightarrow> nat"
  where "orule lr \<equiv> LEAST i. i \<le> n \<and> lr \<in> R (n - i)"

fun
  c ::
  "('f, 'v) term \<Rightarrow> ('f, 'v) rule \<times> bool option \<Rightarrow> ('f, 'v) term \<Rightarrow>
      ('f, 'v) term list \<times> nat"
  where
    "c s (_, None) t = ([s, t], 0)" |
    "c s (lr, Some True) t = ([s], orule lr)" |
    "c s (lr, Some False) t = ([t], orule lr)"

fun cost :: "('f, 'v) comp_conversion \<Rightarrow> (('f, 'v) term list \<times> nat) list"
  where "cost (m, si, ri) = map (\<lambda> i. c (si i) (ri i) (si (Suc i))) [0 ..< m]"

fun
  conversion_merge ::
  "('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) comp_conversion"
  where
    "conversion_merge (m1, si1, ri1) (m2, si2, ri2) = 
    (m1 + m2, 
    (\<lambda> i. if i < m1 then si1 i else si2 (i - m1)), 
    (\<lambda> i. if i < m1 then ri1 i else ri2 (i - m1)))" 

lemma conversion_merge:
  assumes c1: "comp_conversion t1 c1 t2"
    and c2: "comp_conversion t2 c2 t3"
  shows "comp_conversion t1 (conversion_merge c1 c2) t3 \<and>
    cost (conversion_merge c1 c2) = cost c1 @ cost c2"
proof -
  obtain m1 si1 ri1 where 1: "c1 = (m1, si1, ri1)" by (cases c1, auto)
  obtain m2 si2 ri2 where 2: "c2 = (m2, si2, ri2)" by (cases c2, auto)
  note c1 = c1[unfolded 1]
  note c2 = c2[unfolded 2]
  let ?m = "m1 + m2"
  let ?si = "(\<lambda> i. if i < m1 then si1 i else si2 (i - m1))"
  let ?ri = "(\<lambda> i. if i < m1 then ri1 i else ri2 (i - m1))"
  let ?c = "conversion_merge (m1, si1, ri1) (m2, si2, ri2)"
  {
    fix i
    assume i: "i \<le> m1"
    have "?si i = si1 i" using i c1 c2
      by (cases "i < m1", auto)
  } note si1 = this
  {
    fix i
    assume i: "i \<ge> m1"
    then have "?si i = si2 (i - m1)" by simp
  } note si2 = this
  show ?thesis   unfolding conversion_merge.simps comp_conversion.simps 1 2
  proof (intro conjI allI impI)
    have "t1 = si1 0" using c1 by simp
    also have "... = ?si 0" using si1[of 0] by simp
    finally show "t1 = ?si 0" .
  next
    have "t3 = si2 m2" using c2 by simp
    also have "... = ?si ?m" using si2[of ?m] by simp
    finally show "t3 = ?si ?m" .
  next
    fix i
    assume i: "i < ?m"
    show "valid_step (?si i) (?ri i) (?si (Suc i))"
    proof (cases "i < m1")
      case True
      then show ?thesis using si1[of i] si1[of "Suc i"] c1 by auto
    next
      case False
      then have id: "Suc i - m1 = Suc (i - m1)" by simp
      with False have id: "?si i = si2 (i - m1)" "?si (Suc i) = si2 (Suc (i - m1))" by auto
      show ?thesis unfolding id using i False c2 by simp
    qed
  next
    have le: "0 \<le> m1" by simp
    let ?c = "\<lambda> i. c (?si i) (?ri i) (?si (Suc i))"
    let ?c1 = "\<lambda> i. c (si1 i) (ri1 i) (si1 (Suc i))"
    let ?c2 = "\<lambda> i. c (si2 i) (ri2 i) (si2 (Suc i))"
    have id1: "cost (?m, ?si, ?ri) = map ?c [0 ..< m1] @ map ?c [m1 ..< ?m]"
      unfolding cost.simps upt_add_eq_append[OF le] map_append ..
    have id2: "map ?c [0 ..< m1] = map ?c1 [0 ..< m1]" 
    proof (rule nth_map_conv, simp, intro allI impI)
      fix i
      assume "i < length [0 ..< m1]"
      then have i: "i < m1" by simp
      then have "?c ([0 ..< m1] ! i) = ?c i" by simp
      also have "... = ?c1 i" using si1[of i] si1[of "Suc i"] i by simp
      finally show "?c ([0 ..< m1] ! i) = ?c1 ([0 ..< m1] ! i)" using i by simp
    qed
    have id3: "map ?c [m1 ..< ?m] = map ?c2 [0 ..< m2]" 
    proof (rule nth_map_conv, simp, intro allI impI)
      fix i
      assume "i < length [m1..< ?m]"
      then have i: "i < m2" by simp
      then have "?c ([m1 ..< ?m] ! i) = ?c (m1 + i)" by simp
      also have "... = ?c2 i" using si2[of "m1 + i"] si2[of "m1 + Suc i"] i by simp
      finally show "?c ([m1 ..< ?m] ! i) = ?c2 ([0 ..< m2] ! i)" using i by simp
    qed
    from id1[unfolded id2 id3]
    show "cost (?m, ?si, ?ri) = cost (m1, si1, ri1) @ cost(m2, si2, ri2)"
      by simp
  qed
qed

definition conversion_merge_three :: "('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) comp_conversion \<Rightarrow> ('f, 'v) comp_conversion"
  where "conversion_merge_three c1 c2 c3 = conversion_merge (conversion_merge c1 c2) c3"

lemma conversion_merge_three:
  assumes c1: "comp_conversion t1 c1 t2"
    and c2: "comp_conversion t2 c2 t3"
    and c3: "comp_conversion t3 c3 t4"
  shows "comp_conversion t1 (conversion_merge_three c1 c2 c3) t4 \<and>
    cost (conversion_merge_three c1 c2 c3) = cost c1 @ cost c2 @ cost c3"
proof -
  from conversion_merge[OF c1 c2] have c12: "comp_conversion t1 (conversion_merge c1 c2) t3"
    and cost: "cost (conversion_merge c1 c2) = cost c1 @ cost c2" by auto
  from conversion_merge[OF c12 c3] cost show ?thesis
    unfolding conversion_merge_three_def by simp
qed

fun
  conversion_split ::
  "('f, 'v) comp_conversion \<Rightarrow> nat \<Rightarrow>
      ('f, 'v) comp_conversion \<times> ('f, 'v) comp_conversion"
  where
    "conversion_split (m, si, ri) k = (
    (k, si, ri),
    (m - k, \<lambda> i. si (i + k), \<lambda> i. ri (i + k)))"

lemma conversion_split_left:
  assumes "comp_conversion t (m, si, ri) u"
    and "k \<le> m"
  shows "comp_conversion t (fst (conversion_split (m, si, ri) k)) (si k)"
  using assms by auto

lemma conversion_split_right:
  assumes "comp_conversion t (m, si, ri) u"
    and "k \<le> m"
  shows "comp_conversion (si k) (snd (conversion_split (m, si, ri) k)) u"
  using assms by auto

lemma conversion_split_cost:
  assumes k: "k \<le> m"
  shows "cost (m, si, ri) = cost (fst (conversion_split (m, si, ri) k)) @
    cost (snd (conversion_split (m, si, ri) k))"
proof -
  from upt_add_eq_append[of 0 k "m - k"] k
  have id: "[0..<m] = [0..<k] @ [k..<m]" by simp
  show ?thesis by (simp add: id, rule nth_map_conv, auto simp: ac_simps)
qed

fun
  conversion_split_three ::
  "('f, 'v) comp_conversion \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ('f, 'v) comp_conversion \<times> ('f, 'v) comp_conversion \<times> ('f, 'v) comp_conversion"
  where
    "conversion_split_three c123 k1 k2 = (
    let (c12, c3) = conversion_split c123 k2;
        (c1, c2)  = conversion_split c12 k1
    in (c1, c2, c3))"

lemma conversion_split_three:
  assumes c: "comp_conversion t (m, si, ri) u"
    and k1: "k1 \<le> k2"
    and k2: "k2 \<le> m"
    and s3: "conversion_split_three (m, si, ri) k1 k2 = (c1, c2, c3)"
  shows "comp_conversion t c1 (si k1) \<and> 
    comp_conversion (si k1) c2 (si k2) \<and> 
    comp_conversion (si k2) c3 u \<and>
    cost (m, si, ri) = cost c1 @ cost c2 @ cost c3 \<and>
    c2 = (k2 - k1, (\<lambda> i. si (k1 + i)), (\<lambda> i. ri (k1 + i)))"
proof - 
  let ?c = "comp_conversion"
  let ?s = "conversion_split"
  obtain c12 c3' where s1: "?s (m, si, ri) k2 = (c12, c3')" by force
  note s3 = s3[unfolded conversion_split_three.simps Let_def s1 split]
  from s3 have s2: "?s c12 k1 = (c1, c2)" by (cases "?s c12 k1", auto)
  from s3[unfolded s2] s1 have s1: "?s (m, si, ri) k2 = (c12, c3)" by simp
  from conversion_split_right[OF c k2, unfolded s1] have 3: "?c (si k2) c3 u" by simp
  from conversion_split_left[OF c k2, unfolded s1] have 12: "?c t c12 (si k2)" by simp
  have c12: "c12 = (k2, si, ri)" using s1 by simp
  note 12 = 12[unfolded c12]
  note s2 = s2[unfolded c12]
  have c2: "c2 = (k2 - k1, \<lambda>i. si (k1 + i), \<lambda>i. ri (k1 + i))" using s2
    by (auto simp: ac_simps)
  from conversion_split_left[OF 12 k1, unfolded s2] have 1: "?c t c1 (si k1)" by simp
  from conversion_split_right[OF 12 k1, unfolded s2] have 2: "?c (si k1) c2 (si k2)" by simp
  from conversion_split_cost[OF k2, of si ri, unfolded s1] 
  have "cost (m, si, ri) = cost c12 @ cost c3" by simp
  also have "... = cost c1 @ cost c2 @ cost c3"
    using conversion_split_cost[OF k1, of si ri] unfolding c12 using s2 by auto
  finally
  show ?thesis using 1 2 3 c2 by simp
qed

definition C where
  "C \<equiv> lex_two
    {(xs,ys). (mset ys, mset xs) \<in> mult1 (S\<inverse>)}
    {(xs,ys). mset xs = mset ys} 
    {(a,b :: nat) . a > b}"

definition Cost :: "('f, 'v) comp_conversion rel" where
  "Cost \<equiv> {(a, b). (mset (cost b), mset (cost a)) \<in> mult (C\<inverse>)}"

lemma comp_step: 
  "i < n \<Longrightarrow> ((E i, R i), (E (Suc i), R (Suc i))) \<in> comp_step"
  using frun[unfolded full_completion_run_def split completion_run_def]
  by auto

lemma rstep_R_all_S: "rstep R_all \<subseteq> S"
proof -
  note frun = frun[unfolded full_completion_run_def split]
  then have crun: "completion_run (n, \<lambda>i. (E i, R i))" ..
  {
    fix i 
    assume "i \<le> n"
    from completion_run_orientation[OF crun _ this] frun
    have "R i \<subseteq> S" by auto
  }
  then have rel: "R_all \<subseteq> S" unfolding R_all_def by auto
  show ?thesis
    by (rule rstep_subset[OF ctxt_S subst_S rel])
qed


lemma proof_simplification:
  assumes cconv: "comp_conversion s conv t"
    and nrewr: "\<not> rewrite_conversion conv"
  shows "\<exists> conv'. comp_conversion s conv' t \<and> (conv, conv') \<in> Cost"
proof -
  obtain m si ri where c: "conv = (m, si, ri)" by (cases conv, auto)
  note cconv = cconv[unfolded c]
  note conv = cconv[simplified]
  from conv have valid: "\<And> i. i < m \<Longrightarrow> valid_step (si i) (ri i) (si (Suc i))"
    by auto
  let ?smaller = "\<lambda> i. \<exists> m' si' ri'. comp_conversion (si i) (m', si', ri') (si (Suc i)) \<and>
    (\<forall> i' < m'. (c (si i) (ri i) (si (Suc i)), c (si' i') (ri' i') (si' (Suc i'))) \<in> C)" 
  let ?smaller2 = "\<lambda> i. \<exists> m' si' ri'. comp_conversion (si i) (m', si', ri') (si (Suc (Suc i))) \<and>
    (\<forall> i' < m'. (c (si i) (ri i) (si (Suc i)), c (si' i') (ri' i') (si' (Suc i'))) \<in> C)" 
  have main: "(\<exists> i < m. ?smaller i) \<or> (\<exists> i. Suc i < m \<and> ?smaller2 i)"
  proof (cases "\<exists> i < m. snd (ri i) = None")
    case True note 1 = this
    then obtain i where i: "i < m" and snd: "snd (ri i) = None" by auto
    then obtain lr where ri: "ri i = (lr, None)" by (cases "ri i", auto)
    from equation_step[OF snd valid[OF i]]
    have step: "(si i, si (Suc i)) \<in> (rstep E_all)\<^sup>\<leftrightarrow>" 
      and lr_step: "(si i, si (Suc i)) \<in> (rstep {lr})\<^sup>\<leftrightarrow>" and lr_mem: "lr \<in> E_all" 
      unfolding ri by auto
    have ci: "c (si i) (ri i) (si (Suc i)) = ([si i, si (Suc i)], 0)" (is "_ = ?ci")
      unfolding ri by simp
    {
      (* tedious reasoning that lr must be deleted at some point *)
      from lr_mem[unfolded E_all_def] obtain j where j: "j \<le> n" and lr_mem: "lr \<in> E j"
        by auto
      let ?P = "\<lambda> j. j \<le> n \<and> lr \<in> E (n - j)"
      have P: "?P (n - j)" using lr_mem j by simp
      obtain j where j: "j  = (LEAST j. ?P j)" by auto
      from LeastI[of ?P, OF P] have lr_mem: "?P j" unfolding j .
      from frun[unfolded full_completion_run_def] 
      have lr_nmem: "lr \<notin> E n" by auto
      have j0: "j \<noteq> 0"
      proof 
        assume "j = 0"
        with lr_nmem lr_mem show False by simp
      qed
      then have "j - Suc 0 < j" by simp
      from not_less_Least[OF this[unfolded j]] have lr_nmem: "\<not> ?P (j - Suc 0)"
        unfolding j .
      from j0 lr_mem have id: "n - (j - Suc 0) = Suc (n - j)" by (cases j, auto)
      have "\<exists> j < n. lr \<in> E j \<and> lr \<notin> E (Suc j)"
        by (intro exI conjI, insert j0 lr_mem lr_nmem, auto simp: id)
    }
    then obtain j where j: "j < n" and lr_mem: "lr \<in> E j" 
      and lr_nmem: "lr \<notin> E (Suc j)" by blast
    then have neq: "E j \<noteq> E (Suc j)" by auto
    show ?thesis
    proof (rule disjI1, rule exI, rule conjI[OF i])
      from comp_step[OF j] have cstep: "((E j, R j), (E (Suc j), R (Suc j))) \<in> comp_step" .
      from cstep show "?smaller i"
      proof(cases)
        case (delete s) (* 1.3 *)
        with lr_mem lr_nmem have "lr = (s, s)" by simp
        from lr_step[unfolded this] have "(si i, si (Suc i)) \<in> (rstep Id)\<^sup>\<leftrightarrow>"
          by auto
        with rstep_id have id: "si i = si (Suc i)" by force
        let ?si' = "\<lambda> n :: nat. si i"
        let ?ri' = ri
        from id have conv: "comp_conversion (si i) (0, ?si', ?ri') (si (Suc i))"
          by simp
        show ?thesis
          by (intro exI conjI, rule conv, simp add: ci)
      next
        case (orientl s t) (* 1.1 *)
        with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
        let ?si' = "\<lambda> i' :: nat. if i' = 0 then si i else si (Suc i)" 
        from j have "Suc j \<le> n" by simp
        with orientl(2) have st: "(s, t) \<in> R_all" unfolding R_all_def by blast
        from lr_step[unfolded lr] show ?thesis
        proof
          assume step: "(si i, si (Suc i)) \<in> rstep {(s, t)}"
          let ?ri' = "\<lambda> i' :: nat. ((s, t), Some True)"        
          have conv: "comp_conversion (si i) (Suc 0, ?si', ?ri') (si (Suc i))"
            using step st
            by (auto simp: R_all_def)          
          have C: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (simp add: C_def mult1_ab_a)
          show ?thesis
            by (intro exI conjI, rule conv, insert C, auto simp: ci)
        next
          assume step: "(si i, si (Suc i)) \<in> (rstep {(s, t)})\<inverse>"
          let ?ri' = "\<lambda> i' :: nat. ((s, t), Some False)"        
          have conv: "comp_conversion (si i) (Suc 0, ?si', ?ri') (si (Suc i))"
            using step st
            by simp
          have C: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (simp add: C_def mult1_ab_b)
          show ?thesis
            by (intro exI conjI, rule conv, insert C, auto simp: ci)
        qed
      next
        case (orientr t s) (* 1.1 *)
        with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
        let ?si' = "\<lambda> i' :: nat. if i' = 0 then si i else si (Suc i)" 
        from j have "Suc j \<le> n" by simp
        with orientr(2) have st: "(t, s) \<in> R_all" unfolding R_all_def by blast
        from lr_step[unfolded lr] show ?thesis
        proof
          assume "(si i, si (Suc i)) \<in> rstep {(s, t)}"
          then have step: "(si i, si (Suc i)) \<in> (rstep {(t, s)})\<inverse>" unfolding rstep_converse
              converse_def by auto        
          let ?ri' = "\<lambda> i' :: nat. ((t, s), Some False)"        
          have conv: "comp_conversion (si i) (Suc 0, ?si', ?ri') (si (Suc i))"
            using step st
            by (auto simp: R_all_def) 
          have C: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (simp add: C_def mult1_ab_b)
          show ?thesis
            by (intro exI conjI, rule conv, insert C, auto simp: ci)
        next
          assume "(si i, si (Suc i)) \<in> (rstep {(s, t)})\<inverse>"
          then have step: "(si i, si (Suc i)) \<in> rstep {(t, s)}" unfolding rstep_converse converse_def by auto
          let ?ri' = "\<lambda> i' :: nat. ((t, s), Some True)"        
          have conv: "comp_conversion (si i) (Suc 0, ?si', ?ri') (si (Suc i))"
            using step st
            by simp
          have C: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (simp add: C_def mult1_ab_a)
          show ?thesis
            by (intro exI conjI, rule conv, insert C, auto simp: ci)
        qed
      next
        case (simplifyl s u E' t) (* 1.3 *)
        with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
        from lr_step[unfolded lr] have step: "(si i, si (Suc i)) \<in> rstep {(s, t),(t, s)}"
          by auto
        then obtain D l r \<sigma> where id: "si i = D\<langle>l \<cdot> \<sigma>\<rangle>" "si (Suc i) = D\<langle>r \<cdot> \<sigma>\<rangle>" and
          mem: "(l, r) = (s, t) \<or> (l, r) = (t, s)" by auto
        from simplifyl(4) obtain l' r' D' \<sigma>' where 
          id': "s = D'\<langle>l' \<cdot> \<sigma>'\<rangle>" "u = D'\<langle>r' \<cdot> \<sigma>'\<rangle>" and lr': "(l', r') \<in> R j"
          by auto
        from j have "j \<le> n" "Suc j \<le> n" by auto
        with simplifyl(2) lr' have lr': "(l', r') \<in> R_all" and
          ut: "(u, t) \<in> E_all" unfolding E_all_def R_all_def by blast+
        have su_step: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> rstep (R_all \<inter> {(l', r')})"
          by (unfold id',
              rule rstepI[of l' r' _ _ "D \<circ>\<^sub>c (D' \<cdot>\<^sub>c \<sigma>)"  "\<sigma>' \<circ>\<^sub>s \<sigma>"], insert lr', auto)
        have su_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> S"
          by (rule set_mp[OF rstep_R_all_S], insert su_step, auto)
        from mem 
        show ?thesis
        proof
          assume "(l, r) = (s, t)"
          then have id2: "l = s" "r = t" by auto
          note id = id[unfolded id2] 
          let ?one = "D\<langle>s \<cdot> \<sigma>\<rangle>"
          let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
          let ?three = "D\<langle>t \<cdot> \<sigma>\<rangle>"
          let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
          let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((l', r'), Some True) | _ \<Rightarrow> ((u, t), None)"          
          have step1: "(?one, ?two) \<in> rstep {(l', r')}" using su_step by auto
          have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
            unfolding id
            by (simp add: all_less_two lr' ut step1, auto)
          have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (simp add: C_def id mult1_ab_a)
          have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
            by (fastforce simp: C_def id mult1_def su_S)
          show ?thesis
            by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
        next
          assume "(l, r) = (t, s)"
          then have id2: "l = t" "r = s" by auto
          note id = id[unfolded id2] 
          let ?one = "D\<langle>t \<cdot> \<sigma>\<rangle>"
          let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
          let ?three = "D\<langle>s \<cdot> \<sigma>\<rangle>"
          let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
          let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((u, t), None) | _ \<Rightarrow> ((l', r'), Some False)"          
          have step2: "(?two, ?three) \<in> (rstep {(l', r')})\<inverse>" using su_step by auto
          have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
            unfolding id using step2
            by (simp add: all_less_two lr' ut, auto)
          have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (fastforce simp: C_def id mult1_def add_mset_commute su_S)
          have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
            by (auto simp: C_def id mult1_ab_b)
          show ?thesis
            by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
        qed
      next
        case (simplifyr t u E' s)
        with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
        from lr_step[unfolded lr] have step: "(si i, si (Suc i)) \<in> rstep {(s, t),(t, s)}"
          by auto
        then obtain D l r \<sigma> where id: "si i = D\<langle>l \<cdot> \<sigma>\<rangle>" "si (Suc i) = D\<langle>r \<cdot> \<sigma>\<rangle>" and
          mem: "(l, r) = (s, t) \<or> (l, r) = (t, s)" by auto
        from simplifyr(4) obtain l' r' D' \<sigma>' where 
          id': "t = D'\<langle>l' \<cdot> \<sigma>'\<rangle>" "u = D'\<langle>r' \<cdot> \<sigma>'\<rangle>" and lr': "(l', r') \<in> R j"
          by auto
        from j have "j \<le> n" "Suc j \<le> n" by auto
        with simplifyr(2) lr' have lr': "(l', r') \<in> R_all" and
          su: "(s, u) \<in> E_all" unfolding E_all_def R_all_def by blast+
        have tu_step: "(D\<langle>t \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> rstep (R_all \<inter> {(l', r')})"
          by (unfold id',
              rule rstepI[of l' r' _ _ "D \<circ>\<^sub>c (D' \<cdot>\<^sub>c \<sigma>)"  "\<sigma>' \<circ>\<^sub>s \<sigma>"], insert lr', auto)
        have tu_S: "(D\<langle>t \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> S"
          by (rule set_mp[OF rstep_R_all_S], insert tu_step, auto)
        from mem 
        show ?thesis
        proof
          assume "(l, r) = (s, t)"
          then have id2: "l = s" "r = t" by auto
          note id = id[unfolded id2] 
          let ?one = "D\<langle>s \<cdot> \<sigma>\<rangle>"
          let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
          let ?three = "D\<langle>t \<cdot> \<sigma>\<rangle>"
          let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
          let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((s, u), None) | _ \<Rightarrow> ((l', r'), Some False)"   
          have step2: "(?two, ?three) \<in> (rstep {(l', r')})\<inverse>" using tu_step by auto
          have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
            unfolding id using step2
            by (auto simp: all_less_two lr' su)
          have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            apply (auto simp: C_def id tu_S)
          proof -
            have f1: "{#} + {#D\<langle>s \<cdot> \<sigma>\<rangle>#} + ({#} + {#D\<langle>u \<cdot> \<sigma>\<rangle>#}) = {#D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>#}"
              by auto
            have f2: "{#} + {#D\<langle>s \<cdot> \<sigma>\<rangle>#} + ({#} + {#D\<langle>t \<cdot> \<sigma>\<rangle>#}) = {#D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>#}"
              by auto
            have "({#} + {#D\<langle>u \<cdot> \<sigma>\<rangle>#}, {#D\<langle>t \<cdot> \<sigma>\<rangle>#}) \<in> mult1 (S\<inverse>)"
              using tu_S by auto
            then show "({#D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>#}, {#D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>#}) \<in> mult1 (S\<inverse>)"
              using f2 f1 by (metis (no_types) add_mset_add_single mult1_union)
          qed
            (*by (auto simp: C_def id tu_S)*)
          have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
            by (auto simp: C_def id mult1_ab_b)
          show ?thesis
            by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
        next
          assume "(l, r) = (t, s)"
          then have id2: "l = t" "r = s" by auto
          note id = id[unfolded id2] 
          let ?one = "D\<langle>t \<cdot> \<sigma>\<rangle>"
          let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
          let ?three = "D\<langle>s \<cdot> \<sigma>\<rangle>"
          let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
          let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((l', r'), Some True) | _ \<Rightarrow> ((s, u), None)"          
          have step1: "(?one, ?two) \<in> rstep {(l', r')}" using tu_step by auto
          have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
            unfolding id using step1
            by (simp add: all_less_two lr' su, auto)
          have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
            by (auto simp: C_def id mult1_ab_a)
          have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
            by (fastforce simp: C_def id mult1_def tu_S)
          show ?thesis
            by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
        qed
      qed (insert neq lr_mem lr_nmem, auto)
    qed
  next
    case False note not_1 = this
    then have no_eqns: "\<And> i. i < m \<Longrightarrow> snd (ri i) \<noteq> None" by auto
    show ?thesis
    proof (cases "\<exists> i < m. fst (ri i) \<notin> R n")
      case True note 2 = this
      then obtain i where i: "i < m" and nmem: "fst (ri i) \<notin> R n" by auto
      from no_eqns[OF i] obtain lr dir where ri: "ri i = (lr, Some dir)" by (cases "ri i", cases "snd (ri i)", auto)
      from valid[OF i, unfolded ri] have lr_all: "lr \<in> R_all" by (cases dir, auto)
      from ri nmem have lr_n: "lr \<notin> R n" by auto
      obtain j' where j': "j' = orule lr" by auto
      obtain j where jj': "j = n - j'" by auto
      { (* tedious reasoning to show that lr is removed in step j *)
        let ?P = "\<lambda> j. j \<le> n \<and> lr \<in> R (n - j)"
        from lr_all[unfolded R_all_def] obtain j'' where j'': "j'' \<le> n" 
          and lr_j'': "lr \<in> R j''" by blast
        have j': "j' = (LEAST j. ?P j)" unfolding j' orule_def by simp
        have P: "?P (n - j'')" using lr_j'' j'' by simp
        from LeastI[of ?P, OF P] have lr_mem: "?P j'" unfolding j' .
        have j'0: "j' \<noteq> 0"
        proof 
          assume "j' = 0"
          with lr_n lr_mem show False by simp
        qed
        from j'0 lr_mem have id: "n - (j' - Suc 0) = Suc (n - j')" by (cases j', auto)
        have one: "lr \<in> R j" unfolding jj' using lr_mem by simp
        {
          fix k
          assume kj: "k > j" and kn: "k \<le> n"
          then have "n - k < j'" unfolding jj' by auto
          from not_less_Least[OF this[unfolded j']] have "lr \<notin> R k" using kn
            by auto
        } note two = this
        have three: "j < n" unfolding jj' using j'0 lr_mem by auto
        have four: "j' \<le> n" using lr_mem by simp 
        note one two three four
      }
      then have lr_mem: "lr \<in> R j" and j: "j < n" and j'n: "j' \<le> n" and lr_nmemk: "\<And> k. j < k \<Longrightarrow> k \<le> n \<Longrightarrow> lr \<notin> R k" by auto
      from lr_nmemk[of "Suc j"] j have lr_nmem: "lr \<notin> R (Suc j)" by simp      
      with lr_mem have neq: "R j \<noteq> R (Suc j)" by auto
      from forward_step[OF _ valid[OF i]] backward_step[OF _ valid[OF i]]
      have fbstep: "(dir \<and> (si i, si (Suc i)) \<in> rstep (R_all \<inter> {lr})) \<or> (\<not> dir \<and> (si i, si (Suc i)) \<in> rstep ((R_all \<inter> {lr})\<inverse>))"
        unfolding ri rstep_converse by (cases dir, auto)
      let ?lr = "if dir then lr else (snd lr, fst lr)"
      let ?R_all = "if dir then R_all else R_all\<inverse>"
      let ?step = "\<lambda> st. \<exists> D l r \<sigma>. si i = D\<langle>l \<cdot> \<sigma>\<rangle> \<and> si (Suc i) = D\<langle>r \<cdot> \<sigma>\<rangle> \<and> (l, r) = st \<and> st \<in> ?R_all"
      {
        assume dir with fbstep have "?step ?lr" by force
      }
      moreover
      {
        assume "\<not> dir" with fbstep have "?step ?lr" by force
      }
      ultimately have "?step ?lr" by blast          
      then obtain D l r \<sigma> where id: "si i = D\<langle>l \<cdot> \<sigma>\<rangle>" "si (Suc i) = D\<langle>r \<cdot> \<sigma>\<rangle>"
        "(l, r) = ?lr" 
        and mem: "?lr \<in> ?R_all" by auto
      show ?thesis
      proof (rule disjI1, rule exI, rule conjI[OF i])
        from comp_step[OF j] have cstep: "((E j, R j), (E (Suc j), R (Suc j))) \<in> comp_step" .
        from cstep show "?smaller i"
        proof(cases)
          case (compose t u R' s) (* 2.1 *)
          with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
          note id = id[unfolded lr snd_conv fst_conv]
          note mem = mem[unfolded lr snd_conv fst_conv]
          from compose(4) obtain l' r' D' \<sigma>' where 
            id': "t = D'\<langle>l' \<cdot> \<sigma>'\<rangle>" "u = D'\<langle>r' \<cdot> \<sigma>'\<rangle>" and lr': "(l', r') \<in> R'"
            by auto
          from lr' compose(3) have lr': "(l', r') \<in> R (Suc j)" by auto
          from j have "j \<le> n" "Suc j \<le> n" by auto
          with compose(3) lr' have lr': "(l', r') \<in> R_all" and
            su: "(s, u) \<in> R_all" unfolding R_all_def by blast+
          have tu_step: "(D\<langle>t \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> rstep (R_all \<inter> {(l', r')})"
            by (unfold id',
                rule rstepI[of l' r' _ _ "D \<circ>\<^sub>c (D' \<cdot>\<^sub>c \<sigma>)"  "\<sigma>' \<circ>\<^sub>s \<sigma>"], insert lr', auto)
          have tu_S: "(D\<langle>t \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> S"
            by (rule set_mp[OF rstep_R_all_S], insert tu_step, auto)
          {
            from j jj' obtain k where k: "j' = Suc k" by (cases j', auto)
            have "orule (s, u) \<le> k"
              unfolding orule_def
            proof (rule Least_le, intro conjI)
              show "k \<le> n" using j j'n unfolding jj' k by auto
            next
              have id: "Suc (n - Suc k) = n - k" using j j'n unfolding jj' k
                by auto
              show "(s, u) \<in> R (n - k)" using compose(3) unfolding jj' k id
                by simp
            qed
            then have "orule (s, u) < j'" unfolding k by simp
          }
          note o_su = this
          show ?thesis
          proof (cases dir)
            case True
            from True ri have ci: "c (si i) (ri i) (si (Suc i)) = ([si i], j')"
              (is "_ = ?ci")
              unfolding j' by simp
            from True id have id2: "l = s" "r = t" by auto
            from True mem have mem: "(s, t) \<in> R_all" by auto
            have st_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>) \<in> S"
              by (rule set_mp[OF rstep_R_all_S], insert mem, auto)            
            note id = id(1-2)[unfolded id2] 
            let ?one = "D\<langle>s \<cdot> \<sigma>\<rangle>"
            let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
            let ?three = "D\<langle>t \<cdot> \<sigma>\<rangle>"
            let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
            let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((s, u), Some True) | _ \<Rightarrow> ((l', r'), Some False)"   
            have step2: "(?two, ?three) \<in> (rstep {(l', r')})\<inverse>" using tu_step by auto
            have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
              unfolding id using step2
              by (auto simp: all_less_two lr' su)
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              by (auto simp: C_def id o_su) 
            have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
              by (auto simp: C_def id st_S)
            show ?thesis
              by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
          next
            case False
            from False ri have ci: "c (si i) (ri i) (si (Suc i)) = ([si (Suc i)], j')"
              (is "_ = ?ci")
              unfolding j' by simp
            from False id have id2: "l = t" "r = s" by auto
            from False mem have mem: "(s, t) \<in> R_all" by auto
            have st_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>) \<in> S"
              by (rule set_mp[OF rstep_R_all_S], insert mem, auto)            
            note id = id(1-2)[unfolded id2] 
            let ?one = "D\<langle>t \<cdot> \<sigma>\<rangle>"
            let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
            let ?three = "D\<langle>s \<cdot> \<sigma>\<rangle>"
            let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
            let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((l', r'), Some True) | _ \<Rightarrow> ((s, u), Some False)"          
            have step1: "(?one, ?two) \<in> rstep {(l', r')}" using tu_step by auto
            have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
              unfolding id using step1
              by (simp add: all_less_two lr' su, auto)
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              by (auto simp: C_def id st_S)
            have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
              by (auto simp: C_def id o_su)
            show ?thesis
              by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
          qed
        next
          case (collapse s u t) (* 2.2 *)
          with lr_mem lr_nmem have lr: "lr = (s, t)" by simp
          note id = id[unfolded lr snd_conv fst_conv]
          note mem = mem[unfolded lr snd_conv fst_conv]
          from collapse(3) obtain l' r' D' \<sigma>' where 
            id': "s = D'\<langle>l' \<cdot> \<sigma>'\<rangle>" "u = D'\<langle>r' \<cdot> \<sigma>'\<rangle>" and lr'sj: "(l', r') \<in> R (Suc j)"
            by auto
          from j have "j \<le> n" "Suc j \<le> n" by auto
          with collapse(2) lr'sj have lr': "(l', r') \<in> R_all" and
            ut: "(u, t) \<in> E_all" unfolding E_all_def R_all_def by blast+
          have su_step: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> rstep (R_all \<inter> {(l', r')})"
            by (unfold id', rule rstepI[of l' r' _ _ "D \<circ>\<^sub>c (D' \<cdot>\<^sub>c \<sigma>)"  "\<sigma>' \<circ>\<^sub>s \<sigma>"], insert lr', auto)
          have su_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>u \<cdot> \<sigma>\<rangle>) \<in> S"
            by (rule set_mp[OF rstep_R_all_S], insert su_step, auto)
          {
            from j jj' obtain k where k: "j' = Suc k" by (cases j', auto)
            have "orule (l', r') \<le> k"
              unfolding orule_def
            proof (rule Least_le, intro conjI)
              show "k \<le> n" using j j'n unfolding jj' k by auto
            next
              have id: "Suc (n - Suc k) = n - k" using j j'n unfolding jj' k
                by auto
              show "(l', r') \<in> R (n - k)" using collapse(1) lr'sj unfolding jj' k id
                by simp
            qed
            then have "orule (l', r') < j'" unfolding k by simp
          }
          note o_lr' = this
          show ?thesis
          proof (cases dir)
            case True
            from True ri have ci: "c (si i) (ri i) (si (Suc i)) = ([si i], j')"
              (is "_ = ?ci")
              unfolding j' by simp
            from True id have id2: "l = s" "r = t" by auto
            from True mem have mem: "(s, t) \<in> R_all" by auto
            have st_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>) \<in> S"
              by (rule set_mp[OF rstep_R_all_S], insert mem, auto)
            note id = id(1-2)[unfolded id2] 
            let ?one = "D\<langle>s \<cdot> \<sigma>\<rangle>"
            let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
            let ?three = "D\<langle>t \<cdot> \<sigma>\<rangle>"
            let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
            let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((l', r'), Some True) | _ \<Rightarrow> ((u, t), None)"          
            have step1: "(?one, ?two) \<in> rstep {(l', r')}" using su_step by auto
            have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
              unfolding id
              by (simp add: all_less_two lr' ut step1, auto)
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              by (simp add: C_def id o_lr')
            have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
              by (auto simp: C_def id st_S su_S)
            show ?thesis
              by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
          next
            case False
            from False ri have ci: "c (si i) (ri i) (si (Suc i)) = ([si (Suc i)], j')"
              (is "_ = ?ci")
              unfolding j' by simp
            from False id have id2: "l = t" "r = s" by auto
            from False mem have mem: "(s, t) \<in> R_all" by auto
            have st_S: "(D\<langle>s \<cdot> \<sigma>\<rangle>, D\<langle>t \<cdot> \<sigma>\<rangle>) \<in> S"
              by (rule set_mp[OF rstep_R_all_S], insert mem, auto)
            note id = id(1-2)[unfolded id2] 
            let ?one = "D\<langle>t \<cdot> \<sigma>\<rangle>"
            let ?two = "D\<langle>u \<cdot> \<sigma>\<rangle>"
            let ?three = "D\<langle>s \<cdot> \<sigma>\<rangle>"
            let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ?one | Suc 0 \<Rightarrow> ?two | _ \<Rightarrow> ?three" 
            let ?ri' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> ((u, t), None) | _ \<Rightarrow> ((l', r'), Some False)"          
            have step2: "(?two, ?three) \<in> (rstep {(l', r')})\<inverse>" using su_step by auto
            have conv: "comp_conversion (si i) (Suc (Suc 0), ?si', ?ri') (si (Suc i))"
              unfolding id using step2
              by (simp add: all_less_two lr' ut, auto)
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              by (auto simp: C_def id su_S st_S)
            have C1: "(?ci, c (?si' (Suc 0)) (?ri' (Suc 0)) (?si' (Suc (Suc 0)))) \<in> C"
              by (auto simp: C_def id o_lr')
            show ?thesis
              by (intro exI conjI, rule conv, unfold all_less_two, insert C0 C1, auto simp: ci)
          qed
        qed (insert lr_mem lr_nmem neq, auto)
      qed
    next
      case False note 3 = this
      {
        fix i b
        assume i: "i < m"
        from no_eqns[OF i] have "(snd (ri i) \<noteq> Some b) = (snd (ri i) = Some (\<not> b))" by auto
      } note not_Some = this
      from 3 have all_R_n: "\<And> i. i < m \<Longrightarrow> fst (ri i) \<in> R n" by auto
      with nrewr[unfolded c rewrite_conversion.simps]
      have nrewr: "\<And> k. k \<le> m \<Longrightarrow> (\<exists> i < k. snd (ri i) \<noteq> Some True) \<or> 
                          (\<exists> i \<ge> k. i < m \<and> snd (ri i) \<noteq> Some False)" by auto

      { (* tedious reasoning to get a peak \<leftarrow> \<rightarrow> in the sequence via regexp;
           problem is that nrewr only shows that given sequence is no join,
           and that peak must be constructed within this sequence.
           indirection requires auxiliary relation on indices *)
        define aux where "aux = (\<lambda> b. {(i, Suc i) | i. snd (ri i) = Some b})"
        define f where "f = aux True"
        define b where "b = aux False"
        {
          fix i j fb
          assume ij: "(i, j) \<in> fb\<^sup>*" and sub: "fb \<subseteq> f \<union> b"
          from ij[unfolded rtrancl_is_UN_relpow] obtain n where ij: "(i, j) \<in> fb^^n" by auto
          then have "j = i + n \<and> (\<forall> k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> (k, Suc k) \<in> fb)"
          proof (induct n arbitrary: i j)
            case (Suc n)
            from Suc(2) obtain k where ik: "(i, k) \<in> fb^^n" and kj: "(k, j) \<in> fb" by auto
            from kj sub have j: "j = Suc k" unfolding f_def aux_def b_def by auto
            from Suc(1)[OF ik] kj show ?case unfolding j by (metis add_Suc_right neqE not_less_eq)
          qed auto
          then have "\<exists> n. j = i + n \<and> (\<forall> k. k \<ge> i \<longrightarrow> k < j \<longrightarrow> (k, Suc k) \<in> fb)" by blast
        } note rtrancl_elim = this
        have "(0, m) \<in> (f \<union> b)\<^sup>*" unfolding rtrancl_fun_conv
          by (rule exI[of _ "\<lambda> x. x"], rule exI[of _ m], insert not_Some, auto simp: f_def aux_def b_def)
        then have "(0, m) \<in> (f\<^sup>* O b\<^sup>*) \<union> (f \<union> b)\<^sup>* O b O f O (f \<union> b)\<^sup>*"
          by regexp (* here we get the case distinction automatically *)
        then have "(0, m) \<in> (f \<union> b)\<^sup>* O b O f O (f \<union> b)\<^sup>*"
        proof
          assume "(0, m) \<in> (f\<^sup>* O b\<^sup>*)"
          then obtain k where k: "(0, k) \<in> f\<^sup>*" and km: "(k, m) \<in> b\<^sup>*" by auto
          from rtrancl_elim[OF k] have k: "\<And> i. i < k \<Longrightarrow> (i, Suc i) \<in> f" by auto
          from rtrancl_elim[OF km] obtain n where m: "m = k + n" and 
            km: "\<And> i. i \<ge> k \<Longrightarrow> i < m \<Longrightarrow> (i, Suc i) \<in> b" by auto            
          from m have "k \<le> m" by auto
          from nrewr[OF this] have False 
          proof
            assume "\<exists> i < k. snd (ri i) \<noteq> Some True"
            then obtain i where i: "i < k" and neg: "snd (ri i) \<noteq> Some True" by auto
            from i m not_Some[of i] neg have "snd (ri i) = Some False" by auto
            with k[OF i] show False unfolding f_def aux_def by auto
          next
            assume "\<exists>i\<ge>k. i < m \<and> snd (ri i) \<noteq> Some False"
            then obtain i where i: "i \<ge> k" "i < m" and neg: "snd (ri i) \<noteq> Some False" by blast
            from not_Some[OF i(2)] neg have "snd (ri i) = Some True" by auto
            with km[OF i] show False unfolding b_def aux_def by auto
          qed
          then show ?thesis by simp
        qed
        then obtain i j k where r: "(i, j) \<in> b" and f: "(j, k) \<in> f" and
          km: "(k, m) \<in> (f \<union> b)\<^sup>*" by auto
        from r f have j: "j = Suc i" and k: "k = Suc (Suc i)" unfolding b_def f_def aux_def by auto
        from rtrancl_elim[OF km[unfolded k]] have "i < m" "Suc i < m" by auto
        with r f have "\<exists> l. l < m \<and> Suc l < m \<and> snd (ri l) = Some False \<and> snd (ri (Suc l)) = Some True" 
          unfolding b_def f_def aux_def by blast
      } note peak1 = this

      { (* tedious reasoning to get a peak \<leftarrow> \<rightarrow> in the sequence;
           in this alternative proof we use a direct argument without regexp *)
        let ?P = "\<lambda> i. i < m \<and> snd (ri i) \<noteq> Some True"
        obtain i where i: "i = (LEAST i. ?P i)" by auto
        from nrewr[of m] have "\<exists> i. ?P i" by auto
        from LeastI_ex[of ?P, OF this] have Pi: "?P i" unfolding i .
        with not_Some[of i] have im: "i < m" and rev: "snd (ri i) = Some False"
          by auto
        {
          fix j 
          assume "j < i"
          from not_less_Least[OF this[unfolded i]] have "\<not> ?P j" .
        } then have "\<forall> j < i. \<not> ?P j" by simp
        with nrewr[of i] im have "\<exists> j \<ge> i. j < m \<and> (snd (ri j)) \<noteq> Some False"
          by auto
        then obtain j where ji: "j \<ge> i" and jm: "j < m" and forw: "snd (ri j) \<noteq> Some False" by auto
        from not_Some[OF jm] forw have forw: "snd (ri j) = Some True" by simp
        with rev have "i \<noteq> j" by auto 
        with ji have ji: "j > i" by auto
        let ?P = "\<lambda> k. k > i \<and> k \<le> j \<and> snd (ri k) = Some True"
        obtain k where k: "k = (LEAST k. ?P k)" by auto
        have Pj: "?P j" using ji forw by simp
        from LeastI[of ?P, OF Pj] have Pk: "?P k" unfolding k .
        then obtain l where kl: "k = Suc l" by (cases k, auto) 
        note Pk = Pk[unfolded kl]
        from kl have "l < k" by auto
        from not_less_Least[of _ ?P, OF this[unfolded k]] have Pl: "\<not> ?P l" .
        from kl Pk jm have lm: "l < m" "Suc l < m" by auto
        {
          assume "l = i"
          then have "snd (ri l) = Some False" using rev by simp
        }
        moreover
        {
          assume "l \<noteq> i"
          with Pk have "i < l" by auto
          with Pk Pl have "snd (ri l) \<noteq> Some True" by simp
          with not_Some[OF lm(1)] have "snd (ri l) = Some False" by simp
        }
        ultimately have rev: "snd (ri l) = Some False" by auto
        with Pk lm
        have "\<exists> l. l < m \<and> Suc l < m \<and> snd (ri l) = Some False \<and> snd (ri (Suc l)) = Some True" by blast
      } note peak2 = this

      from peak1 (* or *) peak2
      obtain i where i: "i < m" "Suc i < m" and revs: "snd (ri i) = Some False"
        and forws: "snd (ri (Suc i)) = Some True" by auto
      let ?i = i
      let ?i' = "Suc ?i"
      let ?i'' = "Suc ?i'"
      show ?thesis
      proof (rule disjI2, rule exI, rule conjI[OF i(2)])
        from forward_step[OF forws valid[OF i(2)]]
        have forw: "(si ?i', si ?i'') \<in> rstep {fst (ri ?i')}" by auto
        have forw: "(si ?i', si ?i'') \<in> rstep (R n)" 
          by (rule set_mp[OF rstep_mono forw], insert all_R_n[OF i(2)], auto)
        from backward_step[OF revs valid[OF i(1)]]
        have rev: "(si ?i', si ?i) \<in> rstep {fst (ri ?i)}" by auto
        have rev: "(si ?i', si ?i) \<in> rstep (R n)" 
          by (rule set_mp[OF rstep_mono rev], insert all_R_n[OF i(1)], auto)
        have "c (si i) (ri i) (si ?i') = c (si i) (fst (ri i), snd (ri i)) (si ?i')" by simp
        also have "... = ([si ?i'], orule (fst (ri i)))" (is "_ = ?ci") unfolding revs by simp
        finally have ci: "c (si i) (ri i) (si ?i') = ?ci" .
        from subset_trans[OF rstep_mono rstep_R_all_S, of "R n"] 
        have "rstep (R n) \<subseteq> S" unfolding R_all_def by auto
        then have RnS: "\<And> x. x \<in> rstep (R n) \<Longrightarrow> x \<in> S" by auto
        from RnS[OF forw] have i'i'': "(si ?i', si ?i'') \<in> S" .
        from RnS[OF rev] have i'i: "(si ?i', si ?i) \<in> S" .
        let ?CP = "critical_pairs ren (R n) (R n)"
        let ?cp = "\<exists> D b l r \<sigma>. si ?i = D\<langle>l \<cdot> \<sigma>\<rangle> \<and> si ?i'' = D\<langle>r \<cdot> \<sigma>\<rangle>
            \<and> ((b, l, r) \<in> ?CP \<or> (b, r, l) \<in> ?CP)"
        let ?join = "(si ?i, si ?i'') \<in> (rstep (R n))\<^sup>\<down>"
        from critical_pairs_main[OF rev forw]
        have "?join \<or> ?cp" .
        then have "?join \<or> (\<not> ?join \<and> ?cp)" by blast
        then show "?smaller2 i"
        proof 
          assume join: ?join (* case 3.1 *)
          then obtain u where iu: "(si ?i, u) \<in> (rstep (R n))\<^sup>*"
            and i''u: "(si ?i'', u) \<in> (rstep (R n))\<^sup>*"
            by auto
          note conv = qrsteps_imp_qrsteps_r_p_s[where Q = "{}" and nfs = False, simplified]
          {
            fix s t lr p \<sigma>
            assume "(s, t) \<in> qrstep_r_p_s False {} (R n) lr p \<sigma>"
            note step = this[unfolded qrstep_r_p_s_def, simplified]
            from step have mem: "lr \<in> R n" by simp
            have step: "(s, t) \<in> rstep {lr}" unfolding rstep_iff_rstep_r_p_s 
            proof (intro exI)
              show "(s, t) \<in> rstep_r_p_s {lr} (fst lr, snd lr) p \<sigma>"
                using step unfolding rstep_r_p_s_def' by auto
            qed
            note mem step
          } note qrstep_conv = this            
          from conv[OF iu] obtain mf sif lrf pf \<sigma>f
            where idf: "sif 0 = si i" "sif mf = u"
              and stepsf: "\<And> j. j < mf \<Longrightarrow>
              (sif j, sif (Suc j)) \<in> qrstep_r_p_s False {} (R n) (lrf j) (pf j) (\<sigma>f j)"
            by blast
          note stepsf = qrstep_conv[OF stepsf]
          from conv[OF i''u] obtain mr sir lrr "pr" \<sigma>r
            where idr: "sir 0 = si ?i''" "sir mr = u"
              and stepsr: "\<And> j. j < mr \<Longrightarrow>
              (sir j, sir (Suc j)) \<in> qrstep_r_p_s False {} (R n) (lrr j) (pr j) (\<sigma>r j)"
            by blast
          note stepsr = qrstep_conv[OF stepsr]
          let ?m = "mf + mr"
          let ?si = "\<lambda> j. if j < mf then sif j else sir (mr - (j - mf))"
          let ?ri =
            "\<lambda> j. if j < mf then (lrf j, Some True)else (lrr (mr - (j - mf) - Suc 0), Some False)"
          obtain m' where m': "m' = ?m" by auto
          obtain si' where si': "si' = ?si" by auto
          obtain ri' where ri': "ri' = ?ri" by auto
          let ?fstep = "\<lambda> j. (si' j, si' (Suc j)) \<in> rstep {(fst (ri' j))} \<and> fst (ri' j) \<in> R n"
          {
            fix j
            assume j: "j < mf"
            then have fst: "fst (ri' j) = lrf j" and sij: "si' j = sif j" 
              unfolding ri' si' by auto            
            have sisj: "?si (Suc j) = sif (Suc j)"
            proof (cases "Suc j < mf")
              case True then show ?thesis by simp
            next
              case False
              with j have "Suc j = mf" by simp
              then show ?thesis using idf idr by simp
            qed
            then have sisj: "si' (Suc j) = sif (Suc j)" unfolding si' .
            from stepsf[OF j] have "?fstep j" unfolding fst sij sisj by simp
          } note stepsf = this
          have sii: "si i = si' 0" unfolding si' m' using idf idr by (cases mf, auto)
          {
            fix j
            assume j: "j < mf"
            then have "(si ?i', si' j) \<in> S"
            proof (induct j)
              case 0
              show ?case using i'i unfolding sii .
            next
              case (Suc j)
              then have rel: "(si ?i', si' j) \<in> S" and less: "j < mf" by auto
              show ?case
              proof (rule trans_S_point[OF rel RnS])
                show "(si' j, si' (Suc j)) \<in> rstep (R n)"
                  using stepsf[OF less] using qrstep_rule_conv[where Q = "{}" and R = "R n"] by auto
              qed
            qed
          } note smallf = this              
          let ?rstep = "\<lambda> j. (si' j, si' (Suc j)) \<in> (rstep {(fst (ri' j))})\<inverse>
                    \<and> fst (ri' j) \<in> R n"
          {
            fix j
            assume j1: "\<not> j < mf" and j2: "j < m'"
            from j1 have fst: "fst (ri' j) = lrr (mr + mf - Suc j)" and 
              sij: "si' j = sir (mr + mf - j)" 
              and sisj: "si' (Suc j) = sir (mr + mf - Suc j)"
              unfolding si' ri'
              by auto
            note j2 = j2[unfolded m']
            have less: "mr + mf - Suc j < mr" using j1 j2 by arith
            have id: "Suc (mr + mf - Suc j) = mr + mf - j" using j1 j2 by arith
            from stepsr[OF less] have "?rstep j" unfolding fst sij sisj id by auto
          } note stepsr = this
          have sii'': "si ?i'' = si' m'" unfolding si' m' by (simp add: idr)
          {
            fix j
            assume j: "j < mr"
            then have "(si ?i', si' (mf + mr - j)) \<in> S"
            proof (induct j)
              case 0
              show ?case using i'i'' unfolding sii'' m' by simp
            next
              case (Suc j)
              then have rel: "(si ?i', si' (mf + mr - j)) \<in> S" and less: "j < mr" by auto
              show ?case
              proof (rule trans_S_point[OF rel RnS])
                let ?j = "mf + mr - Suc j"
                have id: "Suc ?j = mf + mr - j" using Suc(2) by auto
                from less have jm': "?j < m'" unfolding m' by auto
                from less have jmf: "\<not> ?j < mf" by auto
                from stepsr[OF jmf jm', unfolded id]
                  qrstep_rule_conv[where Q = "{}" and R = "R n"] 
                have "(si' ?j, si' (mf + mr - j)) \<in> (rstep (R n))\<inverse>" by force
                then show "(si' (mf + mr - j), si' (mf + mr - Suc j)) \<in> rstep (R n)"
                  by auto
              qed
            qed
          } note smallg = this              
          have conv: "comp_conversion (si ?i) (m', si', ri') (si ?i'')"
          proof (unfold comp_conversion.simps, intro conjI allI impI)
            show "si ?i'' = si' m'" unfolding sii'' ..
          next
            show "si i = si' 0" unfolding sii ..
          next
            fix i
            assume i: "i < m'"
            show "valid_step (si' i) (ri' i) (si' (Suc i))"
            proof (cases "i < mf")
              case True
              with stepsf[OF this]
              show ?thesis unfolding ri' by (auto simp: R_all_def)
            next
              case False
              with stepsr[OF this i] i
              show ?thesis unfolding ri' by (auto simp: R_all_def)
            qed
          qed
          show ?thesis 
          proof (intro exI conjI, rule conv, unfold ci, intro allI impI)
            fix j
            assume j: "j < m'"
            show "(?ci, c (si' j) (ri' j) (si' (Suc j))) \<in> C" (is "(_, ?c) \<in> C")
            proof (cases "j < mf")
              case True
              then have c: "?c = ([si' j], orule (lrf j))"
                unfolding ri' by simp
              from smallf[OF True] have "(si ?i', si' j) \<in> S" .
              then show ?thesis unfolding c C_def by auto
            next
              case False
              from False have  "j = mf + (j - mf)" by simp
              then obtain k where jk: "j = mf + k" by simp
              with j[unfolded m'] have kmr: "mr - k - Suc 0 < mr" by arith
              from j[unfolded m'] kmr jk
              have id: "mf + mr - (mr - k - Suc 0) = Suc (mf + k)" by auto
              from False have c: "?c = ([si' (Suc j)], orule (lrr (mr + mf - Suc j)))"
                unfolding ri' by simp
              have "(si ?i', si' (Suc j)) \<in> S" using smallg[OF kmr]
                unfolding jk id by auto
              then show ?thesis unfolding c C_def by auto              
            qed
          qed
        next
          (* case 3.2 *)
          assume "\<not> ?join \<and> ?cp"
          then obtain D b l r \<sigma> where id: "si ?i = D\<langle>l \<cdot> \<sigma>\<rangle>" "si ?i'' = D\<langle>r \<cdot> \<sigma>\<rangle>"
            and mem: "((b, l, r) \<in> ?CP \<or> (b, r, l) \<in> ?CP)" 
            and njoin: "\<not> ?join" by force
          {
            assume "(l, r) \<in> (rstep (R n))\<^sup>\<down>" (is "_ \<in> ?R\<^sup>\<down>")
            then obtain u where lu: "(l, u) \<in> ?R\<^sup>*" and ru: "(r, u) \<in> ?R\<^sup>*"
              by auto
            note D\<sigma> = rsteps_closed_ctxt[OF rsteps_closed_subst[of _ _ _ \<sigma>], of _ _ _ D]
            from D\<sigma>[OF lu] D\<sigma>[OF ru] njoin have False unfolding id by auto
          } note njoin = this
          let ?si' = "\<lambda> i' :: nat. case i' of 0 \<Rightarrow> si ?i | _ \<Rightarrow> si ?i''"
          from mem
          show ?thesis 
          proof
            assume cp: "(b, l, r) \<in> ?CP"
            from fair[OF cp] njoin have lr: "(l, r) \<in> E_all" 
              unfolding E_all_def by auto
            let ?ri' = "\<lambda> i' :: nat. ((l, r), None)"
            have conv: "comp_conversion (si ?i) (Suc 0, ?si', ?ri') (si ?i'')"
              unfolding id using lr by auto
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              using i'i i'i''
              by (auto simp: C_def id)
            show ?thesis
              by (intro exI conjI, rule conv, insert C0, auto simp: ci)
          next
            assume cp: "(b, r, l) \<in> ?CP"
            from fair[OF cp] njoin have lr: "(r, l) \<in> E_all" 
              unfolding E_all_def by auto
            let ?ri' = "\<lambda> i' :: nat. ((r, l), None)"
            have conv: "comp_conversion (si ?i) (Suc 0, ?si', ?ri') (si ?i'')"
              unfolding id using lr by auto
            have C0: "(?ci, c (?si' 0) (?ri' 0) (?si' (Suc 0))) \<in> C"
              using i'i i'i''
              by (auto simp: C_def id)
            show ?thesis
              by (intro exI conjI, rule conv, insert C0, auto simp: ci)
          qed
        qed
      qed
    qed
  qed
  let ?comp = "comp_conversion"
  let ?m = "mset"
  note id = c
  from main show ?thesis 
  proof
    assume "\<exists> i < m. ?smaller i"
    then obtain i where i: "i < m" and small: "?smaller i" by auto
    let ?c = "c (si i) (ri i) (si (Suc i))"
    let ?split = "conversion_split_three (m, si, ri) i (Suc i)"
    obtain bef cc aft where csplit: "?split = (bef, cc, aft)" by (cases ?split, force)
    from i have "i \<le> Suc i" "Suc i \<le> m" by auto
    from conversion_split_three[OF cconv this csplit]
    have bef: "?comp s bef (si i)" 
      and aft: "?comp (si (Suc i)) aft t"
      and cost_old: "cost (m, si, ri) = cost bef @ [?c] @ cost aft" by auto
    from small obtain m' si' ri' where c: "comp_conversion (si i) (m', si', ri') (si (Suc i))"
      and small: "\<And> i'. i' < m' \<Longrightarrow> (?c, 
                          c (si' i') (ri' i') (si' (Suc i'))) \<in> C" by blast
    let ?merge = "conversion_merge_three bef (m', si', ri') aft"
    from conversion_merge_three[OF bef c aft]
    have conv: "?comp s ?merge t" 
      and cost_new: "cost ?merge = cost bef @ cost (m', si', ri') @ cost aft" by auto
    let ?bef = "?m (cost bef)"
    let ?aft = "?m (cost aft)"
    let ?old = "?m [?c]"
    let ?new = "?m (cost (m', si', ri'))"
    show ?thesis unfolding id
    proof (intro exI conjI, rule conv, unfold Cost_def, rule, unfold split,
        unfold cost_old cost_new mset_append)
      have "(?bef + (?new + ?aft), ?bef + (?old + ?aft)) \<in> mult1 (C\<inverse>)" (is "(?l, ?r) \<in> _")
        unfolding mult1_def
      proof (rule, unfold split, intro exI conjI allI impI)
        have "?r = (?bef + ?aft) + {#?c#}" by (simp add: ac_simps)
        then show "mset (cost bef) + (mset [c (si i) (ri i) (si (Suc i))] +
          mset (cost aft)) = add_mset (c (si i) (ri i) (si (Suc i))) (mset (cost bef) +
          mset (cost aft))"
          by auto
      next
        show "?l = (?bef + ?aft) + ?new" by (simp add: ac_simps)
      next
        fix b
        assume "b \<in># ?new"
        then have "b \<in> set (cost (m', si', ri'))" unfolding in_multiset_in_set .
        from this[unfolded cost.simps set_map] obtain j
          where j: "j \<in> set [0..<m']" and b: "b = c (si' j) (ri' j) (si' (Suc j))"
          by auto
        from j have j: "j < m'" by auto
        from small[OF j]
        show "(b, ?c) \<in> C\<inverse>" unfolding b by simp
      qed 
      then show "(?l, ?r) \<in> mult (C\<inverse>)" unfolding mult_def by auto
    qed
  next        
    assume "\<exists> i. Suc i < m \<and> ?smaller2 i"
    then obtain i where i: "Suc i < m" and small: "?smaller2 i" by auto
    let ?c = "c (si i) (ri i) (si (Suc i))"
    let ?c' = "c (si (Suc i)) (ri (Suc i)) (si (Suc (Suc i)))"
    let ?split = "conversion_split_three (m, si, ri) i (Suc (Suc i))"
    obtain bef cc aft where csplit: "?split = (bef, cc, aft)" by (cases ?split, force)
    have id': "2 = Suc (Suc 0)" by simp
    from i have "i \<le> Suc (Suc i)" "Suc (Suc i) \<le> m" by auto
    from conversion_split_three[OF cconv this csplit]
    have bef: "?comp s bef (si i)" 
      and aft: "?comp (si (Suc (Suc i))) aft t"
      and cost_old: "cost (m, si, ri) = cost bef @ [?c, ?c'] @ cost aft" by (auto simp: id')
    from small obtain m' si' ri' where c: "comp_conversion (si i) (m', si', ri') (si (Suc (Suc i)))"
      and small: "\<And> i'. i' < m' \<Longrightarrow> (?c, 
                          c (si' i') (ri' i') (si' (Suc i'))) \<in> C" by blast
    let ?merge = "conversion_merge_three bef (m', si', ri') aft"
    from conversion_merge_three[OF bef c aft]
    have conv: "?comp s ?merge t" 
      and cost_new: "cost ?merge = cost bef @ cost (m', si', ri') @ cost aft" by auto
    let ?bef = "?m (cost bef)"
    let ?aft = "?m (cost aft)"
    let ?old = "?m [?c, ?c']"
    let ?mid = "?m [?c]"
    let ?new = "?m (cost (m', si', ri'))"
    show ?thesis unfolding id
    proof (intro exI conjI, rule conv, unfold Cost_def, rule, unfold split,
        unfold cost_old cost_new mset_append)
      have "(?bef + (?new + ?aft), ?bef + (?mid + ?aft)) \<in> mult1 (C\<inverse>)" (is "(?l, ?z) \<in> _")
        unfolding mult1_def
      proof (rule, unfold split, intro exI conjI allI impI)
        have "?z = (?bef + ?aft) + {#?c#}" by (simp add: ac_simps)
        then show "mset (cost bef) + (mset [c (si i) (ri i) (si (Suc i))] + mset (cost aft)) =
          add_mset (c (si i) (ri i) (si (Suc i))) (mset (cost bef) +
          mset (cost aft))" by auto
      next
        show "?l = (?bef + ?aft) + ?new" by (simp add: ac_simps)
      next
        fix b
        assume "b \<in># ?new"
        then have "b \<in> set (cost (m', si', ri'))" unfolding in_multiset_in_set .
        from this[unfolded cost.simps set_map] obtain j
          where j: "j \<in> set [0..<m']" and b: "b = c (si' j) (ri' j) (si' (Suc j))"
          by auto
        from j have j: "j < m'" by auto
        from small[OF j]
        show "(b, ?c) \<in> C\<inverse>" unfolding b by simp
      qed 
      also have "(?z, ?bef + (?old + ?aft)) \<in> mult1 (C\<inverse>)" (is "(_, ?r) \<in> _")
        unfolding mult1_def
        by (rule, unfold split, rule exI[of _ ?c'], rule exI[of _ ?z], rule exI[of _ "{#}"], auto simp: ac_simps)
      finally 
      show "(?l, ?r) \<in> mult (C\<inverse>)" unfolding mult_def .
    qed
  qed
qed 

lemma SN_C: "SN C"
  unfolding C_def
proof (rule lex_two[OF _ _ SN_nat_gt])
  have "SN {(a, a'). (mset a', mset a) \<in> mult1 (S\<inverse>)} = 
        wf {(a', a). (mset a', mset a) \<in> mult1 (S\<inverse>)}" (is "?goal = _")
    unfolding SN_iff_wf converse_unfold by auto
  also have "..."
    using wf_inv_image[OF wf_mult1[OF SN[unfolded SN_iff_wf]], of mset]
    unfolding inv_image_def .
  finally show ?goal .
qed auto

lemma Cost_SN: "SN Cost"
proof -
  have "SN Cost = wf {(b, a). (mset (cost b), mset (cost a)) \<in> mult (C\<inverse>)}"
    unfolding Cost_def SN_iff_wf converse_unfold
    by auto
  also have "..."
    using wf_inv_image[OF wf_mult[OF SN_C[unfolded SN_iff_wf]], of "\<lambda> x. mset (cost x)"]
    unfolding inv_image_def .
  finally show ?thesis .
qed

lemma conversion_imp_join: 
  assumes conv: "comp_conversion s conv t"
  shows "(s, t) \<in> (rstep (R n))\<^sup>\<down>"
proof -
  from conv have "\<exists> conv. comp_conversion s conv t \<and> rewrite_conversion conv" 
  proof (induct conv rule: SN_induct[OF Cost_SN])
    case (1 conv)
    show ?case
    proof (cases "rewrite_conversion conv")
      case True
      show ?thesis
        by (intro exI conjI, rule 1(2), rule True)
    next
      case False
      from proof_simplification[OF 1(2) False]
      obtain conv' where conv: "comp_conversion s conv' t" and rel: "(conv, conv') \<in> Cost" by blast
      from 1(1)[OF rel conv] show ?thesis .
    qed
  qed
  then obtain conv where conv: "comp_conversion s conv t"
    and rewr: "rewrite_conversion conv" by blast
  show ?thesis
    by (rule rewrite_conversion_imp_join[OF conv rewr])
qed      

lemma Rn_CR: "CR (rstep (R n))"
proof (rule Newman[OF Rn_SN], unfold critical_pair_lemma[of _ ren], clarify)
  fix b l r
  assume cp: "(b, l, r) \<in> critical_pairs ren (R n) (R n)"
  show "(l, r) \<in> (rstep (R n))\<^sup>\<down>" 
  proof (rule ccontr)
    assume njoin: "\<not> ?thesis"
    from fair[OF cp] njoin have lr: "(l, r) \<in> E_all" unfolding E_all_def by auto
    let ?si = "\<lambda> i :: nat. if i = 0 then l else r"
    let ?ri = "\<lambda> i :: nat. ((l, r), None)"
    have "comp_conversion l (Suc 0, ?si, ?ri) r" using lr by auto
    from conversion_imp_join[OF this] njoin
    show False by simp
  qed
qed

lemmas completion_sound = E0_Rn_conversion Rn_SN Rn_CR

end

end
