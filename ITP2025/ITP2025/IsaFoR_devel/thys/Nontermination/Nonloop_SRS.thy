(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
(* formalization of nontermination techniques of string
  rewrite systems from diploma thesis of Martin Oppelt *)
theory Nonloop_SRS 
imports 
  String_Reversal
begin

section \<open>String rewriting and its connection to term rewriting\<close>

fun term_to_string :: "('f,'v)term \<Rightarrow> 'f list" where
  "term_to_string (Fun f [t]) = f # term_to_string t"
| "term_to_string _ = []"

fun string_to_term :: "('f,'v)term \<Rightarrow> 'f list \<Rightarrow> ('f,'v)term" where
  "string_to_term d (f # fs) = Fun f [string_to_term d fs]"
| "string_to_term d [] = d"

type_synonym 'f srs_rule = "'f list \<times> 'f list"
type_synonym 'f srs = "'f srs_rule set"

definition srs_of_trs :: "('f,'v)trs \<Rightarrow> 'f srs" where
  "srs_of_trs R = {(term_to_string l, term_to_string r) | l r. (l,r) \<in> R \<and> unary_term l \<and> unary_term r}"

inductive_set srs_step :: "'f srs \<Rightarrow> 'f srs" for R where
  step: "(l,r) \<in> R \<Longrightarrow> (u @ l @ v, u @ r @ v) \<in> srs_step R" 

lemma unary_term_matching: "unary_term t \<Longrightarrow> string_to_term d (term_to_string t @ v) = t \<cdot> (\<lambda> _. string_to_term d v)"
  by (induct, auto)

lemma srs_of_trs_step: "(u, v) \<in> srs_step (srs_of_trs R) \<Longrightarrow> (string_to_term d u, string_to_term d v) \<in> rstep R"
proof (induct rule: srs_step.induct)
  case (step l r u v)
  show ?case
  proof (induct u)
    case (Cons a u)
    from rstep_ctxt[OF Cons, of "More a [] \<box> []"] show ?case by auto
  next
    case Nil
    from step[unfolded srs_of_trs_def] obtain l' r' where 
      l: "l = term_to_string l'" and r: "r = term_to_string r'" and
      lu: "unary_term l'" and ru: "unary_term r'" and lr: "(l',r') \<in> R" by auto
    show ?case unfolding l r
      by (rule rstepI[OF lr, of _ \<box> "\<lambda> _ . string_to_term d v"], 
      insert unary_term_matching[OF lu] unary_term_matching[OF ru], auto)
  qed
qed

lemma srs_of_trs_SN: assumes SN: "SN (rstep R)" shows "SN (srs_step (srs_of_trs R))"
proof 
  fix f
  assume steps: "\<forall> i. (f i, f (Suc i)) \<in> srs_step (srs_of_trs R)"
  let ?g = "\<lambda> i. string_to_term undefined (f i)"
  have "\<forall> i. (?g i, ?g (Suc i)) \<in> rstep R" using srs_of_trs_step[OF steps[rule_format]] by auto
  from chain_imp_not_SN_on[OF this] SN show False unfolding SN_on_def by blast
qed    
 
lemma srs_step_ctxtI: "(u,v) \<in> srs_step R \<Longrightarrow>
  (l @ u @ r, l @ v @ r) \<in> srs_step R"
proof (induct rule: srs_step.induct)
  case (step l' r' u v)
  from srs_step.step[OF this, of "l @ u" "v @ r"]
  show ?case by simp
qed

section \<open>Nontermination analysis\<close>

type_synonym 'f word_pat = "'f list \<times> (nat \<times> nat \<times> 'f list) \<times> 'f list"
type_synonym 'f deriv_pat = "'f word_pat \<times> 'f word_pat"


lemma trancl_srs_step_ctxtI: "(u,v) \<in> (srs_step R)^+ \<Longrightarrow>
  (l @ u @ r, l @ v @ r) \<in> (srs_step R)^+"
  by (induct rule: trancl_induct, insert srs_step_ctxtI[of _ _ R l r], force+)

lemma rtrancl_srs_step_ctxtI: "(u,v) \<in> (srs_step R)^* \<Longrightarrow>
  (l @ u @ r, l @ v @ r) \<in> (srs_step R)^*"
  by (induct rule: rtrancl_induct, insert srs_step_ctxtI[of _ _ R l r], force+)

abbreviation (input)repl_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "repl_list n xs \<equiv> concat (replicate n xs)"

lemma repl_list_left: "repl_list n l @ l @ r = l @ repl_list n l @ r"
  by (induct n, auto)

fun word_pat :: "'f word_pat \<Rightarrow> nat \<Rightarrow> 'f list" where
  "word_pat (l,(f,c,m),r) n = l @ repl_list (f * n + c) m @ r"

definition word_pat_equiv :: "'f word_pat \<Rightarrow> 'f word_pat \<Rightarrow> bool" where
  [simp]: "word_pat_equiv p1 p2 = (word_pat p1 = word_pat p2)"

abbreviation oc :: "'f list \<Rightarrow> 'f word_pat" where "oc u \<equiv> ([],(0,0,[]),u)"

locale fixed_srs =
  fixes R :: "'f srs"
begin

abbreviation RR where "RR \<equiv> (srs_step R)^+"

lemma ctxtI:
  "(u,v) \<in> RR \<Longrightarrow> (l @ u @ r, l @ v @ r) \<in> RR"
  by (rule trancl_srs_step_ctxtI)

definition deriv_pat_valid :: "'f deriv_pat \<Rightarrow> bool" where
  "deriv_pat_valid uv \<equiv> case uv of (u,v) \<Rightarrow> (\<forall> n > 0. (word_pat u n, word_pat v n) \<in> RR)" 

lemma dpI[intro]: assumes "\<And> n. n > 0 \<Longrightarrow> (word_pat u n, word_pat v n) \<in> RR"
  shows "deriv_pat_valid (u,v)" using assms unfolding deriv_pat_valid_def by auto

lemma ocI[intro]: assumes "(u,v) \<in> RR"
  shows "deriv_pat_valid (oc u, oc v)" 
  by (rule dpI, insert assms, auto)

lemma dpE[elim]: assumes "deriv_pat_valid (u,v)"
  shows "n > 0 \<Longrightarrow> (word_pat u n, word_pat v n) \<in> RR"
  using assms unfolding deriv_pat_valid_def by auto

lemma ocE[elim]: assumes "deriv_pat_valid (oc u, oc v)"
  shows "(u,v) \<in> (srs_step R)^+" using dpE[OF assms] by auto

inductive deriv_pat :: "'f deriv_pat \<Rightarrow> bool" where
  OC1: "(l,r) \<in> R \<Longrightarrow> deriv_pat (oc l, oc r)"
| OC2: "deriv_pat (oc w, oc (t @ x)) \<Longrightarrow> deriv_pat (oc (x @ l), oc r) \<Longrightarrow> deriv_pat (oc (w @ l), oc (t @ r))"
| OC2': "deriv_pat (oc w, oc (x @ t)) \<Longrightarrow> deriv_pat (oc (l @ x), oc r) \<Longrightarrow> deriv_pat (oc (l @ w), oc (r @ t))"
| OC3: "deriv_pat (oc w, oc (t1 @ x @ t2)) \<Longrightarrow> deriv_pat (oc x, oc r) \<Longrightarrow> deriv_pat (oc w, oc (t1 @ r @ t2))"
| OC3': "deriv_pat (oc (t1 @ x @ t2), oc r) \<Longrightarrow> deriv_pat (oc w, oc x) \<Longrightarrow> deriv_pat (oc (t1 @ w @ t2), oc r)"
| oc_into_dp_1: "deriv_pat (oc (l @ c), oc (c @ r)) \<Longrightarrow> deriv_pat (([], (1,0,l), c), (c, (1,0,r), []))"
| oc_into_dp_2: "deriv_pat (oc (c @ l), oc (r @ c)) \<Longrightarrow> deriv_pat ((c, (1,0,l), []), ([], (1,0,r), c))"
| wp_equiv: "word_pat_equiv left left' \<Longrightarrow> word_pat_equiv right right' \<Longrightarrow> deriv_pat (left, right) \<Longrightarrow> deriv_pat (left', right')"
| lift: "deriv_pat ((l,(f,c,m),r), (l',(f',c',m'),r')) \<Longrightarrow> deriv_pat ((l,(f,c+f,m),r), (l',(f',c'+f',m'),r'))"
| dp_oc_1_1: "deriv_pat (left, (l @ x @ r,m2,r2)) \<Longrightarrow> deriv_pat (oc x, oc v) \<Longrightarrow> deriv_pat (left, (l @ v @ r, m2, r2))"
| dp_oc_1_2: "deriv_pat ((l1,m1,r1), (x @ r,m2,r2)) \<Longrightarrow> deriv_pat (oc (l @ x), oc v) \<Longrightarrow> deriv_pat ((l @ l1,m1,r1), (v @ r, m2, r2))"
| dp_oc_2: "deriv_pat (left, (l2,(f2,c2,l @ x @ r),r2)) \<Longrightarrow> deriv_pat (oc x, oc v) \<Longrightarrow> deriv_pat (left, (l2,(f2,c2,l @ v @ r),r2))" 
| dp_oc_3_1: "deriv_pat (left, (l2,m2,l @ x @ r)) \<Longrightarrow> deriv_pat (oc x, oc v) \<Longrightarrow> deriv_pat (left, (l2,m2,l @ v @ r))"
| dp_oc_3_2: "deriv_pat ((l1,m1,r1), (l2,m2,l @ x)) \<Longrightarrow> deriv_pat (oc (x @ r), oc v) \<Longrightarrow> deriv_pat ((l1,m1,r1 @ r), (l2,m2,l @ v))"
| dp_dp_1_1: "deriv_pat (left, (l @ l2,mm,r2 @ r)) \<Longrightarrow> deriv_pat ((l2,mm,r2), (l2',mm2',r2')) 
  \<Longrightarrow> deriv_pat (left,(l @ l2', mm2', r2' @ r))"
| dp_dp_1_2: "deriv_pat ((l1', mm1', r1'), (l @ l2,mm,r1)) \<Longrightarrow> deriv_pat ((l2,mm,r1 @ r), (l2',mm2',r2')) 
  \<Longrightarrow> deriv_pat ((l1',mm1',r1' @ r),(l @ l2', mm2', r2'))"
| dp_dp_2_1: "deriv_pat ((l1', mm1', r1'), (l1,mm,r2 @ r)) \<Longrightarrow> deriv_pat ((l @ l1,mm,r2), (l2',mm2',r2')) 
  \<Longrightarrow> deriv_pat ((l @ l1',mm1',r1'),(l2', mm2', r2' @ r))"
| dp_dp_2_2: "deriv_pat ((l1', mm1', r1'), (l1,mm,r1)) \<Longrightarrow> deriv_pat ((l @ l1,mm,r1 @ r), right) 
  \<Longrightarrow> deriv_pat ((l @ l1',mm1',r1' @ r),right)"

lemma deriv_pat_valid: "deriv_pat (u,v) \<Longrightarrow> deriv_pat_valid (u,v)"
proof (induct rule: deriv_pat.induct)
  case (OC1 l r)
  from srs_step.step[OF this, of Nil Nil]
  have "(l,r) \<in> RR" by auto
  then show ?case ..
next
  case (OC2 w t x l r)
  from ctxtI[OF ocE[OF OC2(2)], of Nil l] ctxtI[OF ocE[OF OC2(4)], of t Nil]
  show ?case by auto
next
  case (OC2' w x t l r)
  from ctxtI[OF ocE[OF OC2'(2)], of l Nil] ctxtI[OF ocE[OF OC2'(4)], of Nil t]
  show ?case by auto
next
  case (OC3 w t1 x t2 r)
  from ocE[OF OC3(2)] ctxtI[OF ocE[OF OC3(4)], of t1 t2]
  show ?case by auto
next
  case (OC3' t1 x t2 r w)
  from ocE[OF OC3'(2)] ctxtI[OF ocE[OF OC3'(4)], of t1 t2]
  show ?case by auto
next
  case (oc_into_dp_1 l c r)
  note lc = ctxtI[OF ocE[OF oc_into_dp_1(2)]]
  {
    fix n
    have "n > 0 \<Longrightarrow> (concat (replicate n l) @ c, c @ concat (replicate n r)) \<in> RR"
    proof (induct n)
      case (Suc n) note IH = this(1)
      show ?case
      proof (cases n)
        case 0
        then show ?thesis using lc[of Nil Nil] by auto
      next
        case (Suc m)
        then have "n > 0" by auto
        from ctxtI[OF IH[OF this], of l Nil] lc[of Nil "concat (replicate n r)"]
        show ?thesis by simp
      qed
    qed auto
  }
  then show ?case by auto
next
  case (oc_into_dp_2 c l r)
  note lc = ctxtI[OF ocE[OF oc_into_dp_2(2)]]
  {
    fix n
    have "n > 0 \<Longrightarrow> (c @ concat (replicate n l), concat (replicate n r) @ c) \<in> RR"
    proof (induct n)
      case (Suc n) note IH = this(1)
      show ?case
      proof (cases n)
        case 0
        then show ?thesis using lc[of Nil Nil] by auto
      next
        case (Suc m)
        then have "n > 0" by auto
        from lc[of Nil "concat (replicate n l)"] ctxtI[OF IH[OF this], of r Nil] 
        show ?thesis by simp
      qed
    qed auto
  }
  then show ?case by auto
next
  case (wp_equiv left left' right right')
  from dpE[OF wp_equiv(4)] wp_equiv(1,2)  show ?case
    by (intro dpI, simp)
next
  case (lift l f c m r l' f' c' m' r')
  show ?case
  proof 
    fix n
    show "(word_pat (l, (f, c + f, m), r) n, word_pat (l', (f', c' + f', m'), r') n) \<in> RR"
      using dpE[OF lift(2), of "Suc n"] by (simp add: ac_simps)
  qed
next
  case (dp_oc_1_1 left l x r mm1 r2 v)
  obtain f c m where mm1: "mm1 = (f,c,m)" by (cases mm1) auto
  show ?case 
  proof 
    fix n
    from dpE[OF dp_oc_1_1(2), of n] ctxtI[OF ocE[OF dp_oc_1_1(4)], of l "r @ repl_list (f * n + c) m @ r2"]
    show "n > 0 \<Longrightarrow> (word_pat left n, word_pat (l @ v @ r, mm1, r2) n) \<in> RR" unfolding mm1 by auto
  qed
next
  case (dp_oc_1_2 l1 mm1 r1 x r mm2 r2 l v)
  obtain f1 c1 m1 where mm1: "mm1 = (f1,c1,m1)" by (cases mm1) auto
  obtain f2 c2 m2 where mm2: "mm2 = (f2,c2,m2)" by (cases mm2) auto
  show ?case
  proof 
    fix n
    from ctxtI[OF dpE[OF dp_oc_1_2(2), of n], of l Nil] ctxtI[OF ocE[OF dp_oc_1_2(4)], of Nil "r @ repl_list (f2 * n + c2) m2 @ r2"]
    show "n > 0 \<Longrightarrow> (word_pat (l @ l1, mm1, r1) n, word_pat (v @ r, mm2, r2) n) \<in> RR" unfolding mm1 mm2 by auto
  qed
next
  case (dp_oc_2 left l2 f2 c2 l x r r2 v)
  show ?case
  proof
    fix n
    define k where "k = f2 * n + c2"
    note xv = trancl_into_rtrancl[OF ctxtI[OF ocE[OF dp_oc_2(4)]]]
    note ctxtI = rtrancl_srs_step_ctxtI
    let ?RR = "(srs_step R)^*"
    from dp_oc_2(2) have step: "n > 0 \<Longrightarrow> (word_pat left n, word_pat (l2, (f2, c2, l @ x @ r), r2) n) \<in> RR" ..
    also have "(word_pat (l2, (f2, c2, l @ x @ r), r2) n, word_pat (l2, (f2, c2, l @ v @ r), r2) n) \<in> ?RR" 
      unfolding word_pat.simps k_def[symmetric]
    proof (rule ctxtI, induct k)
      case (Suc k)
      from ctxtI[OF Suc, of "l @ x @ r" Nil] xv[of l "r @ concat (replicate k (l @ v @ r))"]
      show ?case by auto
    qed auto
    finally
    show "n > 0 \<Longrightarrow> (word_pat left n, word_pat (l2, (f2, c2, l @ v @ r), r2) n) \<in> RR" .
  qed
next
  case (dp_oc_3_1 left l2 mm2 l x r v)
  obtain f2 c2 m2 where mm2: "mm2 = (f2,c2,m2)" by (cases mm2) auto
  show ?case
  proof 
    fix n
    from dpE[OF dp_oc_3_1(2), of n] ctxtI[OF ocE[OF dp_oc_3_1(4)], of "l2 @ repl_list (f2 * n + c2) m2 @ l" r]
    show "n > 0 \<Longrightarrow> (word_pat left n, word_pat (l2, mm2, l @ v @ r) n) \<in> RR" unfolding mm2 by auto
  qed
next
  case (dp_oc_3_2 l1 mm1 r1 l2 mm2 l x r v)
  obtain f1 c1 m1 where mm1: "mm1 = (f1,c1,m1)" by (cases mm1) auto
  obtain f2 c2 m2 where mm2: "mm2 = (f2,c2,m2)" by (cases mm2) auto
  show ?case
  proof 
    fix n
    from ctxtI[OF dpE[OF dp_oc_3_2(2), of n], of Nil r] ctxtI[OF ocE[OF dp_oc_3_2(4)], of "l2 @ repl_list (f2 * n + c2) m2 @ l" Nil]
    show "n > 0 \<Longrightarrow> (word_pat (l1, mm1, r1 @ r) n, word_pat (l2, mm2, l @ v) n) \<in> RR" unfolding mm1 mm2 by auto
  qed
next
  case (dp_dp_1_1 left l l2 mm r2 r l2' mm2' r2')
  show ?case
  proof
    fix n
    from dpE[OF dp_dp_1_1(2), of n] ctxtI[OF dpE[OF dp_dp_1_1(4), of n], of l r]
    show "n > 0 \<Longrightarrow> (word_pat left n, word_pat (l @ l2', mm2', r2' @ r) n) \<in> RR" 
      by (cases mm2', cases mm, auto)
  qed
next
  case (dp_dp_1_2 l1' mm1' r1' l l2 mm r1 r l2' mm2' r2')
  show ?case
  proof
    fix n
    from ctxtI[OF dpE[OF dp_dp_1_2(2), of n], of Nil r] ctxtI[OF dpE[OF dp_dp_1_2(4), of n], of l Nil]
    show "n > 0 \<Longrightarrow> (word_pat (l1', mm1', r1' @ r) n, word_pat (l @ l2', mm2', r2') n) \<in> RR" 
      by (cases mm1', cases mm2', cases mm, auto)
  qed
next
  case (dp_dp_2_1 l1' mm1' r1' l1 mm r2 r l l2' mm2' r2')
  show ?case
  proof
    fix n
    from ctxtI[OF dpE[OF dp_dp_2_1(2), of n], of l Nil] ctxtI[OF dpE[OF dp_dp_2_1(4), of n], of Nil r]
    show "n > 0 \<Longrightarrow> (word_pat (l @ l1', mm1', r1') n, word_pat (l2', mm2', r2' @ r) n) \<in> RR" 
      by (cases mm1', cases mm2', cases mm, auto)
  qed
next
  case (dp_dp_2_2 l1' mm1' r1' l1 mm r1 l r right)
  show ?case
  proof
    fix n
    from ctxtI[OF dpE[OF dp_dp_2_2(2), of n], of l r] dpE[OF dp_dp_2_2(4), of n]
    show "n > 0 \<Longrightarrow> (word_pat (l @ l1', mm1', r1' @ r) n, word_pat right n) \<in> RR" 
      by (cases mm1', cases mm, auto)
  qed
qed

lemma self_embed_oc: assumes oc: "deriv_pat_valid (oc x, oc (l @ x @ r))"
  shows "\<not> SN (srs_step R)"
proof 
  assume "SN (srs_step R)"
  from SN_on_trancl[OF this] have "SN RR" .
  from ocE[OF oc] have step: "(x, l @ x @ r) \<in> RR" .
  define f where "f = (\<lambda> n. repl_list n l @ x @ repl_list n r)"
  {
    fix n
    have "(f n, f (Suc n)) \<in> RR"
      unfolding f_def using ctxtI[OF step, of "repl_list n l" "repl_list n r"]
      by (simp add: repl_list_left)
  }
  with \<open>SN RR\<close> show False by blast
qed
end

(* semantic property that we require for the proof *)
definition fittable :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "fittable f1 c1 f2 c2 \<equiv> \<exists> k > 0. \<forall> n \<ge> k. \<exists> n' \<ge> k. f2 * n + c2 = f1 * n' + c1"

(* 
  sufficient criterion implemented in AProVE
*)
lemma fittableI: assumes f12: "f1 \<le> f2"
  and eq: "f1 = f2 \<Longrightarrow> c1 \<le> c2 \<and> (c2 - c1) mod f1 = 0"
  and less: "f1 < f2 \<Longrightarrow> f2 mod f1 = 0 \<and> max (c2 - c1) (c1 - c2) mod f1 = 0"
  shows "fittable f1 c1 f2 c2"
proof (cases "c1 \<le> c2")
  case True
  show ?thesis
    unfolding fittable_def
  proof (intro exI, intro conjI allI impI)
    fix n :: nat
    assume n: "n \<ge> 1"
    define c where "c = c2 - c1"
    from f12 have "f1 = f2 \<or> f1 < f2" by auto
    from this True eq less have mod: "c mod f1 = 0 \<and> f2 mod f1 = 0" unfolding c_def by (cases, auto)
    from True have c2: "c2 = c1 + c" unfolding c_def by auto
    from mod[folded c_def] obtain cf1 where c: "c = f1 * cf1" by force
    have "\<exists> f > 0. f2 = f1 * f" using mod f12 by (cases "f1 = f2", auto)
    then obtain f where f2: "f2 = f1 * f" and f: "f > 0" by auto
    let ?n = "f * n + cf1"
    have id: "f2 * n + c2 = f1 * ?n + c1" unfolding f2 c2 c
      by (auto simp: field_simps)
    from f n have n: "?n \<ge> 1" by (cases n, auto)
    show "\<exists>n' \<ge> 1. f2 * n + c2 = f1 * n' + c1" unfolding id using n by blast
  qed simp
next
  case False
  with eq have "f1 \<noteq> f2" by auto
  with f12 have f12: "f1 < f2" by auto
  define c where "c = c1 - c2"
  from less[OF f12] False have mod: "f2 mod f1 = 0" "c mod f1 = 0" unfolding c_def by auto
  from False have c1: "c1 = c + c2" unfolding c_def by auto
  from mod obtain cf1 where c: "c = f1 * cf1" by force
  with c1 False have cf1: "cf1 > 0" by auto
  show ?thesis
    unfolding fittable_def
  proof (rule exI[of _ cf1], intro conjI allI impI, rule cf1)
    fix n :: nat
    assume n: "n \<ge> cf1"
    define k where "k = n - cf1"
    have "\<exists> f > 1. f2 = f1 * f" using mod f12 by auto
    then obtain f where f2: "f2 = f1 * f" and f: "f > 1" by auto
    define f' where "f' = (f - 2) * (cf1 + k) + k + k"
    from n have n: "n = cf1 + k" unfolding k_def by simp
    have "f * (cf1 + k) = (f - 2 + 2) * (cf1 + k)"
      by (rule arg_cong[of f "f - 2 + 2"], insert f, auto)
    also have "\<dots> = cf1 + cf1 + f'" unfolding f'_def by (simp add: field_simps)
    finally have id: "f1 * f * (cf1 + k) = f1 * (cf1 + cf1 + f')" by auto
    show "\<exists>n' \<ge> cf1. f2 * n + c2 = f1 * n' + c1" unfolding f2 c1 c n id
      by (rule exI[of _ "cf1 + f'"], auto simp: field_simps)
  qed
qed

context fixed_srs
begin
lemma self_embed_dp: assumes dp: "deriv_pat_valid ((l,(f1,c1,m),r), (l' @ l,(f2,c2,m),r @ r'))"
  and fit: "fittable f1 c1 f2 c2"
  shows "\<not> SN (srs_step R)"
proof 
  assume "SN (srs_step R)"
  from SN_on_trancl[OF this] have "SN RR" .
  from fit[unfolded fittable_def] obtain k where k: "k > 0"
    and fit: "\<And> n. n \<ge> k \<Longrightarrow> \<exists>n'\<ge>k. f2 * n + c2 = f1 * n' + c1" by auto
  let ?t = "\<lambda> (n,i). repl_list i l' @ l @ repl_list (f1 * (max n k) + c1) m @ r @ repl_list i r'"
  let ?f = "\<lambda> n i n'. n' \<ge> k \<and> f2 * (max n k) + c2 = f1 * n' + c1"
  define f where "f = (\<lambda> (n,i). ((SOME n'. ?f n i n'), Suc i))"
  have "\<not> SN RR"
  proof (rule steps_imp_not_SN[of ?t f])
    fix x 
    obtain n i :: nat where x: "x = (n,i)" by force
    obtain n' where fx: "f x = (n', Suc i)" and n': "n' = (SOME n'. ?f n i n')" unfolding f_def x by auto
    let ?n = "max n k"
    have nk: "?n \<ge> k" and n0: "?n > 0" using k by auto
    from fit[OF nk]
    have "\<exists> n'. ?f n i n'" .
    from someI_ex[of "?f n i", OF this, folded n']
    have id: "f2 * ?n + c2 = f1 * n' + c1" "max n' k = n'" by auto
    from ctxtI[OF dpE[OF dp n0], of "repl_list i l'" "repl_list i r'"]
    have "(?t x, (repl_list (Suc i) l' ) @ word_pat (l, (f2, c2, m), r) ?n @ repl_list (Suc i) r') \<in> RR"
      unfolding x by (simp add: repl_list_left)
    also have "word_pat (l, (f2, c2, m), r) ?n = word_pat (l, (f1, c1, m), r) n'"
      unfolding word_pat.simps using id by simp
    finally
    show "(?t x, ?t (f x)) \<in> RR" unfolding fx using id by auto
  qed
  with \<open>SN RR\<close> show False by blast
qed
end
end
