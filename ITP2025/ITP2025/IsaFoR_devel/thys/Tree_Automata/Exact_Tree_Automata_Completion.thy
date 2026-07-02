(*
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015, 2016)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015, 2016, 2019)
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>Exact Tree Automata Completion\<close>

theory Exact_Tree_Automata_Completion
  imports
    First_Order_Rewriting.Trs
    First_Order_Rewriting.Multihole_Context
    Tree_Automata
begin

abbreviation "fground F t \<equiv> ground t \<and> funas_term t \<subseteq> F"

abbreviation "fterm \<equiv> map_funs_term Inl"

abbreviation "fctxt \<equiv> map_funs_ctxt Inl"

abbreviation "qterm \<equiv> map_funs_term Inr"

abbreviation "State f \<equiv> Fun (Inr f) []"

abbreviation "fqterm f qs \<equiv>  Fun (Inl f) (map State qs)"

type_synonym ('f, 'v) crterm = "('f + ('f, 'v) term, 'v) term"

lemma fterm_no_State: "fterm s \<noteq> State q" by (induct s) (auto)

lemma fterm_no_Inr: "fterm s \<noteq> Fun (Inr f) ts" by (induct s) (auto)

lemma fterm_contains_no_Inr: "fterm s \<noteq> C\<langle>Fun (Inr f) ts\<rangle>"
by (induct C, simp add: fterm_no_Inr) (metis fterm_no_Inr map_funs_term_ctxt_decomp)

lemma ground_term_no_State:
  assumes "ground t"
  shows "\<forall> q. fterm t \<noteq> State q"
using assms by (induct t) auto

definition ancestors :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) terms"
where
  "ancestors F R L = { t | t s. (t, s) \<in> (rstep R)\<^sup>* \<and> s \<in> L \<and> fground F t }"

lemma ancestors_lang_mono:
  "L \<subseteq> L' \<Longrightarrow> ancestors F R L \<subseteq> ancestors F R L'"
by (auto simp: ancestors_def)

lemma ancestors_refl:
  assumes "s \<in> L" and "fground F s"
  shows "s \<in> ancestors F R L"
using assms unfolding ancestors_def by blast

fun growing_rule :: "('f, 'v) rule \<Rightarrow> bool"
where
  "growing_rule (l, r) \<longleftrightarrow> (\<forall>x \<in> vars_term r. \<forall>p \<in> var_poss l. Var x = l |_ p \<longrightarrow> size p \<le> 1)"

definition "growing R \<longleftrightarrow> (\<forall>r \<in> R. growing_rule r)"

lemma Var_Fun_pos_size_One:
  assumes "Var x = Fun f ts |_ p" and "p \<in> poss (Fun f ts)" and "size p = 1"
  shows "\<exists>i < length ts. ts ! i = Var x"
using assms by (cases p) auto

fun star :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "star c (Var x) = Fun c []"
| "star c (Fun f ts) = Fun f (map (star c) ts)"

fun star_ctxt :: "'f \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) ctxt"
where
  "star_ctxt c Hole = Hole"
| "star_ctxt c (More f ss C ts) = More f (map (star c) ss) (star_ctxt c C) (map (star c) ts)"

lemma star_subst_conv:
  "star a t = t \<cdot> (\<lambda>x. Fun a [])"
by (induct t) auto

lemma star_ctxt_apply_term [simp]:
  "star c (C\<langle>t\<rangle>) = (star_ctxt c C)\<langle>star c t\<rangle>"
by (induct C) simp_all

lemma star_subst_apply_term [simp]:
  "star c (t \<cdot> \<sigma>) = t \<cdot> (star c \<circ> \<sigma>)"
by (induct t) simp_all

lemma star_rstep:
  assumes "(s, t) \<in> rstep R" shows "(star c s, star c t) \<in> rstep R"
using assms by (force)

lemma star_rsteps:
  assumes "(s, t) \<in> (rstep R)\<^sup>*" shows "(star c s, star c t) \<in> (rstep R)\<^sup>*"
using assms by (induct) (auto intro: star_rstep rtrancl_into_rtrancl)

lemma ground_star [simp]: "ground (star c t)" by (induct t) simp_all

lemma ground_star_ident [simp]:
  assumes "ground t"
  shows "star c t = t"
using assms by (induct t) (auto simp: map_idI)

lemma funas_term_star_conv:
  "funas_term (star c t) = (if ground t then funas_term t else {(c, 0)} \<union> funas_term t)"
by (induct t) (auto split: if_splits)

definition "sig_rules F c = {TA_rule f (replicate n c) c | f n. (f, n) \<in> F}"

lemma sig_rules_r_states:
  assumes "r \<in> sig_rules F c"
  shows "r_states r = { c }"
using assms
apply (auto simp: sig_rules_def)
apply (metis in_set_replicate insert_iff r_states_def ta_rule.sel(2) ta_rule.sel(3))
by (simp add: r_states_def)

fun ground_instances_rules :: "'f sig \<Rightarrow> 'f \<Rightarrow> ('f, 'v) term \<Rightarrow> (('f ,'v) term, 'f) ta_rule set"
where
  "ground_instances_rules F c (Var x) = sig_rules F (Fun c [])"
| "ground_instances_rules F c (Fun f ts) =
    {TA_rule f (map (star c) ts) (star c (Fun f ts))} \<union> \<Union>(ground_instances_rules F c ` set ts)"

lemma ground_instances_rules_mono:
  assumes "s \<unlhd> t"
  shows "ground_instances_rules F c s \<subseteq> ground_instances_rules F c t"
using assms by (induct s) auto

lemma ground_instances_rules_r_states:
  assumes "r \<in> ground_instances_rules F c t"
  shows "r_states r \<subseteq> { star c s | s. t \<unrhd> s}"
using assms
proof (induct t)
  case (Var x)
  then have "r \<in> sig_rules F (Fun c [])" by simp
  from sig_rules_r_states [OF this] have "r_states r = {Fun c []}" .
  also have "\<dots> = {star c s | s. Var x \<unrhd> s}" using supteq_Var_id by force
  finally show ?case by auto
next
  case (Fun f ts)
  with assms have "r \<in> {TA_rule f (map (star c) ts) (star c (Fun f ts))} \<union>
    \<Union>(ground_instances_rules F c ` set ts)" by simp
  moreover
  { assume "r \<in> {TA_rule f (map (star c) ts) (star c (Fun f ts))}"
    then have "r = TA_rule f (map (star c) ts) (star c (Fun f ts))" by auto
    then have "r_states r \<subseteq> { star c s | s. Fun f ts \<unrhd> s}" by (auto simp: r_states_def) force
  }
  moreover
  { fix i
    assume l: "i < length ts"
      and r: "r \<in> ground_instances_rules F c (ts ! i)"
    have i: "ts ! i \<in> set ts" using l by auto
    from Fun(1) [OF i r] have "r_states r \<subseteq> {star c s | s. ts ! i \<unrhd> s}" .
  }
  ultimately show ?case using Fun by auto fastforce
qed

definition ground_instances_ta :: "_"
  where
    "ground_instances_ta F c t =
      \<lparr> ta_final = {star c t}, ta_rules = ground_instances_rules F c t, ta_eps = {} \<rparr>"

lemma ta_eps_ground_instances_ta [simp]:
  "ta_eps (ground_instances_ta F c t) = {}"
  by (induct t) (auto simp: ground_instances_ta_def)

lemma subst_sig_term_sig_imp:
  assumes "\<forall>x \<in> vars_term t. funas_term (\<sigma> x) \<subseteq> F"
    and "funas_term t \<subseteq> F"
  shows "funas_term (t \<cdot> \<sigma>) \<subseteq> F"
  using assms by (induct t) (auto, blast)

section \<open>Tree automata\<close>
(*
The datatype for tree automata is already defined in Tree_Automata.
*)

(* A TA from a set of ta_rules with empty ta_final and ta_eps. *)
abbreviation "TA \<Delta> \<equiv> \<lparr> ta_final = {}, ta_rules = \<Delta>, ta_eps = {} \<rparr>"

abbreviation "empty_ta \<equiv> TA {}"

definition funas_ta_rule :: "('q, 'f) ta_rule \<Rightarrow> 'f sig" where
  "funas_ta_rule r = { (r_root r, length (r_lhs_states r)) }"

definition funas_ta :: "('q, 'f) ta \<Rightarrow> 'f sig" where
  "funas_ta A = \<Union>(funas_ta_rule ` ta_rules A)"

lemma ta_states_ground_instances_ta_Var [simp]:
  "ta_states (ground_instances_ta F c (Var x)) = {Fun c []}"
by (auto simp: ground_instances_ta_def sig_rules_def ta_states_def r_states_def)

lemma ta_states_ground_instances_ta_Fun [simp]:
  "ta_states (ground_instances_ta F c (Fun f ts)) =
   {star c (Fun f ts)} \<union> \<Union>(ta_states ` (ground_instances_ta F c) ` set ts)"
by (auto simp: ground_instances_ta_def sig_rules_def ta_states_def r_states_def)

definition ta_union :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q, 'f) ta"
where
  "ta_union A B = \<lparr>
    ta_final = ta_final A \<union> ta_final B,
    ta_rules = ta_rules A \<union> ta_rules B,
    ta_eps = ta_eps A \<union> ta_eps B
  \<rparr>"

definition ta_big_union :: "('q, 'f) ta set \<Rightarrow> ('q, 'f) ta"
where
  "ta_big_union T = \<lparr>
     ta_final = \<Union>(ta_final ` T),
     ta_rules = \<Union>(ta_rules ` T),
     ta_eps = \<Union>(ta_eps ` T)
   \<rparr>"

lemma ta_states_ta_big_union:
  "ta_states (ta_big_union A) = \<Union>(ta_states ` A)"
by (simp add: ta_big_union_def ta_states_def r_states_def) blast

lemma ta_union_simps [simp]:
  "ta_final (ta_union A B) = ta_final A \<union> ta_final B"
  "ta_rules (ta_union A B) = ta_rules A \<union> ta_rules B"
  "ta_eps (ta_union A B) = ta_eps A \<union> ta_eps B"
by (auto simp: ta_union_def)

lemma funas_ta_ta_union:
  assumes "funas_ta X \<subseteq> Y" and "funas_ta Z \<subseteq> W"
  shows "funas_ta (ta_union X Z) \<subseteq> Y \<union> W"
using assms by (auto simp: funas_ta_def)

lemma ta_union_comm [simp]: "ta_union A B = ta_union B A" by (auto simp: ta_union_def)

fun reachable_states :: "('q, 'f) ta \<Rightarrow> ('f + 'q, 'v) term \<Rightarrow> 'q set"
where
  "reachable_states A (Fun (Inr q) []) = { q'. (q,q') \<in> (ta_eps A)\<^sup>* }"
| "reachable_states A (Fun (Inl f) ts) = {q' | q' q qs.
    TA_rule f qs q \<in> ta_rules A \<and>
    (q,q') \<in> (ta_eps A)\<^sup>* \<and>
    length qs = length ts \<and>
    (\<forall> i < length ts. qs ! i \<in> reachable_states A (ts ! i)) }"
|  "reachable_states A _ = {}"

subsection \<open>Map ta_states\<close>

definition map_r_states :: "('q \<Rightarrow> 'r) \<Rightarrow> ('q, 'f) ta_rule \<Rightarrow> ('r, 'f) ta_rule" where
  "map_r_states f r = TA_rule (r_root r) (map f (r_lhs_states r)) (f (r_rhs r))"

lemma funas_ta_rule_map_r_states:
  assumes "funas_ta_rule r \<subseteq> Y"
  shows "funas_ta_rule (map_r_states g r) \<subseteq> Y"
using assms by (auto simp: funas_ta_rule_def map_r_states_def)

fun ta_states_term :: "('f + 'q, 'v) term \<Rightarrow> 'q set" where
  "ta_states_term (Fun (Inr q) ts) = { q } \<union> \<Union>(ta_states_term ` set ts)"
| "ta_states_term (Fun (Inl f) ts) = \<Union>(ta_states_term ` set ts)"
| "ta_states_term (Var x) = {}"

fun map_states_term :: "('q \<Rightarrow> 'r) \<Rightarrow> ('f + 'q, 'v) term \<Rightarrow> ('f + 'r, 'v) term" where
  "map_states_term g (Fun (Inr q) ts) = Fun (Inr (g q)) (map (map_states_term g) ts)"
| "map_states_term g (Fun (Inl f) ts) = Fun (Inl f) (map (map_states_term g) ts)"
| "map_states_term g (Var x) = ((Var x) :: ('f + 'r, 'v) term)"

lemma map_states_term_fterm_id [simp]:
  "map_states_term g (fterm t) = fterm t"
by (induct t) auto

lemma reachable_states_InlI:
  assumes "TA_rule f qs q \<in> ta_rules A"
    and "(q, q') \<in> (ta_eps A)\<^sup>*"
    and "length qs = length ts"
    and "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i)"
  shows "q' \<in> reachable_states A (Fun (Inl f) ts)"
using assms by auto

definition accessible :: "('q, 'f) ta \<Rightarrow> 'q \<Rightarrow> bool"
where
  "accessible A q \<longleftrightarrow> (\<exists> t :: ('f, 'v) term. ground (fterm t :: ('f + 'q, 'v) term) \<and>
                       q \<in> reachable_states A (fterm t))"

lemma accessibleE [elim]:
  assumes "accessible TYPE('v) A q"
  obtains t :: "('f, 'v) term" where "ground (fterm t)" and "q \<in> reachable_states A (fterm t)"
using assms unfolding accessible_def by auto

(* the language of an automaton *)
definition lang :: "('q, 'f) ta \<Rightarrow> ('f, 'v) terms"
where 
  "lang A = {t. ground t \<and> ta_final A \<inter> reachable_states A (fterm t) \<noteq> {}}"

lemma ta_states_ground_instances_ta:
  assumes "(a, 0) \<in> F"
  shows "ta_states (ground_instances_ta F c t) = (\<Union>r \<in> ground_instances_rules F c t. r_states r)"
using assms
apply (auto simp add: ta_states_def ground_instances_ta_def)
apply (cases t)
apply (auto intro: exI [of _ "TA_rule a (replicate 0 (Fun c [])) (Fun c [])"]
            simp: sig_rules_def r_states_def)
done

lemma funas_ta_rule_sig_rules:
  shows "\<forall>r \<in> sig_rules F c. funas_ta_rule r \<subseteq> F"
proof -
  let ?srs = "sig_rules F c"
  { fix f qs q
    assume "TA_rule f qs q \<in> ?srs"
    then have "(f, length qs) \<in> F" unfolding sig_rules_def by auto
    then have "funas_ta_rule (TA_rule f qs q) \<subseteq> F" unfolding funas_ta_rule_def by simp
  }
  then have "\<forall>r \<in> ?srs. funas_ta_rule r \<subseteq> F" unfolding sig_rules_def by blast
  then show ?thesis by simp
qed

lemma funas_ta_rule_ground_instances_rules:
  "funas_term t \<subseteq> F \<Longrightarrow> r \<in> ground_instances_rules F c t \<Longrightarrow> funas_ta_rule r \<subseteq> F"
by (induct t) (auto simp: sig_rules_def funas_ta_rule_def)

lemma funas_ta_ground_instances_ta_Var:
  shows "funas_ta (ground_instances_ta F c (Var x)) \<subseteq> F"
unfolding ground_instances_ta_def funas_ta_def
using funas_ta_rule_sig_rules [of F "Fun c []"] by auto

lemma funas_ta_ground_instances_ta:
  assumes "funas_term t \<subseteq> F"
  shows "funas_ta (ground_instances_ta F c t) \<subseteq> F"
using funas_ta_rule_ground_instances_rules [OF assms]
by (auto simp: funas_ta_def ground_instances_ta_def)

lemma ta_final_ground_instances_ta [simp]:
  "ta_final (ground_instances_ta F c t) = {star c t}"
by (auto simp: ground_instances_ta_def)

lemma reachable_states_funas_ta:
  assumes "q \<in> reachable_states A (fterm t)"
  shows "funas_term t \<subseteq> funas_ta A"
using assms
proof (induct t arbitrary: q)
  case (Var x)
  show ?case by auto
next
  case (Fun f ts)
  obtain qs q where
    rule: "TA_rule f qs q \<in> ta_rules A" and
    len: "length qs = length (map fterm ts)" and
    qs: "\<forall>i < length (map fterm ts). qs ! i \<in> reachable_states A (map fterm ts ! i)"
    using Fun(2) by auto
  have f: "(f, length ts) \<in> funas_ta A" using funas_ta_def funas_ta_rule_def rule len
    by fastforce
  { fix u
    assume **: "u \<in> set ts"
    obtain i where "u = ts ! i" and "i < length ts" using in_set_idx [OF **] by auto
    then have "qs ! i \<in> reachable_states A (fterm u)" using qs by simp
    from Fun(1) [OF ** this] have "funas_term u \<subseteq> funas_ta A" .
  }
  then have "\<forall>u \<in> set ts. funas_term u \<subseteq> funas_ta A" by auto
  then show ?case using f by auto
qed

lemma ground_instances_ta_Var [simp]:
  "lang (ground_instances_ta F c (Var x)) = {t. fground F t}" (is "?L = ?R")
proof (intro equalityI subsetI)
  fix t
  assume t: "t \<in> ?L"
  then obtain q where "q \<in> reachable_states (ground_instances_ta F c (Var x)) (fterm t)"
    unfolding lang_def by auto
  moreover have "funas_ta (ground_instances_ta F c (Var x)) \<subseteq> F"
    by (simp add: funas_ta_ground_instances_ta_Var)
  ultimately have "funas_term t \<subseteq> F" using reachable_states_funas_ta by fast
  moreover have "ground t" using t unfolding lang_def by blast
  ultimately have "fground F t" by simp
  then show "t \<in> ?R" by auto
next
  fix t
  assume t: "t \<in> ?R"
  then show "t \<in> ?L"
  proof (induct t)
    case (Fun f ts)
    { fix i
      assume "i < length ts"
      moreover then have "ts ! i \<in> {t. fground F t}" using Fun by (auto dest!: nth_mem)
      ultimately have "ts ! i \<in> lang (ground_instances_ta F c (Var x))" using Fun by auto
      then have "Fun c [] \<in> reachable_states (ground_instances_ta F c (Var x)) (fterm (ts ! i))"
        by (auto simp: lang_def)
    }
    then have "Fun c [] \<in> reachable_states (ground_instances_ta F c (Var x)) (fterm (Fun f ts))"
      using Fun(2)
      by (auto simp: ground_instances_ta_def sig_rules_def
               intro: exI [of _ "Fun c []"] exI [of _ "replicate (length ts) (Fun c [])"])
    then show ?case using Fun by (auto simp: lang_def)
  qed (auto)
qed

lemma disj_ta_states_imp_disj_ta:
  assumes "ta_states A \<inter> ta_states B = {}"
  shows "ta_final A \<inter> ta_final B = {} \<and> ta_rules A \<inter> ta_rules B = {} \<and>
    ta_eps A \<inter> ta_eps B = {}"
using assms by (auto simp: ta_states_def r_states_def)

lemma ta_epsD:
  assumes "(q, q') \<in> ta_eps A"
  shows "{q, q'} \<subseteq> ta_states A"
using assms by (auto simp: ta_states_def)

lemma trancl_ta_epsD:
  assumes "(q, q') \<in> (ta_eps A)\<^sup>+"
  shows "{q, q'} \<subseteq> ta_states A"
using assms by (induct) (auto dest: ta_epsD)

lemma disj_ta_states_imp_disj_ta_eps:
  assumes "(q, q') \<in> (ta_eps A \<union> ta_eps B)\<^sup>+" and "ta_states A \<inter> ta_states B = {}"
  shows "(q, q') \<in> (ta_eps A)\<^sup>+ \<union> (ta_eps B)\<^sup>+"
using assms
by (induct) (auto, (blast intro: trancl.trancl_into_trancl dest: trancl_ta_epsD ta_epsD)+)

lemma r_states_in_states:
  assumes "TA_rule f qs q \<in> ta_rules A"
  shows "insert q (set qs) \<subseteq> ta_states A"
using assms by (force simp: ta_states_def r_states_def)

lemma reachable_states_in_states:
  assumes "\<forall>q. t \<noteq> State q"
  shows "reachable_states A t \<subseteq> ta_states A"
using assms
  by (induct A t rule: reachable_states.induct)
     (auto dest!: rtranclD dest: r_states_in_states trancl_ta_epsD)

lemma ta_states_in_disj_rs_imp_rs:
  assumes "length qs = length ts"
    and "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
    and "ta_states A \<inter> ta_states B = {}"
    and "TA_rule f qs q' \<in> ta_rules A"
  shows "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i)"
proof -
  { fix i
    assume l: "i < length ts"
    then have *: "qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
      using assms(2) by simp
    then have "qs ! i \<in> reachable_states A (ts ! i)"
    proof
      assume rs: "qs ! i \<in> reachable_states B (ts ! i)"
      have "insert q' (set qs) \<subseteq> ta_states A" using r_states_in_states[OF assms(4)] .
      then have "qs ! i \<in> ta_states A" using l assms(1) by auto
      then have not: "qs ! i \<notin> ta_states B" using assms(3) by auto
      show "qs ! i \<in> reachable_states A (ts ! i)"
      proof (cases "\<exists>q. ts ! i = State q")
        case (True)
        then obtain q where "ts ! i = State q" by auto
        then have "(q, qs ! i) \<in> (ta_eps B)\<^sup>*" using reachable_states.simps(1)[of B q] rs by simp
        then show ?thesis
        proof (cases "q = qs ! i")
          case (True)
          then show ?thesis by (simp add: \<open>ts ! i = State q\<close>)
        next
          case (False)
          then show ?thesis using not \<open>(q, qs ! i) \<in> (ta_eps B)\<^sup>*\<close>
            by (auto simp: rtrancl_eq_or_trancl dest: trancl_ta_epsD)
        qed
      next
        case (False)
        then show ?thesis using not reachable_states_in_states rs by auto
      qed
    qed
  }
  then show ?thesis by auto
qed

lemma disj_reachable_states_eq_union:
  fixes t :: "('f + 'q, 'v) term"
  assumes "ta_states A \<inter> ta_states B = {}"
  shows "reachable_states (ta_union A B) t = reachable_states A t \<union> reachable_states B t"
  (is "?L = ?R1 \<union> ?R2")
proof (intro equalityI subsetI)
  fix q
  assume "q \<in> ?L"
  then have "q \<in> ?R1 \<or> q \<in> ?R2"
  using assms
  proof (induct "ta_union A B" t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
    case (state q1)
    then show ?case
    by (auto simp: trancl_into_rtrancl dest!: rtranclD disj_ta_states_imp_disj_ta_eps)
  next
    case ("fun" f ts)
    let ?C = "ta_union A B"
    from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules ?C" and
        eps: "(q', q) \<in> (ta_eps ?C)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states ?C (ts ! j)"
        by (auto)
    { fix i
      assume l: "i < length ts"
      from qs have "qs ! i \<in> reachable_states ?C (ts ! i)" using l by simp
      from "fun"(1)[OF l this "fun"(3)]
      have "qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)" .
    }
    then have qs':
      "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
      by simp
    have eps': "(q', q) \<in> (ta_eps A)\<^sup>* \<union> (ta_eps B)\<^sup>*" using eps "fun"(3)
      by (auto simp: trancl_into_rtrancl dest!: rtranclD disj_ta_states_imp_disj_ta_eps)
      
    from disj_ta_states_imp_disj_ta[OF "fun"(3)] have "ta_rules A \<inter> ta_rules B = {}" by auto
    then have *: "TA_rule f qs q' \<in> ta_rules A \<union> ta_rules B" using trans by (auto)
    then have "q \<in> reachable_states A (Fun (Inl f) ts) \<union> reachable_states B (Fun (Inl f) ts)"
    proof (cases "TA_rule f qs q' \<in> ta_rules A")
      case (True)
      then show ?thesis
      proof (cases "(q', q) \<in> (ta_eps A)\<^sup>*")
        case (True)
        then show ?thesis
        proof (cases "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i)")
          case (True)
          then show ?thesis
            using \<open>TA_rule f qs q' \<in> ta_rules A\<close> \<open>(q', q) \<in> (ta_eps A)\<^sup>*\<close> l'
            by auto
        next
          case (False)
          then show ?thesis
            using \<open>TA_rule f qs q' \<in> ta_rules A\<close> and qs' and "fun.prems"(2) and
            ta_states_in_disj_rs_imp_rs[OF l', of A B f q'] 
            by blast
        qed
      next
        case (False)
        then show ?thesis
        using eps' and "fun.prems"(2) and
        r_states_in_states[OF \<open>TA_rule f qs q' \<in> ta_rules A\<close>]
        by (auto simp: rtrancl_eq_or_trancl) (auto dest!: trancl_ta_epsD)
      qed
    next
      case (False)
      then have transb: "TA_rule f qs q' \<in> ta_rules B" using * by simp
      with ta_states_in_disj_rs_imp_rs[OF l', of B A f q'] fun.prems(2) qs'
        have qsb: "\<forall>i < length ts. qs ! i \<in> reachable_states B (ts ! i)" by blast
      show ?thesis
      proof (cases "(q', q) \<in> (ta_eps A)\<^sup>*")
        case (True)
        then show ?thesis
          using transb True qsb fun.prems(2) l'
          by (auto simp: rtrancl_eq_or_trancl) (auto dest!: r_states_in_states trancl_ta_epsD)
      next
        case (False)
        then have epsb: "(q', q) \<in> (ta_eps B)\<^sup>*" using eps' by auto
        with ta_states_in_disj_rs_imp_rs[OF l', of B A f q']
        show ?thesis
          using \<open>TA_rule f qs q' \<in> ta_rules B\<close> fun.prems(2) qs' l'
          by (simp only: reachable_states.simps) blast
      qed
    qed
    then show ?case by simp
  qed (auto)
  then show "q \<in> ?R1 \<union> ?R2" by simp
next
  fix q
  assume "q \<in> ?R1 \<union> ?R2"
  then show "q \<in> ?L"
  proof
    assume "q \<in> ?R1"
    then show "q \<in> ?L" using assms
    proof (induct A t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
      case (state A q1)
      then show ?case by (auto simp: in_rtrancl_UnI)
    next
      case ("fun" A f ts)
      from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules A" and
        eps: "(q', q) \<in> (ta_eps A)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states A (ts ! j)"
        by (auto)
      from trans have "TA_rule f qs q' \<in> ta_rules (ta_union A B)" by (auto)
      moreover
      from eps have "(q', q) \<in> (ta_eps (ta_union A B))\<^sup>*" by (auto simp: in_rtrancl_UnI)
      moreover
      { fix i
        assume l: "i < length ts"
        from qs have "qs ! i \<in> reachable_states A (ts ! i)" using l by simp
        from "fun"(1)[OF l this "fun"(3)]
        have "qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" .
      }
      then have "\<forall> i < length ts. qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" by simp
      ultimately show ?case using l' by auto
    qed (auto)
  next
    assume "q \<in> ?R2"
    then show "q \<in> ?L" using assms
    proof (induct B t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
      case (state B q1)
      then show ?case by (auto simp: in_rtrancl_UnI)
    next
      case ("fun" B f ts)
      from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules B" and
        eps: "(q', q) \<in> (ta_eps B)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states B (ts ! j)"
        by (auto)
      from trans have "TA_rule f qs q' \<in> ta_rules (ta_union A B)" by (auto)
      moreover
      from eps have "(q', q) \<in> (ta_eps (ta_union A B))\<^sup>*" by (auto simp: in_rtrancl_UnI)
      moreover
      { fix i
        assume l: "i < length ts"
        from qs have "qs ! i \<in> reachable_states B (ts ! i)" using l by simp
        from "fun"(1)[OF l this "fun"(3)]
        have "qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" .
      }
      then have "\<forall> i < length ts. qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" by simp
      ultimately show ?case using l' by auto
    qed (auto)
  qed
qed

lemma disj_ta_states_imp_ta_final_reachable_states_disj:
  assumes "ta_states A \<inter> ta_states B = {}"
    and "\<forall> q. t \<noteq> State q"
  shows "ta_final A \<inter> reachable_states B t = {}"
proof -
  have "ta_final A \<subseteq> ta_states A" by (simp add: ta_states_def r_states_def)
  with assms(1) reachable_states_in_states[OF assms(2), of B]
  show ?thesis by auto
qed


fun var2state :: "('f, 'v) term \<Rightarrow> ('f + 'v, 'w) term"
where
  "var2state (Var x) = Fun (Inr x) []"
| "var2state (Fun f ts) = Fun (Inl f) (map var2state ts)"

fun state2var :: "('f + 'q, 'v) term \<Rightarrow> ('f, 'q) term"
where
  "state2var (Fun (Inr q) []) = Var q"
| "state2var (Fun (Inl f) ts) = Fun f (map state2var ts)"
| "state2var _ = undefined"

lemma ta_res_reachable_states_eq:
  fixes t :: "('f, 'v) term"
  shows "ta_res A t = reachable_states A (var2state t)"
  (is "?L = ?R" is "_ = reachable_states A (?v t)")
proof (intro equalityI subsetI)
  fix q
  assume "q \<in> ?L"
  then show "q \<in> ?R"
  proof (induction t arbitrary: q)
    case (Var x)
    then show ?case by simp
  next
    case (Fun f ts)
    then have "q \<in> ta_res A (Fun f ts)" by simp
    then obtain q' qs where 1: "TA_rule f qs q' \<in> ta_rules A"
      and 2: "(q', q) \<in> (ta_eps A)\<^sup>*"
      and 3: "length qs = length ts"
      and 4: "\<forall>i<length ts. qs ! i \<in> map (ta_res A) ts ! i" by auto
    let ?ts = "map ?v ts"
    have 5: "length qs = length ?ts" using 3 by simp
    { fix i
      assume i: "i < length ts"
      then have "ts ! i \<in> set ts" by simp
      moreover from 4 have "qs ! i \<in> ta_res A (ts ! i)" using i by simp
      ultimately have "qs ! i \<in> reachable_states A (?v (ts ! i))" using Fun by simp
    }
    then have "\<forall>i<length ts. qs ! i \<in> reachable_states A (?v (ts ! i))" by blast
    then have "\<forall>i<length ?ts. qs ! i \<in> reachable_states A (map ?v ts ! i)" by simp
    with reachable_states_InlI [OF 1 2 5 this]
      have "q \<in> reachable_states A (Fun (Inl f) (map ?v ts))" by blast
    then show ?case unfolding Fun by force
  qed
next
  fix q
  assume "q \<in> ?R"
  then show "q \<in> ?L"
  proof (induct t arbitrary: q)
    case (Var x)
    then show ?case by simp
  next
    case (Fun f ts)
    let ?ts = "map ?v ts"
    from Fun have "q \<in> reachable_states A (?v (Fun f ts))" by simp
    then have "q \<in> reachable_states A (Fun (Inl f) (map ?v ts))" by auto
    then obtain q' qs where 1: "TA_rule f qs q' \<in> ta_rules A"
      and 2: "(q', q) \<in> (ta_eps A)\<^sup>*"
      and 3: "length qs = length ?ts"
      and 4: "\<forall>i<length ?ts. qs ! i \<in> reachable_states A (?ts ! i)" by auto
    have 5: "length qs = length ts" using 3 by simp
    { fix i
      assume i: "i < length ts"
      then have "ts ! i \<in> set ts" by simp
      moreover from 4 have "qs ! i \<in> reachable_states A (?v (ts ! i))" using i by simp
      ultimately have "qs ! i \<in> ta_res A (ts ! i)" using Fun(1) by simp
    }
    then have "\<forall>i<length ts. qs ! i \<in> ta_res A (ts ! i)" by simp
    then have "\<forall>i<length ts. qs ! i \<in> map (ta_res A) ts ! i" by simp
    then show ?case using 1 2 5 by auto
  qed
qed

lemma ground_fterm_var2_state [simp]:
  assumes "ground t"
  shows "fterm (adapt_vars t) = var2state t"
using assms by (induct t) (auto)

lemma ground_fterm_var2_state' [simp]:
  assumes "ground t"
  shows "fterm t = var2state t"
using assms by (induct t) (auto)

lemma ta_lang_lang_eq:
  "ta_lang A = lang A"
apply (auto simp: ta_lang_def lang_def ta_res_reachable_states_eq)
apply (subst (asm) ta_res_reachable_states_eq)
apply auto
by (metis Set.set_insert adapt_vars_adapt_vars disjoint_insert(2) ground_adapt_vars
    ground_fterm_var2_state ta_res_reachable_states_eq)

lemma lang_subseteq_lang_ta_union:
  "lang A \<subseteq> lang (ta_union A B)"
proof
  fix t :: "('a, 'b) term"
  assume "t \<in> lang A"
  then have *: "t \<in> ta_lang A" by (auto simp: ta_lang_lang_eq)
  have "ta_subset A (ta_union A B)" by (auto simp: ta_union_def ta_subset_def)
  from ta_lang_mono [OF this] * have "t \<in> ta_lang (ta_union A B)" by auto
  then show "t \<in> lang (ta_union A B)" by (auto simp: ta_lang_lang_eq)
qed

lemma lang_disj_union_eq_union_lang:
  assumes "ta_states A \<inter> ta_states B = {}"
  shows "lang (ta_union A B) = lang A \<union> lang B" (is "?L = ?R1 \<union> ?R2")
using assms
proof (intro equalityI subsetI)
  fix t
  assume "t \<in> ?L"
  moreover have "{t. ground t \<and> ta_final A \<inter> reachable_states B (fterm t) \<noteq> {}} = {}"
  and "{t. ground t \<and> ta_final B \<inter> reachable_states A (fterm t) \<noteq> {}} = {}"
    by (simp_all add: assms ac_simps ground_term_no_State
        disj_ta_states_imp_ta_final_reachable_states_disj)
  ultimately show "t \<in> ?R1 \<union> ?R2"
    by (auto simp: lang_def disj_reachable_states_eq_union assms)
next
  fix t
  assume "t \<in> ?R1 \<union> ?R2"
  then show "t \<in> ?L"
  using disj_reachable_states_eq_union[OF assms] by (auto simp: lang_def)
qed

lemma disj_union_empty_ta_final_imp_lang:
  assumes "ta_final B = {}"
    and "ta_states A \<inter> ta_states B = {}"
  shows "lang (ta_union A B) = lang A" (is "?L = ?R")
using assms lang_disj_union_eq_union_lang
by (auto simp: lang_def) (fastforce)+

subsection \<open>The one-step move relation of a tree automaton\<close>

(* the one step move relation for TAs *)
inductive_set move :: "('q, 'f) ta \<Rightarrow> ('f + 'q, 'v) term rel" for A
where
  trans: "TA_rule f qs q \<in> ta_rules A \<Longrightarrow> (C\<langle>fqterm f qs\<rangle>, C\<langle>State q\<rangle>) \<in> move A"
| eps: "(q, q') \<in> (ta_eps A)\<^sup>* \<Longrightarrow> (C\<langle>State q\<rangle>, C\<langle>State q'\<rangle>) \<in> move A"

lemma move_eps:
  "(q, q') \<in> (ta_eps A)\<^sup>* \<Longrightarrow> (State q, State q') \<in> move A"
using move.eps [of q q' A \<box>] by auto

lemma move_eps':
  "(q, q') \<in> ta_eps A \<Longrightarrow> (State q, State q') \<in> move A"
using move_eps [of q q' A] by auto

(* the set of terms from which a given state is reachable in a given TA *)
abbreviation sterms :: "'v itself \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q \<Rightarrow> ('f + 'q, 'v) term set"
where
  "sterms x A q \<equiv> {t | t :: ('f + 'q, 'v) term. (t, State q) \<in> (move A)\<^sup>*}"

abbreviation (input) state :: "'v itself \<Rightarrow> 'q \<Rightarrow> ('f + 'q, 'v) term"
where
  "state x q \<equiv> State q"

lemma apply_ctxt_term_fqterm_ne_State [simp]:
  "C\<langle>fqterm f qs\<rangle> \<noteq> State p"
by (cases C) auto

lemma apply_ctxt_term_State:
  "C\<langle>State p\<rangle> = State q \<Longrightarrow> C = \<box> \<and> q = p"
by (cases C) auto

lemma State_move_imp_eps:
  assumes "(State p, State q) \<in> move A"
  shows "(p, q) \<in> (ta_eps A)\<^sup>*"
using assms by (auto elim!: move.cases dest!: apply_ctxt_term_State)

lemma State_move_imp_State:
  assumes "(State p, t) \<in> move A"
  obtains q where "t = State q"
using assms by (auto elim!: move.cases dest!: apply_ctxt_term_State)

lemma State_moves_imp_State:
  assumes "(State p, t) \<in> (move A)\<^sup>*"
  obtains q where "t = State q"
using assms by (induct) (auto elim: State_move_imp_State)

lemma State_moves_imp_eps:
  assumes "(State p, State q) \<in> (move A)\<^sup>*"
  shows "(p, q) \<in> (ta_eps A)\<^sup>*"
using assms
by (induct "State p :: ('a + 'b, 'c) term" "State q :: ('a + 'b, 'c) term" arbitrary: q)
   (auto elim!: State_moves_imp_State dest: State_move_imp_eps rtrancl_trans)

lemma State_move_trancl_imp_ta_states:
  assumes "(State p, State q) \<in> (move A)\<^sup>+" and "p \<noteq> q"
  shows "{p, q} \<subseteq> ta_states A"
proof -
  have "(p, q) \<in> (ta_eps A)\<^sup>+"
    using assms
    apply (cases "p = q") apply (auto)
    by (metis State_moves_imp_eps r_into_rtrancl rtranclD trancl_rtrancl_absorb)
  then show ?thesis by (auto dest: trancl_ta_epsD)
qed

lemma eps_ta_union_trancl_cases:
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
    and "(q, q') \<in> (ta_eps A \<union> ta_eps B)\<^sup>+"
  shows "(q, q') \<in> (ta_eps A)\<^sup>+ \<or> (q, q') \<in> (ta_eps B)\<^sup>+"
using assms(2)
proof (induct)
  case (base p)
  then show ?case by (auto simp: ta_union_def intro: move_eps)
next
  case (step p p')
  let ?sterms = "sterms TYPE('v)"
  let ?p = "State p :: ('b + 'a, 'v) term"
  let ?q = "State q :: ('b + 'a, 'v) term"
  let ?p' = "State p' :: ('b + 'a, 'v) term"
  consider "(q, p) \<in> (ta_eps A)\<^sup>+" and "(p, p') \<in> ta_eps A"
    | "(q, p) \<in> (ta_eps A)\<^sup>+" and "(p, p') \<in> ta_eps B"
    | "(q, p) \<in> (ta_eps B)\<^sup>+" and "(p, p') \<in> ta_eps A"
    | "(q, p) \<in> (ta_eps B)\<^sup>+" and "(p, p') \<in> ta_eps B" using step by auto
  then show ?case
  proof (cases)
    case (2)
    show ?thesis
    proof (cases "p = q")
      case True
      then show ?thesis using 2 by (auto simp: move_eps r_into_rtrancl r_into_trancl')
    next
      case False
      from 2 have "(?q, ?p) \<in> (move A)\<^sup>+" by (simp add: move_eps r_into_trancl' trancl_into_rtrancl)
      with State_move_trancl_imp_ta_states [of q p A] and False and 2
        have "p \<in> ta_states A \<inter> ta_states B" by (auto dest: ta_epsD)
      with assms(1) have "?sterms A p = ?sterms B p" by auto
      with 2 have *: "(State q, State p) \<in> (move B)\<^sup>+"
        by auto (metis State_moves_imp_eps mem_Collect_eq move_eps r_into_rtrancl r_into_trancl'
                 trancl_rtrancl_absorb)
      have "(State q, State p) \<in> (move B)\<^sup>*" by (simp add: * trancl_into_rtrancl)
      from State_moves_imp_eps [OF this] have "(q, p) \<in> (ta_eps B)\<^sup>*" .
      with 2 have "(q, p') \<in> (ta_eps B)\<^sup>+" by force
      then show ?thesis by (auto)
    qed
  next
    case (3)
    show ?thesis
    proof (cases "p = q")
      case True
      then show ?thesis using 3 by (auto simp: move_eps r_into_rtrancl r_into_trancl')
    next
      case False
      from 3 have "(?q, ?p) \<in> (move B)\<^sup>+" by (simp add: move_eps r_into_trancl' trancl_into_rtrancl)
      with State_move_trancl_imp_ta_states [of q p B] and False and 3
        have "p \<in> ta_states A \<inter> ta_states B" by (auto dest: ta_epsD)
      with assms(1) have "?sterms A p = ?sterms B p" by auto
      with 3 have *: "(State q, State p) \<in> (move A)\<^sup>+"
        by auto (metis State_moves_imp_eps mem_Collect_eq move_eps r_into_rtrancl r_into_trancl'
                 trancl_rtrancl_absorb)
      have "(State q, State p) \<in> (move A)\<^sup>*" by (simp add: * trancl_into_rtrancl)
      from State_moves_imp_eps [OF this] have "(q, p) \<in> (ta_eps A)\<^sup>*" .
      with 3 have "(q, p') \<in> (ta_eps A)\<^sup>+" by force
      then show ?thesis by (auto)
    qed
  qed (auto dest: move_eps' trancl_into_trancl)
qed

lemma State_move_imp_State':
  assumes "(State q, s) \<in> move A"
  shows "\<exists> q'. s = State q'"
proof -
  { fix l
    assume "(l, s) \<in> move A" and "l = State q"
    then have ?thesis
      apply (induct l s rule: move.induct)
      subgoal using apply_ctxt_term_State by fastforce
      subgoal using apply_ctxt_term_State by fastforce
      done
  }
  with assms show ?thesis by simp
qed

lemma State_move_seq_imp_State:
  assumes "(State q, s) \<in> (move A)\<^sup>*"
  shows "\<exists> q'. s = State q'"
proof -
  { fix l
    assume "(l, s) \<in> (move A)\<^sup>*" and "l = State q"
    then have ?thesis
    by (induct) (auto simp: State_move_imp_State')
  }
  with assms show ?thesis by blast
qed

lemma ta_eps_reachable_states:
  assumes "p \<in> reachable_states A t" and "(p, q) \<in> (ta_eps A)\<^sup>*"
  shows "q \<in> reachable_states A t"
using assms
by (induct t rule: reachable_states.induct) (auto, meson rtrancl_trans)

lemma move_ground_ground:
  assumes "(s, t) \<in> move A" and "ground t"
  shows "ground s"
using assms
by (induct rule: move.induct) (simp add: move.intros)+

lemma rtrancl_move_ground_ground:
  assumes "(s, t) \<in> (move A)\<^sup>*" and "ground t"
  shows "ground s"
using assms move_ground_ground
by (induct) (auto)

lemma no_non_ground_move:
  assumes "\<not> ground s" and "ground t"
  shows "(s, t) \<notin> move A"
using assms rtrancl_move_ground_ground by auto

lemma distr_move':
  assumes "(s, Fun (Inl f) ts) \<in> move A"
  shows "\<exists>ss. s = Fun (Inl f) ss \<and> length ts = length ss \<and>
    (\<forall>i < length ss. ss ! i = ts ! i \<or> (ss ! i, ts ! i) \<in> move A)"
proof -
  { fix C q v E
    assume move: "(\<exists>q'. v = State q' \<and> (q', q) \<in> (ta_eps A)\<^sup>*)
        \<or> (\<exists>g qs. v = fqterm  g qs \<and> TA_rule g qs q \<in> ta_rules A)"
      and s: "s = C\<langle>v\<rangle>"
      and C: "Fun (Inl f) ts = C\<langle>State q\<rangle>"
    from C obtain us vs D where D: "C = More (Inl f) us D vs" by (cases C) (auto)
    with s obtain ss where 1: "s = Fun (Inl f) ss" by simp
    from D s 1 have ss: "ss = us @ D\<langle>v\<rangle> # vs" by simp
    then obtain i where iD: "ss ! i = D\<langle>v\<rangle>"
      and us: "take i ss = us" and vs: "drop (Suc i) ss = vs"
      using nth_append_length by fastforce
    from C D have *: "ts = us @ D\<langle>State q\<rangle> # vs" by auto
    { fix j
      assume "j < length ss"
      from us ss not_le have len: "length us = i" by fastforce
      have "ss ! j = ts ! j \<or> (ss ! j, ts ! j) \<in> move A"
      proof (cases "j = i")
        case (True)
        then show ?thesis
          using move move.trans * len iD by (fastforce simp: move.eps r_into_rtrancl)
      qed (simp add: * len append_Cons_nth_not_middle rtrancl_eq_or_trancl ss)
    }
    then have "\<exists> ss. ?thesis" by (simp add: * 1 ss)
  }
  then have
    "\<And> C q v. (\<exists>q'. v = State q' \<and> (q', q) \<in> (ta_eps A)\<^sup>*) \<or>
      (\<exists>g qs. v = fqterm g qs \<and> TA_rule g qs q \<in> ta_rules A) \<Longrightarrow>
      Fun (Inl f) ts = C\<langle>State q\<rangle> \<Longrightarrow> s = C\<langle>v\<rangle> \<Longrightarrow>
      \<exists>ss. s = Fun (Inl f) ss \<and> length ts = length ss \<and> 
      (\<forall>i < length ss. ss ! i = ts ! i \<or> (ss ! i, ts ! i) \<in> move A)" by auto
  with assms show ?thesis by (cases rule: move.cases) (blast)+
qed

lemma distr_move:
  assumes "(s, Fun (Inl f) ts) \<in> move A"
  shows "\<exists>ss. s = Fun (Inl f) ss \<and> length ts = length ss \<and>
    (\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*)"
using distr_move' [OF assms] by fastforce

lemma distr_moves':
  assumes "(s, Fun (Inl f) ts) \<in> (move A)\<^sup>+"
  shows "\<exists>ss. s = Fun (Inl f) ss \<and> length ts = length ss \<and>
    (\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*)"
using assms
by (induct s "Fun (Inl f) ts" arbitrary: ts rule: trancl.induct)
   (auto dest!: distr_move, metis (mono_tags) rtrancl_trans)

lemma distr_moves:
  assumes "(s, Fun (Inl f) ts) \<in> (move A)\<^sup>*"
  shows "\<exists>ss. s = Fun (Inl f) ss \<and> length ts = length ss \<and>
    (\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*)"
using assms
by (induct s "Fun (Inl f) ts" arbitrary: ts rule: rtrancl.induct)
   (auto dest!: distr_move, metis (mono_tags) rtrancl_trans)


lemma move_ctxt:
  assumes "(s, t) \<in> move A"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> move A"
proof -
  note * = move.intros(1)[of _ _ _ _ "C \<circ>\<^sub>c D" for C D, simplified]
           move.intros(2)[of _ _ _ "C \<circ>\<^sub>c D" for C D, simplified]
  show ?thesis using assms
    by (induct) (auto intro: *)
qed

lemma move_ctxt_rtrancl:
  assumes "(s, t) \<in> (move A)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (move A)\<^sup>*"
using assms by (induct) (auto simp: move_ctxt rtrancl.rtrancl_into_rtrancl)

lemma move_ctxt_trancl:
  assumes "(s, t) \<in> (move A)\<^sup>+"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (move A)\<^sup>+"
using assms by (induct) (auto simp: move_ctxt trancl_into_trancl)

lemma ctxt_closed_move: "ctxt.closed (move A)"
proof
  fix s t :: "('a + 'b, 'd) term" and C
  assume "(s, t) \<in> move A"
  then show "(s, t) \<in> move A \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> move A" by (rule move_ctxt)
qed

lemma move_reachable_states:
  "(t, State q) \<in> (move A)\<^sup>* \<longleftrightarrow> q \<in> reachable_states A t" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then show ?R
  proof (induct t arbitrary: q)
    case (Var x)
    with rtrancl_move_ground_ground show ?case by fastforce
  next
    case (Fun f ts)
    note IH = this(1)
    {
      fix l r q
      assume "(l, r) \<in> (move A)\<^sup>*" (is "(_, _) \<in> ?move\<^sup>*") "l = Fun f ts" "r = State q"
      then have "q \<in> reachable_states A (Fun f ts)"
      proof (induct l r arbitrary: q rule: rtrancl.induct[case_names refl step])
        case (step l m r)
        show ?case using step(3,1,2) unfolding step(4,5)
        proof (induct rule: move.cases)
          case (trans f' qs q2 C)
          with apply_ctxt_term_State have "C = \<box>" by metis
          show ?case
          proof (cases m)
            case (Fun g ps)
            then show ?thesis
            proof (cases "\<exists> p. m = State p")
              case (True)
              from True obtain p where True: "m = State p" ..
              from step(2)[OF step(4) True] have 1: "p \<in> reachable_states A (Fun f ts)" .
              from step(3) True step(5) have "(State p, State q) \<in> ?move" by auto
              from State_move_imp_eps[OF this] have 2: "(p, q) \<in> (ta_eps A)\<^sup>*" .
              from ta_eps_reachable_states[OF 1 2] show ?thesis .
            next
              case (False)
              then show ?thesis
              proof (cases "\<exists> h x xs. m = Fun (Inr h) (x # xs)")
                case (False)
                then obtain a us where "m = Fun a us" by (simp add: \<open>C = \<box>\<close> trans)
                from this trans(1) \<open>C = \<box>\<close> have "Fun a us = fqterm f' qs" by simp
                then have "a = Inl f'" and "us = map State qs" by auto
                with \<open>m = Fun a us\<close> have "m = Fun (Inl f') us" by simp
                with step(1) have "(l, Fun (Inl f') us) \<in> ?move\<^sup>*" by simp
                from distr_moves[OF this] obtain ss where "l = Fun (Inl f') ss"
                  and "length us = length ss"
                  and  *: "\<forall>i < length ss. (ss ! i, us ! i) \<in> ?move\<^sup>*" by auto
                from \<open>l = Fun (Inl f') ss\<close> step(4) have "ss = ts" and "f = Inl f'" by auto
                have "a = f" using \<open>a = Inl f'\<close> \<open>f = Inl f'\<close> by simp
                then have "(Fun f ss, Fun f (map State qs)) \<in> ?move\<^sup>*"
                  using \<open>l = Fun (Inl f') ss\<close> \<open>m = Fun a us\<close> \<open>us = map State qs\<close> step
                  by simp
                from * have **: "\<forall>i < length ts. (ts ! i, (map State qs) ! i) \<in> ?move\<^sup>*"
                  by (simp add: \<open>ss = ts\<close> \<open>us = map State qs\<close>)
                { fix i
                  assume len: "i < length ts"
                  then have ti: "ts ! i \<in> set ts" by simp
                  from len ** have qi: "(ts ! i, (map State qs) ! i) \<in> ?move\<^sup>*" by simp
                  with IH[OF ti]
                  have "qs ! i \<in> reachable_states A (ts ! i)"
                    using \<open>length us = length ss\<close> \<open>ss = ts\<close> \<open>us = map State qs\<close> len by auto
                }
                then have "\<forall> i < length ts. qs ! i \<in> reachable_states A (ts ! i)" by auto
                then show ?thesis
                  using \<open>f = Inl f'\<close> \<open>C = \<box>\<close> \<open>length us = length ss\<close> \<open>ss = ts\<close> \<open>us = map State qs\<close>
                  trans by auto
              qed (auto simp: trans \<open>C = \<box>\<close>)
            qed
          qed (auto simp: trans \<open>C = \<box>\<close>)
        next
          case (eps q1 q2 C)
          then show ?case by (cases C, cases f; cases ts) (auto, (metis rtrancl_trans)+)
        qed
      qed auto
    }
    then show ?case using Fun(2) by blast
  qed
next
  assume ?R
  then show ?L
  proof (induct t arbitrary: q rule: reachable_states.induct)
    case (1 A q')
    then show ?case
    using move.intros(2)[of q' q A "\<box>"] by auto
  next
    case (2 A f ts q')
    obtain q qs where trans: "TA_rule f qs q \<in> ta_rules A"
      and eps: "(q, q') \<in> (ta_eps A)\<^sup>*"
      and len: "length qs = length ts"
      and rec: "\<forall> i < length ts. qs ! i \<in> reachable_states A (ts ! i)"
        using 2(2) by auto
    have len': "length ts = length (map State qs)" using len by auto
    have rec': "\<forall>i < length ts. (ts ! i, map State qs ! i) \<in> (move A)\<^sup>*"
      by (simp add: rec "2.hyps" len)
    have 1: "(Fun (Inl f) ts, fqterm f qs) \<in> (move A)\<^sup>*"
      using args_steps_imp_steps[OF ctxt_closed_move len' rec', of "Inl f"] by simp
    have 2: "(fqterm f qs, State q) \<in> move A" using move.intros(1)[OF trans, of "\<box>"]  by simp
    have "(State q, State q') \<in> move A" using move.intros(2)[OF eps, of "\<box>"] by simp
    then have 3: "(State q, State q') \<in> (move A)\<^sup>*" by auto
    show ?case using rtrancl_trans[OF rtrancl.rtrancl_into_rtrancl[OF 1 2] 3] .
  qed (auto)
qed

lemma ta_states_in_rs_imp_rs:
  fixes ts :: "('f + 'q, 'v) term list"
  assumes "length qs = length ts"
    and "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
    and "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
    and "TA_rule f qs q' \<in> ta_rules A"
  shows "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i)"
proof -
  { fix i
    assume l: "i < length ts"
    then have *: "qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
      using assms(2) by simp
    then have "qs ! i \<in> reachable_states A (ts ! i)"
    proof
      assume rs: "qs ! i \<in> reachable_states B (ts ! i)"
      have **: "insert q' (set qs) \<subseteq> ta_states A" using r_states_in_states[OF assms(4)] .
      then have "qs ! i \<in> ta_states A" using l assms(1) by auto
      show "qs ! i \<in> reachable_states A (ts ! i)"
      proof (cases "\<exists>q. ts ! i = State q")
        case (True)
        then obtain q where q: "ts ! i = State q" by auto
        then have "(q, qs ! i) \<in> (ta_eps B)\<^sup>*" using reachable_states.simps(1)[of B q] rs by simp
        then show ?thesis
        proof (cases "q = qs ! i")
          case (True)
          then show ?thesis by (simp add: \<open>ts ! i = State q\<close>)
        next
          case (False)
          with \<open>(q, qs ! i) \<in> (ta_eps B)\<^sup>*\<close> have ***: "(q, qs ! i) \<in> (ta_eps B)\<^sup>+"
            by (auto dest: rtranclD)
          then have "qs ! i \<in> ta_states A \<inter> ta_states B" using ** l assms(1)
            using \<open>qs ! i \<in> ta_states A\<close> trancl_ta_epsD by fastforce
          moreover from *** have "(state TYPE('v) q, state TYPE('v) (qs ! i)) \<in> (move B)\<^sup>*"
            by (simp add: \<open>(q, qs ! i) \<in> (ta_eps B)\<^sup>*\<close> move_eps r_into_rtrancl) 
          ultimately have "(state TYPE('v) q, state TYPE('v) (qs ! i)) \<in> (move A)\<^sup>*"
            using assms(3) by auto
          then show ?thesis by (auto simp: q move_reachable_states)
        qed
      next
        case (False)
        with reachable_states_in_states rs have "qs ! i \<in> ta_states B" by auto
        then have "qs ! i \<in> ta_states A \<inter> ta_states B" using ** l assms(1) by auto
        moreover have "(ts ! i, state TYPE('v) (qs ! i)) \<in> (move B)\<^sup>*" using rs
          by (auto simp: move_reachable_states)
        ultimately have "(ts ! i, state TYPE('v) (qs ! i)) \<in> (move A)\<^sup>*"
          using assms(3) by auto
        then show ?thesis by (auto simp: move_reachable_states)
      qed
    qed
  }
  then show ?thesis by auto
qed

lemma reachable_states_union:
  fixes t :: "('f + 'q, 'v) term"
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
  shows "reachable_states (ta_union A B) t = reachable_states A t \<union> reachable_states B t"
  (is "?L = ?R1 \<union> ?R2")
proof (intro equalityI subsetI)
  from assms have s: "\<forall>q \<in> ta_states B \<inter> ta_states A. sterms TYPE('v) B q = sterms TYPE('v) A q" by auto
  fix q
  assume "q \<in> ?L"
  then have "q \<in> ?R1 \<or> q \<in> ?R2"
  proof (induct "ta_union A B" t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
    case (state q1)
    then have *: "(q1 , q) \<in> (ta_eps (ta_union A B))\<^sup>*" by simp
    show ?case
    proof (cases "q1 = q")
      case (False)
      with * have "(q1 , q) \<in> (ta_eps A \<union> ta_eps B)\<^sup>+" by (auto dest: rtranclD)
      from eps_ta_union_trancl_cases [OF assms this]
        show ?thesis using trancl_into_rtrancl by fastforce 
    qed (simp)
  next
    case ("fun" f ts)
    let ?C = "ta_union A B"
    from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules ?C" and
        eps: "(q', q) \<in> (ta_eps ?C)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states ?C (ts ! j)"
        by (auto)
    { fix i
      assume l: "i < length ts"
      from qs have "qs ! i \<in> reachable_states ?C (ts ! i)" using l by simp
      from "fun"(1)[OF l this]
        have "qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)" .
    }
    then have qs':
      "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i) \<or> qs ! i \<in> reachable_states B (ts ! i)"
      by simp
    then have qs'':
      "\<forall>i < length ts. qs ! i \<in> reachable_states B (ts ! i) \<or> qs ! i \<in> reachable_states A (ts ! i)"
      by blast
    have eps': "(q', q) \<in> (ta_eps A)\<^sup>* \<union> (ta_eps B)\<^sup>*"
    proof (cases "q' = q")
      case (False)
      with eps have "(q' , q) \<in> (ta_eps A \<union> ta_eps B)\<^sup>+" by (auto dest: rtranclD)
      from eps_ta_union_trancl_cases [OF assms this]
        show ?thesis using trancl_into_rtrancl by fastforce 
    qed (simp)
    then have *: "TA_rule f qs q' \<in> ta_rules A \<union> ta_rules B" using trans by (auto)
    let ?rule = "\<lambda>A :: ('q, 'f) ta. TA_rule f qs q' \<in> ta_rules A"
    let ?eps = "\<lambda>A :: ('q, 'f) ta. (q', q) \<in> (ta_eps A)\<^sup>*"
    consider (AA) "?rule A" and "?eps A"
           | (AB) "?rule A" and "?eps B"
           | (BA) "?rule B" and "?eps A"
           | (BB) "?rule B" and "?eps B" using eps' * by auto
    then have "q \<in> reachable_states A (Fun (Inl f) ts) \<union> reachable_states B (Fun (Inl f) ts)"
    proof (cases)
      case (AA)
      then show ?thesis using ta_states_in_rs_imp_rs[OF l' qs' assms, of f q']
        and UnI1 and l' and reachable_states_InlI by auto
    next
      case (AB)
      with r_states_in_states have **: "q' \<in> ta_states A" using insert_subset by fastforce
      from ta_states_in_rs_imp_rs[OF l' qs' assms AB(1)]
        have *: "\<forall>i < length ts. qs ! i \<in> reachable_states A (ts ! i)" .
      show ?thesis
      proof (cases "q' = q")
        case (True)
        with AB * l' show ?thesis by auto
      next
        case (False)
        with AB ** have q': "q' \<in> ta_states A \<inter> ta_states B" by (auto dest: rtranclD trancl_ta_epsD)
        have "\<forall>i < length ts. (ts ! i, (map (state TYPE('v)) qs) ! i) \<in> (move A)\<^sup>*"
          using * by (auto simp: l' move_reachable_states) 
        from args_steps_imp_steps [OF ctxt_closed_move _ this, of "Inl f"]
          have "(Fun (Inl f) ts, fqterm f qs) \<in> (move A)\<^sup>*" by (simp add: l')
        moreover have "(fqterm f qs, state TYPE('v) q') \<in> (move A)\<^sup>*"
          using move.intros(1) [OF AB(1), of \<box>] by auto
        ultimately have "(Fun (Inl f) ts, state TYPE('v) q') \<in> (move A)\<^sup>*" by auto
        with bspec [OF assms q']
          have "(Fun (Inl f) ts, state TYPE('v) q') \<in> (move B)\<^sup>*" by auto
        with AB(2) have "(Fun (Inl f) ts, state TYPE('v) q) \<in> (move B)\<^sup>*"
          by (simp add: move_eps rtrancl.rtrancl_into_rtrancl) 
        then show ?thesis by (auto simp: move_reachable_states) 
      qed
    next
      case (BA)
      with r_states_in_states have **: "q' \<in> ta_states B" using insert_subset by fastforce
      from ta_states_in_rs_imp_rs[OF l' qs'' s BA(1)]
        have *: "\<forall>i < length ts. qs ! i \<in> reachable_states B (ts ! i)" .
      show ?thesis
      proof (cases "q' = q")
        case (True)
        with BA * l' show ?thesis by auto
      next
        case (False)
        with BA ** have q': "q' \<in> ta_states A \<inter> ta_states B" by (auto dest: rtranclD trancl_ta_epsD)
        have "\<forall>i < length ts. (ts ! i, (map (state TYPE('v)) qs) ! i) \<in> (move B)\<^sup>*"
          using * by (auto simp: l' move_reachable_states) 
        from args_steps_imp_steps [OF ctxt_closed_move _ this, of "Inl f"]
          have "(Fun (Inl f) ts, fqterm f qs) \<in> (move B)\<^sup>*" by (simp add: l')
        moreover have "(fqterm f qs, state TYPE('v) q') \<in> (move B)\<^sup>*"
          using move.intros(1) [OF BA(1), of \<box>] by auto
        ultimately have "(Fun (Inl f) ts, state TYPE('v) q') \<in> (move B)\<^sup>*" by auto
        with bspec [OF assms q']
          have "(Fun (Inl f) ts, state TYPE('v) q') \<in> (move A)\<^sup>*" by auto
        with BA(2) have "(Fun (Inl f) ts, state TYPE('v) q) \<in> (move A)\<^sup>*"
          by (simp add: move_eps rtrancl.rtrancl_into_rtrancl) 
        then show ?thesis by (auto simp: move_reachable_states) 
      qed
    next
      case (BB)
      then show ?thesis using ta_states_in_rs_imp_rs[OF l' qs'' s, of f q']
        and UnI1 and l' and reachable_states_InlI by auto
    qed
    then show ?case by simp
  qed (auto)
  then show "q \<in> ?R1 \<union> ?R2" by simp
next
  fix q
  assume "q \<in> ?R1 \<union> ?R2"
  then show "q \<in> ?L"
  proof
    assume "q \<in> ?R1"
    then show "q \<in> ?L" using assms
    proof (induct A t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
      case (state A q1)
      then show ?case by (auto simp: in_rtrancl_UnI)
    next
      case ("fun" A f ts)
      from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules A" and
        eps: "(q', q) \<in> (ta_eps A)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states A (ts ! j)"
        by (auto)
      from trans have "TA_rule f qs q' \<in> ta_rules (ta_union A B)" by (auto)
      moreover
      from eps have "(q', q) \<in> (ta_eps (ta_union A B))\<^sup>*" by (auto simp: in_rtrancl_UnI)
      moreover
      { fix i
        assume l: "i < length ts"
        from qs have "qs ! i \<in> reachable_states A (ts ! i)" using l by simp
        from "fun"(1)[OF l this "fun"(3)]
        have "qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" .
      }
      then have "\<forall> i < length ts. qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" by simp
      ultimately show ?case using l' by auto
    qed (auto)
  next
    assume "q \<in> ?R2"
    then show "q \<in> ?L" using assms
    proof (induct B t arbitrary: q rule: reachable_states.induct[case_names state "fun"])
      case (state B q1)
      then show ?case by (auto simp: in_rtrancl_UnI)
    next
      case ("fun" B f ts)
      from "fun"(2) obtain q' qs where trans: "TA_rule f qs q' \<in> ta_rules B" and
        eps: "(q', q) \<in> (ta_eps B)\<^sup>*" and l': "length qs = length ts" and
        qs: "\<forall>j < length ts. qs ! j \<in> reachable_states B (ts ! j)"
        by (auto)
      from trans have "TA_rule f qs q' \<in> ta_rules (ta_union A B)" by (auto)
      moreover
      from eps have "(q', q) \<in> (ta_eps (ta_union A B))\<^sup>*" by (auto simp: in_rtrancl_UnI)
      moreover
      { fix i
        assume l: "i < length ts"
        from qs have "qs ! i \<in> reachable_states B (ts ! i)" using l by simp
        from "fun"(1)[OF l this "fun"(3)]
        have "qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" .
      }
      then have "\<forall> i < length ts. qs ! i \<in> reachable_states (ta_union A B) (ts ! i)" by simp
      ultimately show ?case using l' by auto
    qed (auto)
  qed
qed

lemma moves_union:
  fixes t :: "('f + 'q, 'v) term"
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
  shows "(t, state TYPE('v) q) \<in> (move (ta_union A B))\<^sup>* \<longleftrightarrow>
         (t, state TYPE('v) q) \<in> (move A)\<^sup>* \<union> (move B)\<^sup>*"
using reachable_states_union [OF assms] move_reachable_states by (metis Un_iff) 

lemma lang_ta_union:
  fixes A :: "('q,'f) ta"
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
  shows "(lang (ta_union A B) :: ('f, 'v) term set) = lang A \<union> lang B" (is "lang ?C = _")
proof (intro equalityI subsetI)
  fix t :: "('f, 'v) term"
  assume "t \<in> lang A \<union> lang B"
  then show "t \<in> lang (ta_union A B)" using lang_subseteq_lang_ta_union by fastforce+
next
  fix t :: "('f, 'v) term"
  assume "t \<in> lang ?C"
  then have g: "ground t" and i: "ta_final ?C \<inter> reachable_states ?C (fterm t) \<noteq> {}"
    by (auto simp: lang_def)
  { fix q
    assume "q \<in> ta_final ?C"
      and "q \<in> reachable_states ?C (fterm t)"
    then consider (AA) "q \<in> ta_final A" and "q \<in> reachable_states A (fterm t)"
                | (BA) "q \<in> ta_final B" and "q \<in> reachable_states A (fterm t)"
                | (AB) "q \<in> ta_final A" and "q \<in> reachable_states B (fterm t)"
                | (BB) "q \<in> ta_final B" and "q \<in> reachable_states B (fterm t)"
                using reachable_states_union [OF assms] by auto
    then have "t \<in> lang A \<union> lang B"
    proof (cases)
      case (BA)
      with reachable_states_in_states have "q \<in> ta_states A"
        by (metis (mono_tags) fterm_no_State subsetCE)
      then have *: "q \<in> ta_states A \<inter> ta_states B" using BA(1) by (simp add: ta_states_def)
      from BA(2) have "(fterm t, state TYPE('v) q) \<in> (move A)\<^sup>*"
        by (auto simp: move_reachable_states)
      then have "(fterm t, state TYPE('v) q) \<in> (move B)\<^sup>*" using * assms by auto
      then have "q \<in> reachable_states B (fterm t)" by (auto simp: move_reachable_states)
      then show ?thesis using BA by (auto simp: g lang_def)
    next
      case (AB)
      with reachable_states_in_states have "q \<in> ta_states B"
        by (metis (mono_tags) fterm_no_State subsetCE)
      then have *: "q \<in> ta_states A \<inter> ta_states B" using AB(1) by (simp add: ta_states_def)
      from AB(2) have "(fterm t, state TYPE('v) q) \<in> (move B)\<^sup>*"
        by (auto simp: move_reachable_states)
      then have "(fterm t, state TYPE('v) q) \<in> (move A)\<^sup>*" using * assms by auto
      then have "q \<in> reachable_states A (fterm t)" by (auto simp: move_reachable_states)
      then show ?thesis using AB by (auto simp: g lang_def)
    qed (auto simp: g lang_def)
  }
  then show "t \<in> lang A \<union> lang B" using i by blast
qed

lemma move_mono [mono_set]:
  assumes "B \<subseteq> C"
  shows "(move (D\<lparr> ta_rules := B \<rparr>))\<^sup>* \<subseteq> (move (D\<lparr> ta_rules := C \<rparr>))\<^sup>*"
using assms by (auto elim!: move.induct intro!: move.intros rtrancl_mono)

lemma move_mono':
  assumes "(s, t) \<in> move U"
    and "ta_rules U \<subseteq> ta_rules I"
    and "ta_eps U \<subseteq> ta_eps I"
  shows "(s, t) \<in> move I"
using assms
  by (induct rule: move.induct) (auto simp: move.trans move.eps subsetD dest: rtrancl_mono)

lemma move_mono'_rtrancl:
  assumes "(s, t) \<in> (move U)\<^sup>*"
    and "ta_rules U \<subseteq> ta_rules I"
    and "ta_eps U \<subseteq> ta_eps I"
  shows "(s, t) \<in> (move I)\<^sup>*"
using assms move_mono' [OF _ assms(2) assms(3)] by (induct) force+

lemma move_mono'_trancl:
  assumes "(s, t) \<in> (move U)\<^sup>+"
    and "ta_rules U \<subseteq> ta_rules I"
    and "ta_eps U \<subseteq> ta_eps I"
  shows "(s, t) \<in> (move I)\<^sup>+"
using assms move_mono'_rtrancl [OF _ assms(2) assms(3)] move_mono' [OF _ assms(2) assms(3)]
  rtrancl_into_trancl1 tranclD2 by metis

subsection \<open>Alternative move relation "move'"\<close>

inductive_set move' :: "('q, 'f) ta \<Rightarrow> ('f + 'q, 'v) term rel" for A
where
  trans: "TA_rule f qs q \<in> ta_rules A \<Longrightarrow> (fqterm f qs, State q) \<in> move' A"
| eps: "(q, q') \<in> (ta_eps A)\<^sup>* \<Longrightarrow> (State q, State q') \<in> move' A"
| Fun: "(s, t) \<in> move' A \<Longrightarrow> (Fun g (ss @ s # ts), Fun g (ss @ t # ts)) \<in> move' A"

lemma move'_intros:
  "TA_rule f qs q \<in> ta_rules A \<Longrightarrow> (C\<langle>fqterm f qs\<rangle>, C\<langle>State q\<rangle>) \<in> move' A"
  "(q, q') \<in> (ta_eps A)\<^sup>* \<Longrightarrow> (C\<langle>State q\<rangle>, C\<langle>State q'\<rangle>) \<in> move' A"
by (induct_tac[!] C) (auto intro: move'.intros)

lemma move_eq_move':
  shows "move A = move' A"
proof (intro equalityI subrelI)
  fix s t :: "('a + 'b, 'v) term"
  assume "(s, t) \<in> move A"
  then show "(s, t) \<in> move' A"
    by cases (auto simp: move'_intros)
next
  note * = move_ctxt[of _ _ _ "More f ss \<box> ts" for f ss ts, simplified]
           move.intros[where C = "\<box>", simplified]
  fix s t :: "('a + 'b, 'v) term"
  assume "(s, t) \<in> move' A"
  then show "(s, t) \<in> move A"
    by (induct) (auto intro: *)
qed

lemma no_move_to_nonempty_Inr:
  assumes "(fterm s, Fun (Inr q) (t # ts)) \<in> move A"
  shows "False"
using assms
apply (cases)
defer
using fterm_contains_no_Inr [of s]
apply metis
apply (case_tac C)
apply auto
apply (cases s)
apply auto
done

lemma fterm_args_fterm:
  assumes "fterm s = Fun (Inl f) ss"
  shows "\<exists>ss'. ss = map fterm ss'"
proof -
  from assms obtain f' ss' where "fterm (Fun f' ss') = Fun (Inl f) ss"
    by (metis term.simps(9) funs_term_list.elims term.distinct(1))
  then have "f' = f" and "ss = map fterm ss'" by auto
  then show ?thesis by blast
qed

lemma no_move_to_term_containing_nonempty_Inr:
  assumes "(fterm s, C\<langle>Fun (Inr q) (t # ts)\<rangle>) \<in> move A"
  shows "False"
using assms
proof (induct C arbitrary: s q t ts)
  case (Hole)
  then show ?case using no_move_to_nonempty_Inr by fastforce
next
  case (More f us E vs)
  then show ?case
  proof (cases f)
    case (Inr f')
    have "(fterm s, (More (Inr f') us E vs)\<langle>Fun (Inr q) (t # ts)\<rangle>) \<in> move A"
      using More(2) unfolding Inr .
    moreover have "(More (Inr f') us E vs)\<langle>Fun (Inr q) (t # ts)\<rangle> =
      Fun (Inr f') (us @ E\<langle>Fun (Inr q) (t # ts)\<rangle> # vs)" by auto
    moreover then obtain w ws where "w # ws = us @ E\<langle>Fun (Inr q) (t # ts)\<rangle> # vs"
      by (metis Nil_is_append_conv list.exhaust)
    ultimately have "(fterm s, Fun (Inr f') (w # ws)) \<in> move A" by simp
    from no_move_to_nonempty_Inr [OF this] show ?thesis .
  next
    case (Inl f')
    let ?q' = "Fun (Inr q) (t # ts)"
    let ?ws = "us @ E\<langle>?q'\<rangle> # vs"
    have "(fterm s, (More (Inl f') us E vs)\<langle>?q'\<rangle>) \<in> move A"
      using More(2) unfolding Inl .
    then have "(fterm s, Fun (Inl f') ?ws) \<in> move A" by simp
    from distr_move' [OF this] obtain ss where s: "fterm s = Fun (Inl f') ss" and
       len: "length ?ws = length ss" and
       *: "\<forall>i < length ss. ss ! i = ?ws ! i \<or> (ss ! i, ?ws ! i) \<in> move A" by blast
    obtain ss' where **: "ss = map fterm ss'" using fterm_args_fterm [OF s] by blast
    from * obtain j where
      "map fterm ss' ! j = E\<langle>?q'\<rangle> \<or> (map fterm ss' ! j, E\<langle>?q'\<rangle>) \<in> move A" (is "?s' = _ \<or> _")
      and len': "j < length (map fterm ss')"
      using ** len by (metis (no_types) add_Suc_right length_Cons length_append length_map
                       less_add_Suc1 nth_append_length)
    moreover
    { assume "(map fterm ss' ! j, E\<langle>?q'\<rangle>) \<in> move A"
      then have "(fterm (ss' ! j), E\<langle>?q'\<rangle>) \<in> move A" using len' by auto
      from More(1) [OF this] have ?thesis .
    }
    moreover
    { assume "map fterm ss' ! j = E\<langle>?q'\<rangle>"
      then have "fterm (ss' ! j) = E\<langle>?q'\<rangle>" using len' by auto
      then have ?thesis using fterm_contains_no_Inr by fast
    }
    ultimately show ?thesis by blast
  qed
qed

inductive_set wf_terms where
  Var: "(Var x) \<in> wf_terms"
| State: "(State q) \<in> wf_terms"
| Fun: "\<forall>t \<in> set ts. t \<in> wf_terms \<Longrightarrow> Fun (Inl f) ts \<in> wf_terms"

inductive_set wf_ctxts where
  Hole: "\<box> \<in> wf_ctxts"
| More: "\<forall>t \<in> set (us @ vs). t \<in> wf_terms \<Longrightarrow> E \<in> wf_ctxts \<Longrightarrow> More (Inl f) us E vs \<in> wf_ctxts"

lemma wf_terms_subtermeq:
  assumes "s \<in> wf_terms"
    and "s \<unrhd> t"
  shows "t \<in> wf_terms"
using assms
proof (induct s arbitrary: t)
  case (Var x)
  then have *: "t = Var x" by simp
  show ?case unfolding * by (simp add: wf_terms.intros)
next
  case (State q)
  then have *: "t = State q" using Fun_Nil_supt by fastforce
  show ?case unfolding * by (simp add: wf_terms.intros)
next
  case (Fun ts f)
  then show ?case by (metis subterm.le_less supt_Fun_imp_arg_supteq wf_terms.simps)
qed

lemma wf_terms_Fun_Inl_args:
  assumes "Fun (Inl f) ts \<in> wf_terms"
  shows "\<forall>t \<in> set ts. t \<in> wf_terms"
using assms by (cases) blast

lemma wf_terms_wf_ctxts:
  assumes "s \<in> wf_terms"
    and "s = C\<langle>t\<rangle>"
  shows "C \<in> wf_ctxts"
using assms
proof (induct C arbitrary: s)
  case (Hole)
  show ?case by (simp add: wf_ctxts.intros)
next
  case (More f us E vs)
  let ?ss = "us @ E\<langle>t\<rangle> # vs"
  have *: "s = Fun f ?ss" using More by simp
  obtain f' where **: "f = Inl f'" using More(2) unfolding * by (cases) blast+
  have "s = Fun (Inl f') ?ss" using * ** by auto
  then have "E\<langle>t\<rangle> \<in> wf_terms" using More.prems(1) wf_terms_Fun_Inl_args by force
  from More(1) [OF this] have E: "E \<in> wf_ctxts" by simp
  from More(2) have "\<forall>t \<in> set ?ss. t \<in> wf_terms" unfolding * ** using wf_terms_Fun_Inl_args by fast
  then have "\<forall>t \<in> set (us @ vs). t \<in> wf_terms" by force
  then show ?case using E unfolding ** by (simp add: E wf_ctxts.More)
qed

lemma wf_ctxts_wf_terms_wf_terms:
  assumes "C \<in> wf_ctxts"
    and "s \<in> wf_terms"
  shows "C\<langle>s\<rangle> \<in> wf_terms"
using assms
proof (induct C)
  case (Hole)
  then show ?case by simp
next
  case (More us vs E f)
  let ?ss = "us @ E\<langle>s\<rangle> # vs"
  have "E\<langle>s\<rangle> \<in> wf_terms" using More(3) [OF More(4)] .
  with More(1) have "\<forall>t \<in> set ?ss. t \<in> wf_terms" by auto
  then show ?case by (simp add: wf_terms.Fun)
qed

lemma move_preserves_wf_terms:
  assumes "(s, t) \<in> move A"
    and "s \<in> wf_terms"
  shows "t \<in> wf_terms"
using assms
proof (cases)
  case (trans f qs q C)
  have "C \<in> wf_ctxts" using wf_terms_wf_ctxts [OF assms(2) trans(1)] .
  moreover have "State q \<in> wf_terms" by (simp add: wf_terms.State)
  ultimately show ?thesis using trans(2) wf_ctxts_wf_terms_wf_terms by blast
next
  case (eps q q' C)
  have "C \<in> wf_ctxts" using wf_terms_wf_ctxts [OF assms(2) eps(1)] .
  moreover have "State q' \<in> wf_terms" by (simp add: wf_terms.State)
  ultimately show ?thesis using eps(2) wf_ctxts_wf_terms_wf_terms by blast
qed

lemma moves_preserve_wf_terms:
  assumes "(s, t) \<in> (move A)\<^sup>*"
    and "s \<in> wf_terms"
  shows "t \<in> wf_terms"
using assms move_preserves_wf_terms by (induct) auto

lemma fterm_in_wf_terms:
  "fterm s \<in> wf_terms"
by (induct s) (auto simp: wf_terms.intros)

lemma fqterm_in_wf_terms:
  "fqterm f qs \<in> wf_terms"
by (simp add: wf_terms.intros)

lemma non_empty_Inr_not_in_wf_terms:
  "Fun (Inr q) (t # ts) \<notin> wf_terms"
by (auto, cases rule: wf_terms.cases) (auto)

lemma wf_term_no_moves_to_non_empty_Inr:
  assumes "(s, Fun (Inr q) (t # ts)) \<in> (move A)\<^sup>*" (is "(_, ?t) \<in> ?A")
    and "s \<in> wf_terms"
  shows "False"
using assms
proof (induct s ?t rule: rtrancl.induct [case_names base step])
  case (base)
  then show ?case using non_empty_Inr_not_in_wf_terms by fast
next
  case (step s u)
  have "u \<in> wf_terms" using moves_preserve_wf_terms [OF step(1) step(4)] .
  moreover have "?t \<notin> wf_terms" using non_empty_Inr_not_in_wf_terms .
  ultimately show ?case using step(3) move_preserves_wf_terms by blast
qed

lemma ftrem_no_moves_to_non_empty_Inr:
  assumes "(fterm s, Fun (Inr g) (t # ts)) \<in> (move A)\<^sup>*" (is "(?s, ?t) \<in> ?A")
  shows "False"
proof -
  have "?s \<in> wf_terms" by (simp add: fterm_in_wf_terms)
  from moves_preserve_wf_terms [OF assms this] have "?t \<in> wf_terms" .
  then show ?thesis using non_empty_Inr_not_in_wf_terms by fast
qed

inductive_set move_comp :: "('q, 'f) ta \<Rightarrow> _" for A
where
  Hole [simp]: "(\<box>, \<box>) \<in> move_comp A"
| More: "f = g \<Longrightarrow> (C, D) \<in> move_comp A \<Longrightarrow> length ss\<^sub>1 = length ts\<^sub>1 \<Longrightarrow> length ss\<^sub>2 = length ts\<^sub>2 \<Longrightarrow>
    \<forall>i < length (ts\<^sub>1). (ss\<^sub>1 ! i, ts\<^sub>1 ! i) \<in> (move A)\<^sup>* \<Longrightarrow>
    \<forall>i < length (ts\<^sub>2). (ss\<^sub>2 ! i, ts\<^sub>2 ! i) \<in> (move A)\<^sup>* \<Longrightarrow>
    (More f ss\<^sub>1 C ss\<^sub>2, More g ts\<^sub>1 D ts\<^sub>2) \<in> move_comp A"

lemma move_comp_imp_moves:
  assumes "(C, D) \<in> move_comp A"
  shows "(C\<langle>t\<rangle>, D\<langle>t\<rangle>) \<in> (move A)\<^sup>*"
using assms
apply (induct)
apply (auto simp: nth_append intro!: args_steps_imp_steps [OF ctxt_closed_move])
apply (case_tac "length ts\<^sub>1 = i"; simp)
done

lemma distr_moves'':
  assumes "(s, C\<langle>Fun (Inl f) ts\<rangle>) \<in> (move A)\<^sup>*"
    and "s \<in> wf_terms"
  shows "\<exists>D ss. s = D\<langle>Fun (Inl f) ss\<rangle> \<and> length ts = length ss \<and>
         (\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*) \<and>
         (D\<langle>Fun (Inl f) ts\<rangle>, C\<langle>Fun (Inl f) ts\<rangle>) \<in> (move A)\<^sup>* \<and>
         (D, C) \<in> move_comp A"
using assms
proof (induct C arbitrary: s)
  case (Hole)
  then have *: "(s, Fun (Inl f) ts) \<in> (move A)\<^sup>*" by simp
  from distr_moves [OF this] obtain ss where "s = Fun (Inl f) ss" and
    "length ts = length ss" and
    "\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*"
    by blast
  then show ?case by (intro exI [where x = \<box>]; simp)
next
  case (More g us E vs)
  let ?t = "Fun (Inl f) ts"
  let ?ts = "us @ E\<langle>?t\<rangle> # vs"
  let ?C = "More g us E vs"
  have *: "?C\<langle>?t\<rangle> = Fun g ?ts" by simp
  show ?case
  proof (cases g)
    case (Inl g')
    have "(s, Fun (Inl g') ?ts) \<in> (move A)\<^sup>*" using More(2) [unfolded *, unfolded Inl] .
    from distr_moves [OF this] obtain ss' where s: "s = Fun (Inl g') ss'" and
       len: "length ?ts = length ss'" and
       ss': "\<forall>i < length ss'. (ss' ! i, ?ts ! i) \<in> (move A)\<^sup>*"
       by blast
    moreover define j where "j = length us"
    ultimately have 1: "j < length ss'" and 2: "(ss' ! j, E\<langle>?t\<rangle>) \<in> (move A)\<^sup>*"
      and 3: "?ts ! j = E\<langle>?t\<rangle>" apply auto
      by (metis less_add_Suc1 nth_append_length)
    from wf_terms_Fun_Inl_args [OF More(3) [unfolded s]] 
      have "ss' ! j \<in> wf_terms" using 1 by auto
    from More(1) [OF 2 this] obtain D' ss where j: "ss' ! j = D'\<langle>Fun (Inl f) ss\<rangle>" and
      len': "length ts = length ss" and
      ss: "\<forall>i < length ss. (ss ! i, ts ! i) \<in> (move A)\<^sup>*" and
      4: "(D'\<langle>?t\<rangle>, E\<langle>?t\<rangle>) \<in> (move A)\<^sup>*" and
      mc: "(D', E) \<in> move_comp A" by blast
    let ?ss'' = "take j ss' @ D'\<langle>Fun (Inl f) ts\<rangle> # drop (Suc j) ss'"
    have "s = Fun (Inl g') (take j ss' @ D'\<langle>Fun (Inl f) ss\<rangle> # drop (Suc j) ss')"
      using s j 1 id_take_nth_drop by fastforce
    then have 5: "ss' = take j ss' @ D'\<langle>Fun (Inl f) ss\<rangle> # drop (Suc j) ss'"
      (is "_ = ?ss'") using s by simp
    then have 6: "s = (More (Inl g') (take j ss') D' (drop (Suc j) ss'))\<langle>Fun (Inl f) ss\<rangle>"
      (is "_ = ?D\<langle>_\<rangle>") using s by fastforce
    have 8: "\<forall>i < length us. (ss' ! i, us ! i) \<in> (move A)\<^sup>*" using 1 ss'
      by (metis (no_types, lifting) Suc_less_eq append_Cons_nth_left j_def less_SucI less_trans_Suc)
    have 9: "\<forall>i < length vs. (ss' ! Suc (length us + i), vs ! i) \<in> (move A)\<^sup>*"
      using 1 len ss'
      by (auto)
         (metis (no_types) add.commute add_Suc_right nat_add_left_cancel_less nth_Cons_Suc
          nth_append_length_plus)
    from ss' have "\<forall>i < length ?ss'. (?ss' ! i, ?ts ! i) \<in> (move A)\<^sup>*" using 5 by presburger
    then have 7: "\<forall>i < length ?ss''. (?ss' ! i, ?ts ! i) \<in> (move A)\<^sup>*" by auto
    { fix i
      assume a: "i < length ?ss''"
      then have "(?ss'' ! i, ?ts ! i) \<in> (move A)\<^sup>*"
      proof (cases "i = j")
        case (False)
        then show ?thesis using a 1 5 7
          by (metis (no_types, lifting) length_Cons length_append less_imp_le_nat
              nth_append_take_drop_is_nth_conv)
      next
        case (True)
        then have *: "?ss'' ! i = D'\<langle>?t\<rangle>" by (simp add: 1 less_imp_le_nat nth_append_take)
        from True have "?ts ! i = E\<langle>?t\<rangle>" using 3 by simp
        then show ?thesis unfolding * using 4 by simp
      qed
    }
    then have "\<forall>i < length ?ss''. (?ss'' ! i, ?ts ! i) \<in> (move A)\<^sup>*" by blast
    from args_steps_imp_steps [OF ctxt_closed_move _ this, of "Inl g'"]
      have "(Fun (Inl g') ?ss'', Fun (Inl g') ?ts) \<in> (move A)\<^sup>*" using Inl More.prems(1) s
      by (metis 5 len length_Cons length_append)
    then have "(?D\<langle>?t\<rangle>, ?C\<langle>?t\<rangle>) \<in> (move A)\<^sup>*" unfolding Inl by fastforce
    moreover have "(?D, ?C) \<in> move_comp A" using mc len 8 9
      by (intro move_comp.More) (auto simp: Inl j_def)
    ultimately show ?thesis using 6 len' ss unfolding Inl by blast
  next
    case (Inr q)
    have "(s, Fun (Inr q) ?ts) \<in> (move A)\<^sup>*" using More(2) unfolding * using Inr by blast
    then obtain w ws where "(s, Fun (Inr q) (w # ws)) \<in> (move A)\<^sup>*"
      by (metis Nil_is_append_conv list.exhaust) 
    from wf_term_no_moves_to_non_empty_Inr [OF this More(3)] have "False" .
    then show ?thesis ..
  qed
qed

lemma map_states_term_State [simp]:
  shows "map_states_term g \<circ> State = State \<circ> g"
by (rule ext) (simp)

lemma inj_map_states_term [intro, simp]:
  assumes "inj g"
  shows "inj (map_states_term g)"
proof (rule injI)
  fix s t :: "('e + 'a, 'f) term"
  assume "map_states_term g s = map_states_term g t"
  then show "s = t"
  using assms
  apply (induct g s arbitrary: t rule: map_states_term.induct)
  apply (auto elim!: map_states_term.elims simp: inj_on_def) by (metis list.inj_map_strong)+
qed

lemma map_append_Cons_exists:
  assumes "xs @ y # ys = map f zs"
    and "inj f"
  shows "\<exists>xs' y' ys'. xs = map f xs' \<and> y = f y' \<and> ys = map f ys' \<and> zs = xs' @ y' # ys'"
proof -
  { fix xs' y' ys'
    assume 1: "xs' = map (inv f) xs" and 2: "ys' = map (inv f) ys" and 3: "y' = inv f y"
    moreover
    then have 4: "length xs' = length xs" and 5: "length ys' = length ys" by auto
    ultimately
    have "xs @ y # ys = (map f xs') @ (f y') # (map f ys')"
      using assms
      by (auto) (metis (no_types, lifting) list.simps(9) map_append map_map o_inv_o_cancel)
    then have "xs = map f xs' \<and> y = f y' \<and> ys = map f ys' \<and> zs = xs' @ y' # ys'"
      using assms 1 2 3 4 5
      by (metis append_eq_conv_conj inj_map_eq_map list.sel(1) list.sel(3) list.simps(9)
          map_append take_map)
  }
  from this[of "map (inv f) xs" "map (inv f) ys" "inv f y"] show ?thesis by blast
qed

lemma disj_move_union_iff:
  assumes "ta_states A \<inter> ta_states B = {}"
  shows "move (ta_union A B) = (move A) \<union> (move B)"
  (is "?L = ?R1 \<union> ?R2")
proof (intro equalityI subrelI)
  fix s t
  assume "(s, t) \<in> ?L"
  then show "(s, t) \<in> ?R1 \<union> ?R2"
  proof (induct)
    case (eps q q' C)
    with assms have "(q, q') \<in> (ta_eps A)\<^sup>* \<union> (ta_eps B)\<^sup>*"
      by (auto simp: rtrancl_eq_or_trancl) (drule disj_ta_states_imp_disj_ta_eps, blast+)
    then show ?case by (auto simp: move.eps)
  qed (auto simp: move.trans)
next
  fix s t
  assume "(s, t) \<in> ?R1 \<union> ?R2"
  then have "(s, t) \<in> ?R1 \<or> (s, t) \<in> ?R2" by simp
  then show "(s, t) \<in> ?L"
  by (auto simp: move.trans elim!: move.cases) (simp add: in_rtrancl_UnI move.eps)+
qed

lemma ta_union_ta_big_union_iff:
  "ta_union A B = ta_big_union {A, B}"
by (auto simp: ta_union_def ta_big_union_def)

lemma empty_ta_eps_move_ta_big_union_iff:
  assumes "\<forall>a \<in> A. ta_eps a = {}" and "A \<noteq> {}"
  shows "move (ta_big_union A) = \<Union>(move ` A)" (is "?A = ?B")
proof (intro equalityI subrelI)
  fix s t
  assume "(s, t) \<in> ?A"
  then show "(s, t) \<in> ?B"
  proof (induct)
    case (eps q q' C)
    then have q: "q' = q" using assms by (auto simp: ta_big_union_def)
    have "(q, q) \<in> (\<Union>(ta_eps ` A))\<^sup>*" by blast
    then obtain a where 1: "a \<in> A" and 2: "(q, q) \<in> (ta_eps a)\<^sup>*" using assms by auto
    have "(C\<langle>State q\<rangle>, C\<langle>State q'\<rangle>) \<in> move a" using 2 by (simp add: move.eps q) 
    then show ?case using 1 by auto
  next
    case (trans f qs q C)
    then obtain a where 1: "a \<in> A" and 2: "TA_rule f qs q \<in> ta_rules a"
      using assms by (auto simp: ta_big_union_def)
    then have "(C\<langle>fqterm f qs\<rangle>, C\<langle>State q\<rangle>) \<in> move a" by (simp add: move.trans)
    then show ?case using 1 by auto
  qed
next
  fix s t
  assume "(s, t) \<in> ?B"
  then obtain a where 1: "a \<in> A" and 2: "(s, t) \<in> move a" using assms by auto
  show "(s, t) \<in> ?A" using 2
  proof (cases rule: move.cases)
    case (trans f qs q C)
    then have "TA_rule f qs q \<in> ta_rules (ta_big_union A)" using 1 by (auto simp: ta_big_union_def)
    then show ?thesis using trans(1,2) by (simp add: move.trans)
  next
    case (eps q q' C)
    then have "(q, q') \<in> (ta_eps (ta_big_union A))\<^sup>*" using 1 assms by (auto simp: ta_big_union_def)
    then show ?thesis using eps(1,2) by (simp add: move.eps)
  qed
qed

lemma empty_ta_eps_move_union_iff:
  assumes "ta_eps A = {}"
  shows "move (ta_union A B) = (move A) \<union> (move B)"
  (is "?L = ?R1 \<union> ?R2")
proof (intro equalityI subrelI)
  fix s t
  assume "(s, t) \<in> ?L"
  then show "(s, t) \<in> ?R1 \<union> ?R2"
  proof (induct)
    case (eps q q' C)
    with assms have "(q, q') \<in> (ta_eps B)\<^sup>*" by (auto)
    then show ?case by (auto simp: move.eps)
  qed (auto simp: move.trans)
next
  fix s t
  assume "(s, t) \<in> ?R1 \<union> ?R2"
  then have "(s, t) \<in> ?R1 \<or> (s, t) \<in> ?R2" by simp
  then show "(s, t) \<in> ?L"
  by (auto simp: move.trans elim!: move.cases) (simp add: in_rtrancl_UnI move.eps)+
qed

lemma empty_ta_eps_move_union_iff':
  assumes "ta_eps B = {}"
  shows "move (ta_union A B) = (move A) \<union> (move B)"
using empty_ta_eps_move_union_iff [OF assms] by auto

lemma funs_term_ctxt_apply [simp]:
  "funs_term (C\<langle>t\<rangle>) = funs_ctxt C \<union> funs_term t"
proof (induct t)
  case (Var x) show ?case by (induct C) auto
next
  case (Fun f ts) show ?case by (induct C arbitrary: f ts) auto
qed

lemma move_preserves_signature:
  assumes "funs_term s \<subseteq> Inl ` F \<union> Inr ` ta_states A" (is "_ \<subseteq> ?S")
    and "(s, t) \<in> move A"
  shows "funs_term t \<subseteq> ?S"
using assms(2)
proof (cases rule: move.cases)
  case (trans f qs q C)
  show ?thesis using trans(1,2) assms(1) r_states_in_states[OF trans(3)] by simp
next
  case (eps q q' C)
  show ?thesis
  proof (cases "q = q'")
    case (True)
    then show ?thesis using assms(1) and eps(1,2) by fast
  next
    case (False)
    show ?thesis using eps and assms(1) and trancl_ta_epsD[of q q' A]
      and rtrancl_eq_or_trancl[of q q' "ta_eps A"] by auto
  qed
qed

lemma move_rtrancl_preserves_signature:
  assumes "funs_term s \<subseteq> Inl ` F \<union> Inr ` ta_states A" (is "_ \<subseteq> ?S")
    and "(s, t) \<in> (move A)\<^sup>*"
  shows "funs_term t \<subseteq> ?S"
using assms(2,1) by (induct) (auto simp: move_preserves_signature)

lemma disj_move_imp_ta_union_move:
  assumes "ta_states A \<inter> ta_states B = {}"
    and "(s, t) \<in> move A"
  shows "(s, t) \<in> move (ta_union A B)"
using assms disj_move_union_iff by blast

lemma disj_move_rtrancl_imp_ta_union_move_rtrancl:
  assumes "ta_states A \<inter> ta_states B = {}"
    and "(s, t) \<in> (move A)\<^sup>*"
  shows "(s, t) \<in> (move (ta_union A B))\<^sup>*"
using assms(2) disj_move_union_iff assms(1)
by (induct, auto)
   (simp add: disj_move_union_iff in_rtrancl_UnI rtrancl.rtrancl_into_rtrancl)

lemma disj_move_trancl_imp_ta_union_move_trancl:
  assumes "ta_states A \<inter> ta_states B = {}"
    and "(s, t) \<in> (move A)\<^sup>+"
  shows "(s, t) \<in> (move (ta_union A B))\<^sup>+"
using assms by (meson disj_move_imp_ta_union_move subrelI trancl_mono)

lemma disj_reachable_states_ta_union_reachable_states:
  assumes "q \<in> reachable_states A t"
    and "ta_states A \<inter> ta_states B = {}"
  shows "q \<in> reachable_states (ta_union A B) t"
proof -
  have "(t, State q) \<in> (move A)\<^sup>*" using move_reachable_states [THEN iffD2, OF assms(1)] .
  from disj_move_rtrancl_imp_ta_union_move_rtrancl [OF assms(2) this]
    have "(t, State q) \<in> (move (ta_union A B))\<^sup>*" .
  from move_reachable_states [THEN iffD1, OF this]
    show "q \<in> reachable_states (ta_union A B) t" .
qed

lemma langE [elim]:
  assumes "t \<in> lang A"
  obtains q\<^sub>f where "(fterm t, State q\<^sub>f) \<in> (move A)\<^sup>*" and "q\<^sub>f \<in> ta_final A"
using assms move_reachable_states[symmetric] unfolding lang_def by fast

lemma fterm_subst_distrib [simp]:
  "fterm (t \<cdot> \<sigma>) = fterm t \<cdot> (fterm \<circ> \<sigma>)"
by (induct t) auto

lemma moves_state_subst:
  fixes \<sigma> :: "('f + 'q, 'v) subst"
  assumes "(s \<cdot> \<sigma>, State q) \<in> (move A)\<^sup>*" (is "_ \<in> ?move") and "q \<in> ta_states A" and "linear_term s"
  shows "\<exists>\<theta>. (\<forall>x \<in> vars_term s. (\<sigma> x, (State \<circ> \<theta>) x) \<in> (move A)\<^sup>*) \<and>
             (s \<cdot> (State \<circ> \<theta>), State q :: ('f + 'q, 'v) term) \<in> (move A)\<^sup>* \<and> 
             range \<theta> \<subseteq> ta_states A"
using assms
proof (induct s arbitrary: q)
  case (Var x)
  { fix \<theta> :: "'v \<Rightarrow> 'q"
    assume \<theta>: "\<theta> = (\<lambda>y. q)"
    let ?\<theta> = "\<lambda>x. State (\<theta> x)"
    have "(Var x \<cdot> \<sigma>, Var x \<cdot> ?\<theta>) \<in> ?move" using Var \<theta> by simp
    moreover have "(Var x \<cdot> ?\<theta>, State q) \<in> ?move" using \<theta> by simp
    moreover have "range \<theta> \<subseteq> ta_states A" using Var \<theta> by blast 
    ultimately
    have "(Var x \<cdot> \<sigma>, Var x \<cdot> ?\<theta>) \<in> ?move \<and> (Var x \<cdot> ?\<theta>, State q) \<in> ?move \<and>
          range \<theta> \<subseteq> ta_states A" by simp
  }
  then show ?case by force
next
  case (Fun f ss)
  let ?ss = "map (\<lambda>s. s \<cdot> \<sigma>) ss"
  show ?case
  proof (cases "\<exists>f'. f = Inl f'")
    case (True) (* f is a function symbol *)
    then obtain f' where f': "f = Inl f'" by auto
    have "q \<in> reachable_states A (Fun (Inl f') ?ss)"
      using move_reachable_states [THEN iffD1, OF Fun(2)] unfolding f' by simp
    then obtain qs q' where
      trans: "TA_rule f' qs q' \<in> ta_rules A" and
      eps: "(q',q) \<in> (ta_eps A)\<^sup>*" and
      len: "length qs = length ?ss" and
      qs: "\<forall> i < length ?ss. qs ! i \<in> reachable_states A (?ss ! i)"
      by auto
    have len': "length qs = length ss" using len by simp
    { fix i
      let ?s\<^sub>i = "ss ! i"
      let ?q\<^sub>i = "qs ! i"
      let ?subst = "\<lambda>\<theta>. State \<circ> \<theta>"
      assume l: "i < length ss"
      have "?s\<^sub>i \<in> set ss" using l by simp
      moreover have "(?s\<^sub>i \<cdot> \<sigma>, State ?q\<^sub>i) \<in> ?move" using move_reachable_states qs l by force
      moreover have "?q\<^sub>i \<in> ta_states A" using l len' using r_states_in_states[OF trans] by fastforce
      moreover have "linear_term ?s\<^sub>i" using Fun(4) \<open>?s\<^sub>i \<in> set ss\<close>  by simp
      ultimately have "\<exists>\<theta>. (\<forall> x \<in> vars_term ?s\<^sub>i. (\<sigma> x, (?subst \<theta>) x) \<in> ?move) \<and>
        (?s\<^sub>i \<cdot> (?subst \<theta>), State ?q\<^sub>i) \<in> ?move \<and>
        range \<theta> \<subseteq> ta_states A"
        by (rule Fun(1))
    }
    then obtain \<theta> where **: "\<forall>i < length ss. (\<forall>x \<in> vars_term (ss ! i).
                (\<sigma> x, (State \<circ> (\<theta> i)) x) \<in> ?move) \<and>
               (ss ! i \<cdot> (State \<circ> (\<theta> i)), State (qs ! i)) \<in> ?move \<and>
               range (\<theta> i) \<subseteq> ta_states A" by metis
    have "is_partition (map vars_term ss)" using Fun(4) by simp
    from subst_merge [OF this, of \<theta>]
      obtain \<theta>' where \<theta>': "\<forall>i < length ss. \<forall>x \<in> vars_term (ss ! i). \<theta>' x = \<theta> i x" by blast
    moreover define \<theta>'' where "\<theta>'' = (\<lambda>x. (if x \<in> vars_term (Fun f ss) then \<theta>' x else q))"
    ultimately have *: "\<forall>i < length ss. \<forall>x \<in> vars_term (ss ! i). State (\<theta>'' x) = State (\<theta> i x)"
      by (auto)
    { fix i :: nat
      assume l: "i < length ss"
      from * [THEN spec, THEN mp, of i, OF this]
      have "\<And>x. x \<in> vars_term (ss ! i) \<Longrightarrow> (State (\<theta>'' x) :: ('f + 'q, 'v) term) = State (\<theta> i x)" by simp
      from term_subst_eq [OF this, of "ss ! i" id, simplified]
        have "(\<forall> x \<in> vars_term (ss ! i). (\<sigma> x, (State \<circ> \<theta>'') x) \<in> ?move) \<and>
               (ss ! i \<cdot> (State \<circ> \<theta>''), State (qs ! i)) \<in> ?move"
        using ** * l by (auto simp: o_def)
    }
    then have "\<forall>i < length ss. (\<forall>x \<in> vars_term (ss ! i). (\<sigma> x, (State \<circ> \<theta>'') x) \<in> ?move) \<and>
               (ss ! i \<cdot> (State \<circ> \<theta>''), State (qs ! i)) \<in> ?move" by (auto simp: o_def)
    then have "(\<forall>x \<in> vars_term (Fun f ss). (\<sigma> x, (State \<circ> \<theta>'') x) \<in> ?move)" and
              "(Fun f ss \<cdot> (State \<circ> \<theta>''), Fun f (map State qs)) \<in> ?move"
      using len by (auto intro: args_steps_imp_steps [OF ctxt_closed_move] simp: in_set_conv_nth)
    moreover have "range \<theta>'' \<subseteq> ta_states A" using ** Fun(3) \<theta>'
      by (auto simp: \<theta>''_def in_set_conv_nth) (blast)
    moreover have "(Fun f (map State qs), State q) \<in> ?move"
      using move.trans [OF trans, of \<box>] and move.eps [OF eps, of \<box>]
      by (auto simp: f' dest: r_into_rtrancl rtrancl_trans)
    ultimately show ?thesis by (force simp: o_def)
  next
    case (False) (* f is a state symbol *)
    then obtain f' where f': "f = Inr f'" using sum.exhaust_sel by blast
    have *: "q \<in> reachable_states A (Fun (Inr f') ss \<cdot> \<sigma>)"
      using move_reachable_states [THEN iffD1, OF Fun(2)] unfolding f' .
    show ?thesis
    proof (cases "ss = Nil")
      case (False)
      then obtain x xs where "ss = x # xs" by (metis list.exhaust)
      then have "reachable_states A (Fun (Inr f') ss \<cdot> \<sigma>) = {}"
      using * reachable_states.simps(4) by auto
      then show ?thesis using * by simp
    next
      define \<theta> where "\<theta> = ((\<lambda>x. q) :: 'v \<Rightarrow> 'q)"
      case True
      then show ?thesis  using Fun(2,3) by (auto simp: \<theta>_def f')
    qed
  qed
qed

lemma moves_State:
  assumes "(C\<langle>t\<rangle>, State q) \<in> (move A)\<^sup>*" (is "(_, ?q) \<in> ?move")
  shows "\<exists>q'. (t, (State q') :: ('f + 'q, 'v) term) \<in> (move A)\<^sup>* \<and>
              (C\<langle>State q'\<rangle>, State q) \<in> (move A)\<^sup>*"
using assms
proof (induct C arbitrary: q)
  case (More f ss D ts)
  let ?ss = "ss @ D\<langle>t\<rangle> # ts"
  show ?case
  proof (cases "\<exists> f'. f = Inl f'")
    case (True) (* f is a function symbol *)
    then obtain f' where f': "f = Inl f'" by auto
    have "q \<in> reachable_states A (More f ss D ts)\<langle>t\<rangle>"
      using move_reachable_states [THEN iffD1, OF More(2)] .
    then obtain qs q\<^sub>1 where
      trans: "TA_rule f' qs q\<^sub>1 \<in> ta_rules A" and
      eps: "(q\<^sub>1, q) \<in> (ta_eps A)\<^sup>*" and
      len: "length qs = length ?ss" and
      qs: "\<forall> i < length ?ss. qs ! i \<in> reachable_states A (?ss ! i)"
      unfolding f' by auto
    have qs': "\<forall> i < length ?ss. (?ss ! i, State (qs ! i)) \<in> ?move"
      using qs move_reachable_states by metis
    then obtain k where 1: "(D\<langle>t\<rangle>, State (qs ! k)) \<in> ?move" and k: "k = length ss"
      by (metis (no_types, lifting) add_Suc_right len length_Cons length_append less_add_Suc1
          nth_append_length)
    let ?q\<^sub>x = "qs ! k"
    obtain q'' where *: "(t, State q'') \<in> ?move" and **: "(D\<langle>State q''\<rangle>, State ?q\<^sub>x) \<in> ?move"
      using 1 More(1) by blast
    have 2: "(Fun f (map State qs), State q\<^sub>1) \<in> ?move" using move.trans [OF trans, of \<box>]
      unfolding f' by auto
    have 3: "(State q\<^sub>1, State q) \<in> ?move" using move.eps [OF eps, of \<box>] by auto
    let ?ss' = "ss @ D\<langle>State q''\<rangle> # ts"
    have len': "length ?ss' = length (map State qs)" using len by simp
    have "(Fun f ?ss', Fun f (map State qs)) \<in> ?move"
    proof (intro args_steps_imp_steps [OF ctxt_closed_move len'] allI impI)
      fix i
      assume l: "i < length ?ss'"
      have "(?ss' ! i, State (qs ! i)) \<in> ?move"
      proof (cases "i = k")
        case (True)
        then show ?thesis using k len' ** by simp
      next
        case (False)
        show ?thesis
        proof (cases "i < k")
          case (True)
          then have "i < length ss" using k by simp
          then show ?thesis
            using k True qs' [THEN spec, of i] by (simp add: nth_append)
        next
          note False' = False
          moreover case (False)
          ultimately show ?thesis
            using k qs' [THEN spec, of i]
            by (metis append_Cons_nth_not_middle l len len' length_map)
        qed
      qed
      then show "(?ss' ! i, (map State qs ! i)) \<in> ?move" using l len' by simp
    qed
    then have "((More f ss D ts)\<langle>State q''\<rangle>, State q) \<in> ?move" using 2 3 by auto
    with * show ?thesis by blast
  next
    case (False) (* f is a state *)
    then obtain f' where f': "f = Inr f'" using sum.exhaust_sel by blast
    have "q \<in> reachable_states A (More (Inr f') ss D ts)\<langle>t\<rangle>"
      using move_reachable_states [THEN iffD1, OF More(2)] unfolding f' .
    moreover have "(More (Inr f') ss D ts)\<langle>t\<rangle> = Fun (Inr f') (ss @ D\<langle>t\<rangle> # ts)" by auto
    ultimately have 1: "q \<in> reachable_states A (Fun (Inr f') (ss @ D\<langle>t\<rangle> # ts))" by simp
    thm Nil_is_append_conv
    obtain x xs where "x # xs = ss @ D\<langle>t\<rangle> # ts" by (metis Nil_is_append_conv list.exhaust) 
    then have "reachable_states A (Fun (Inr f') (ss @ D\<langle>t\<rangle> # ts)) = {}"
      using reachable_states.simps(4) by metis
    with 1 have "False" by simp
    then show ?thesis ..
  qed
qed (auto)

lemma non_empty_ta_rules_ta_union:
  assumes "ta_rules A \<noteq> {}"
  shows "ta_rules (ta_union A B) \<noteq> {}"
using assms by (auto)

lemma ta_states_ta_union_iff [simp]:
  "ta_states (ta_union A B) = ta_states A \<union> ta_states B"
unfolding ta_states_def by auto

lemma accessible_disj_ta_states_ta_union:
  assumes "accessible TYPE('v) A q"
    and "ta_states A \<inter> ta_states B = {}"
  shows "accessible TYPE('v) (ta_union A B) q"
proof -
  obtain t :: "('b, 'v) term" where 1: "ground (fterm t)"
    and 2: "q \<in> reachable_states A (fterm t)"
    using accessibleE [OF assms(1)] by blast
  from disj_reachable_states_ta_union_reachable_states [OF 2 assms(2)] have
    "q \<in> reachable_states (ta_union A B) (fterm t)" .
  with 1 show ?thesis unfolding accessible_def by auto
qed

lemma accessible_ta_union:
  assumes "accessible TYPE('v) A q"
    and "\<forall>q \<in> ta_states A \<inter> ta_states B. sterms TYPE('v) A q = sterms TYPE('v) B q"
  shows "accessible TYPE('v) (ta_union A B) q"
proof -
  obtain t :: "('b, 'v) term" where 1: "ground (fterm t)"
    and 2: "q \<in> reachable_states A (fterm t)"
    using accessibleE [OF assms(1)] by blast
  from 2 have "q \<in> ta_states A" using reachable_states_in_states fterm_no_State by fast
  then consider (A) "q \<in> ta_states A - ta_states B" | (I) "q \<in> ta_states A \<inter> ta_states B" by blast
  then show ?thesis
  proof (cases)
    case (A)
    then show ?thesis using 1 2
      apply (auto simp: accessible_def) using assms(2) reachable_states_union by force
  next
    case (I)
    from 2 have "q \<in> reachable_states A (fterm t) \<union> reachable_states B (fterm t)" by auto
    with assms I reachable_states_union have "q \<in> reachable_states (ta_union A B) (fterm t)"
      by blast
    then show ?thesis using 1 by (auto simp: accessible_def)
  qed
qed

lemma accessible_ground_move_rtrancl:
  assumes "accessible TYPE('v) A q"
  shows "\<exists>t :: ('b, 'v) term. ground (fterm t) \<and> (fterm t, State q) \<in> (move A)\<^sup>*"
using assms unfolding accessible_def move_reachable_states by simp

lemma vars_move_imp_move:
  assumes "\<forall>x \<in> vars_term t. (\<sigma> x, \<theta> x) \<in> (move A)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<theta>) \<in> (move A)\<^sup>*"
using assms by (induct t) (auto simp add: args_steps_imp_steps ctxt_closed_move)

definition "sr R = {u | u l r. u \<unlhd> l \<and> (l, r) \<in> R}"

lemma subterm_in_sr:
  assumes "t \<unrhd> s" and "t \<in> sr R"
  shows "s \<in> sr R"
using subterm.order.trans[OF assms(1)] assms(2) unfolding sr_def by blast

lemma subterm_funas_term_subset:
  assumes "s \<lhd> t" and "funas_term t \<subseteq> F" shows "funas_term s \<subseteq> F"
using assms by (induct) auto

lemma Fun_in_sr_imp_F:
  assumes "Fun f ts \<in> sr R" and "funas_trs R \<subseteq> F"
  shows "(f, length ts) \<in> F"
using assms by (force simp: sr_def funas_defs dest: subterm_funas_term_subset)

lemma funas_term_sr:
  assumes "t \<in> sr R" and "funas_trs R \<subseteq> F"
  shows "funas_term t \<subseteq> F"
using assms by (force simp: sr_def funas_defs)

lemma subterm_linear:
  assumes "s \<unrhd> t" and "linear_term s"
  shows "linear_term t"
using assms by (induct) auto

lemma sr_linear:
  assumes "t \<in> sr R" and "\<forall> (l, r) \<in> R. linear_term l"
  shows "linear_term t"
using assms
unfolding sr_def
by (auto split: prod.splits dest: subterm_linear)

lemma Fun_args_sr:
  assumes "Fun f ts \<in> sr R"
  shows "\<forall>i < length ts. (ts ! i) \<in> sr R"
using assms by (auto simp: sr_def) (meson arg_subteq nth_mem supteq_trans)

lemma finite_sr:
  fixes R :: "('f, 'v) trs"
  assumes "finite R"
  shows "finite (sr R)"
proof -
  let ?h = "\<lambda>t. {s. t \<unrhd> s}"
  have *: "sr R = \<Union>(?h ` lhss R)" (is "_ = \<Union>(?B)") unfolding sr_def by force
  show "finite (sr R)" unfolding *
  proof (intro finite_Union)
     from assms have "finite (lhss R)" by auto
     from finite_imageI [OF this, of ?h] show "finite (?h ` lhss R)" by blast
  next
    fix M
    assume "M \<in> ?B"
    then show "finite M" by (auto simp: finite_subterms supt_supteq_not_supteq)
  qed
qed

lemma fterm_State_funas_imp_ta_fground:
  assumes "(fterm s, State q) \<in> (move A)\<^sup>*" and "funas_ta A \<subseteq> F"
  shows "fground F s"
proof -
  have "ground (State q)" by simp
  with assms(1) have "ground (fterm s)" using rtrancl_move_ground_ground by fastforce
  then have "ground s" by simp
  from move_reachable_states [THEN iffD1, OF assms(1)] have "q \<in> reachable_states A (fterm s)" .
  from reachable_states_funas_ta [OF this] have "funas_term s \<subseteq> funas_ta A" .
  then have "funas_term s \<subseteq> F" using assms(2) by blast
  then show "fground F s" using \<open>ground s\<close> by simp
qed

section \<open>Ground Instances\<close>

definition ground_instances :: "'f sig \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) terms"
where "ground_instances F t = { t \<cdot> \<sigma> | \<sigma>. fground F (t \<cdot> \<sigma>) }"

lemma ground_instances_subseteq_ancestors_ground_instances:
  "ground_instances F t \<subseteq> ancestors F R (ground_instances F t)"
apply (auto simp: ancestors_def)
apply (rule_tac x = "x" in exI)
apply (auto simp: ground_instances_def)
done

lemma ground_instances_Var [simp]:
  "ground_instances F (Var x) = {t. fground F t}"
by (auto simp: ground_instances_def)

lemma term_ground_instances_Fun:
  fixes ts :: "('f, 'v) term list"
  shows "ground_instances F (Fun f ts) \<subseteq> { Fun f ss | ss. (f, length ts) \<in> F \<and>
    length ts = length ss \<and> (\<forall>i < length ss. ss ! i \<in> ground_instances F (ts ! i))}"
proof -
  { fix ss :: "('f, 'v) term list"
    assume *: "is_partition (map vars_term ts)" and f: "(f, length ts) \<in> F"
      and "\<forall>x\<in>set ts. linear_term x"
      and l: "length ts = length ss"
      and "\<forall>i<length ss.
             \<exists>\<sigma>. ss ! i = ts ! i \<cdot> \<sigma> \<and>
                 (\<forall>x\<in>vars_term (ts ! i). ground (\<sigma> x)) \<and>
                 funas_term (ts ! i \<cdot> \<sigma>) \<subseteq> F" (is "\<forall>i<length ss. \<exists>\<sigma>. ?P i \<sigma>")
    then obtain \<tau> where **: "\<forall>i < length ss. ?P i (\<tau> i)" by metis
    from subst_merge [OF *, of \<tau>] obtain \<sigma>
      where ***: "\<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x"
      by auto
    then have 4: "\<forall>i <length ts. ts ! i \<cdot> \<sigma> = ts ! i \<cdot> \<tau> i" by (auto intro: term_subst_eq)
    with ** have "ss = map (\<lambda>t. t \<cdot> \<sigma>) ts" using l by (auto intro!: nth_equalityI)
    moreover have "\<forall>x\<in>set ts. \<forall>x\<in>vars_term x. ground (\<sigma> x)"
      using ** *** l by (auto simp: in_set_conv_nth)
    moreover have "(f, length ss) \<in> F" using l f by auto
    moreover have "(\<Union>x\<in>set ts. funas_term (x \<cdot> \<sigma>)) \<subseteq> F"
      using ** 4 l by (auto simp: in_set_conv_nth) blast
    ultimately have "\<exists>\<sigma>. ss = map (\<lambda>t. t \<cdot> \<sigma>) ts \<and>
              (\<forall>x\<in>set ts. \<forall>x\<in>vars_term x. ground (\<sigma> x)) \<and>
              (f, length ss) \<in> F \<and>
              (\<Union>x\<in>set ts. funas_term (x \<cdot> \<sigma>)) \<subseteq> F" by blast
  }
  then show ?thesis 
    by (auto simp: ground_instances_def)  (metis UN_subset_iff nth_mem)
qed

lemma linear_term_ground_instances_Fun:
  fixes ts :: "('f, 'v) term list"
  assumes "linear_term (Fun f ts)"
  shows "ground_instances F (Fun f ts) = { Fun f ss | ss. (f, length ts) \<in> F \<and>
    length ts = length ss \<and> (\<forall>i < length ss. ss ! i \<in> ground_instances F (ts ! i))}"
proof -
  { fix ss :: "('f, 'v) term list"
    assume *: "is_partition (map vars_term ts)" and f: "(f, length ts) \<in> F"
      and "\<forall>x\<in>set ts. linear_term x"
      and l: "length ts = length ss"
      and "\<forall>i<length ss.
             \<exists>\<sigma>. ss ! i = ts ! i \<cdot> \<sigma> \<and>
                 (\<forall>x\<in>vars_term (ts ! i). ground (\<sigma> x)) \<and>
                 funas_term (ts ! i \<cdot> \<sigma>) \<subseteq> F" (is "\<forall>i<length ss. \<exists>\<sigma>. ?P i \<sigma>")
    then obtain \<tau> where **: "\<forall>i < length ss. ?P i (\<tau> i)" by metis
    from subst_merge [OF *, of \<tau>] obtain \<sigma>
      where ***: "\<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x"
      by auto
    then have 4: "\<forall>i <length ts. ts ! i \<cdot> \<sigma> = ts ! i \<cdot> \<tau> i" by (auto intro: term_subst_eq)
    with ** have "ss = map (\<lambda>t. t \<cdot> \<sigma>) ts" using l by (auto intro!: nth_equalityI)
    moreover have "\<forall>x\<in>set ts. \<forall>x\<in>vars_term x. ground (\<sigma> x)"
      using ** *** l by (auto simp: in_set_conv_nth)
    moreover have "(f, length ss) \<in> F" using l f by auto
    moreover have "(\<Union>x\<in>set ts. funas_term (x \<cdot> \<sigma>)) \<subseteq> F"
      using ** 4 l by (auto simp: in_set_conv_nth) blast
    ultimately have "\<exists>\<sigma>. ss = map (\<lambda>t. t \<cdot> \<sigma>) ts \<and>
              (\<forall>x\<in>set ts. \<forall>x\<in>vars_term x. ground (\<sigma> x)) \<and>
              (f, length ss) \<in> F \<and>
              (\<Union>x\<in>set ts. funas_term (x \<cdot> \<sigma>)) \<subseteq> F" by blast
  }
  then show ?thesis using assms by (auto simp: ground_instances_def)
                                   (metis UN_subset_iff nth_mem)
qed

lemma Fun_in_ground_instances_VarD:
  assumes "Fun f ss \<in> ground_instances F (Var x)" and "s \<in> set ss"
  shows "s \<in> ground_instances F (Var x)"
using assms by (fastforce simp: ground_instances_def)

lemma args_in_ground_instances_FunD:
  assumes "Fun f ss \<in> ground_instances F (Fun f ts)" and "length ss = length ts" and "i < length ss"
  shows "ss ! i \<in> ground_instances F (ts ! i)"
using assms by (fastforce simp: ground_instances_def)

lemma ground_term_in_ground_instances_Var:
  assumes "fground F s"
  shows "s \<in> ground_instances F (Var x)"
using assms unfolding ground_instances_def by auto

lemma linear_args_ground_instances:
  assumes "linear_term (Fun f ts)" and "f = g" and "(f, length ts) \<in> F"
    and "length ts = length ss" and "\<forall>i < length ss. ss ! i \<in> ground_instances F (ts ! i)"
  shows "Fun g ss \<in> ground_instances F (Fun f ts)"
proof -
  have "\<forall>i < length ss. \<exists> \<sigma>. ss ! i = (ts ! i) \<cdot> \<sigma> \<and> ground ((ts ! i) \<cdot> \<sigma>)
    \<and> funas_term ((ts ! i) \<cdot> \<sigma>) \<subseteq> F"
    using assms(5) by (auto simp: ground_instances_def)
  then obtain \<sigma> where \<sigma>i: "\<forall>i < length ss. (ss ! i) = (ts ! i) \<cdot> \<sigma> i \<and> ground ((ts ! i) \<cdot> \<sigma> i)
    \<and> funas_term ((ts ! i) \<cdot> \<sigma> i) \<subseteq> F"
    by metis
  from subst_merge[of ts \<sigma>] assms(1) obtain \<tau>
    where "\<forall>i < length ts. \<forall>x \<in> vars_term (ts ! i). \<tau> x = \<sigma> i x" by auto
  then have "\<forall>i < length ts. ss ! i = (ts ! i) \<cdot> \<tau> \<and> fground F ((ts ! i) \<cdot> \<tau>)"
    using \<sigma>i assms(4) term_subst_eq by fastforce
  then have "Fun g ss = Fun f ts \<cdot> \<tau>" and "fground F (Fun f ts \<cdot> \<tau>)"
    using assms by (auto simp: in_set_conv_nth, metis map_nth_eq_conv) blast
  then show ?thesis using assms(1) by (auto simp: ground_instances_def)
qed

lemma move_ignores_ta_final:
  assumes "(s, t) \<in> move \<lparr>ta_final = Q, ta_rules = \<Delta>, ta_eps = E\<rparr>"
  shows "(s, t) \<in> move \<lparr>ta_final = P, ta_rules = \<Delta>, ta_eps = E\<rparr>"
using assms by (auto simp: move.simps)

lemma move_rtrancl_ignores_ta_final:
  assumes "(s, t) \<in> (move \<lparr>ta_final = Q, ta_rules = \<Delta>, ta_eps = E\<rparr>)\<^sup>*"
  shows "(s, t) \<in> (move \<lparr>ta_final = P, ta_rules = \<Delta>, ta_eps = E\<rparr>)\<^sup>*"
using assms move_ignores_ta_final by (simp add: move_mono'_rtrancl subsetI)

lemma reachable_states_ignores_ta_final:
  assumes "q \<in> reachable_states \<lparr>ta_final = Q, ta_rules = \<Delta>, ta_eps = E\<rparr> t"
  shows "q \<in> reachable_states \<lparr>ta_final = P, ta_rules = \<Delta>, ta_eps = E\<rparr> t"
proof -
  from assms have "(t, State q) \<in> (move \<lparr>ta_final = Q, ta_rules = \<Delta>, ta_eps = E\<rparr>)\<^sup>*"
    by (simp add: move_reachable_states)
  then have "(t, State q) \<in> (move \<lparr>ta_final = P, ta_rules = \<Delta>, ta_eps = E\<rparr>)\<^sup>*"
    using move_rtrancl_ignores_ta_final by blast
  then show ?thesis by (simp add: move_reachable_states)
qed

lemma ta_states_ground_instances_ta_subseteq:
  "ta_states (ground_instances_ta F c t) \<subseteq> {Fun c []} \<union> {star c s | s. s \<unlhd> t}"
by (induct t) (simp_all, force)

lemma ta_states_ground_instances_ta_ground:
  assumes "ground t"
  shows "ta_states (ground_instances_ta F c t) \<subseteq> {star c s | s. s \<unlhd> t}"
using assms by (induct t) (simp_all, force)

lemma not_ground_star_in_reachable_states:
  assumes "\<not> ground t" and "(a, 0) \<in> F"
  shows "Fun c [] \<in> reachable_states (ground_instances_ta F c t) (fterm (Fun a []))"
using assms by (induct t) (auto simp: ground_instances_ta_def sig_rules_def)

lemma star_ground_instances:
  assumes "(a, 0) \<in> F" and "funas_term t \<subseteq> F"
  shows "star a t \<in> ground_instances F t"
using assms by (induct t)
  (force simp: ground_instances_def star_subst_conv UN_subset_iff intro: exI [of _ "\<lambda>x. Fun a []"])+


lemma size_list_cong [cong]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g xs"
by (induct xs) force+

lemma size_star [simp]:
  "size \<circ> (star c) = size"
by (rule ext, induct_tac x) (auto)

lemma size_r_rhs_le:
  assumes "r \<in> ground_instances_rules F c t"
  shows "size (r_rhs r) \<le> size t"
using assms
apply (induct t)
apply (auto simp: sig_rules_def)
by (simp add: le_Suc_eq size_list_estimation')

lemma funas_term_r_states_subseteq_funas_term_ground_instance_rules:
  assumes "r \<in> ground_instances_rules F c t"
  shows "\<Union>(funas_term ` r_states r) \<subseteq> funas_term t \<union> {(c,0)}"
proof -
  from ground_instances_rules_r_states [OF assms]
    have "r_states r \<subseteq> {star c s | s. t \<unrhd> s}" .
  then have "\<Union>(funas_term ` r_states r) \<subseteq> \<Union>(funas_term ` {star c s | s. t \<unrhd> s})" by auto
  also have "\<dots> \<subseteq> funas_term (star c t)" using supteq_imp_funas_term_subset [of t] by auto
  also have "\<dots> \<subseteq> funas_term t \<union> {(c,0)}" using funas_term_star_conv[of c t]
    by (auto split: if_splits)
  finally show ?thesis .  
qed

lemma ground_instances_rules_not_sig_rules_shape:
  assumes "r \<in> ground_instances_rules F c u - sig_rules F (Fun c [])"
  shows "\<exists>f ts. r = TA_rule f (map (star c) ts) (star c (Fun f ts))"
using assms by (induct u) auto

lemma ground_instances_rules_not_star_shape:
  assumes "r \<in> ground_instances_rules F c u" and "r_rhs r \<noteq> Fun c []"
  shows "\<exists>f ts. r = TA_rule f (map (star c) ts) (star c (Fun f ts))"
proof -
  have "r \<in> ground_instances_rules F c u - sig_rules F (Fun c [])"
    using assms by (auto simp: sig_rules_def)
  from ground_instances_rules_not_sig_rules_shape [OF this] show ?thesis by auto
qed

lemma ground_instances_rules_unique:
  assumes "TA_rule g qs (star c (Fun f ts)) \<in> ground_instances_rules F c (Fun f ts)"
  shows "g = f \<and> qs = map (star c) ts"
proof -
  let ?t = "Fun f ts"
  from assms have "TA_rule g qs (star c ?t) \<in> {TA_rule f (map (star c) ts) (star c ?t)} \<union>
    \<Union>(ground_instances_rules F c ` set ts)" by force
  moreover have "TA_rule g qs (star c ?t) \<notin> \<Union>(ground_instances_rules F c ` set ts)"
    apply (auto dest!: size_r_rhs_le)
    using not_le size_simp1 by auto
  ultimately show ?thesis by auto
qed

lemma ta_rules_ground_instances_ta_unique:
  assumes "TA_rule g qs (star c (Fun f ts)) \<in> ta_rules (ground_instances_ta F c (Fun f ts))"
  shows "g = f \<and> qs = map (star c) ts"
using assms ground_instances_rules_unique by (auto simp: ground_instances_ta_def) fastforce+

lemma star_Fun_in_reachable_states_ground_instances_ta_imp_Fun:
  assumes "star c (Fun f ts) \<in> reachable_states (ground_instances_ta F c (Fun f ts)) (fterm s)"
  shows "\<exists>ss. s = Fun f ss"
proof -
  let ?A = "\<lambda>t. ground_instances_ta F c t"
  let ?t = "Fun f ts"
  show "\<exists>ss. s = Fun f ss"
  proof (cases s)
    case (Var x)
    show ?thesis using assms [unfolded Var] by simp
  next
    case (Fun g ss)
    let ?ss = "map fterm ss"
    let ?qs = "map (star c) ss"
    have "fterm (Fun g ss) = (Fun (Inl g) ?ss)" by simp
    with assms Fun have "star c ?t \<in> reachable_states (?A ?t) (Fun (Inl g) ?ss)" by simp
    then obtain q qs
      where rule: "TA_rule g qs q \<in> ta_rules (?A ?t)"
      and eps: "(q, star c ?t) \<in> (ta_eps (?A ?t))\<^sup>*"
      and "length qs = length ?ss"
      and "\<forall>i < length ?ss. qs ! i \<in> reachable_states (?A ?t) (?ss ! i)" by auto
    have "q = star c ?t" using eps ground_instances_ta_def [of F c ?t] by auto
    then have "TA_rule g qs (star c ?t) \<in> ta_rules (?A ?t)" using rule by auto
    from ta_rules_ground_instances_ta_unique [OF this]
      have "g = f \<and> qs = map (star c) ts" .
    then have "s = Fun f ss" using Fun by blast
    then show ?thesis by simp
  qed
qed

lemma fground_reachable_states_ground_instances_ta:
  assumes "fground F t"
  shows "Fun c [] \<in> reachable_states (ground_instances_ta F c (Var x)) (fterm t)"
  (is "?c \<in> reachable_states ?A ?t")
using assms
proof (induct t)
  case (Fun f ts)
  let ?ts = "map fterm ts"
  have "(f, length ts) \<in> F" using Fun by force
  then have 1: "TA_rule f (replicate (length ts) ?c) ?c \<in> ta_rules ?A"
    by (auto simp: ground_instances_ta_def sig_rules_def)
  have 2: "(?c, ?c) \<in> (ta_eps ?A)\<^sup>*" by auto
  have 3: "length (replicate (length ts) (Fun c [])) = length ?ts" by auto
  { fix i
    assume "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    moreover then have "fground F (ts ! i)" using Fun by auto
    ultimately have "?c \<in> reachable_states ?A (fterm (ts ! i))" using Fun by auto
  }
  then have 4: "\<forall>i < length ts. ?c \<in> reachable_states ?A (fterm (ts ! i))" by auto
  show ?case using reachable_states_InlI [OF 1 2 3] 4 by force
qed (auto)

lemma ta_rules_ground_instances_ta:
  assumes "s \<unrhd> t"
  shows "ta_rules (ground_instances_ta F c s) = ground_instances_rules F c t \<union>
   (ground_instances_rules F c s - ground_instances_rules F c t)"
using assms by (induct t) (auto simp: ground_instances_ta_def)

lemma reachable_states_mono:
  assumes "ta_rules A \<subseteq> ta_rules B"
    and "ta_eps A \<subseteq> ta_eps B"
  shows "reachable_states A t \<subseteq> reachable_states B t"
proof
  fix q
  assume "q \<in> reachable_states A t"
  then have "(t, State q) \<in> (move A)\<^sup>*" using move_reachable_states [symmetric] by fast
  from move_mono'_rtrancl [OF this assms] have "(t, State q) \<in> (move B)\<^sup>*" .
  then show "q \<in> reachable_states B t" using move_reachable_states by fast
qed

lemma ground_instances_subseteq_lang_ground_instances_ta:
  assumes "funas_term t \<subseteq> F"
  shows "ground_instances F t \<subseteq> lang (ground_instances_ta F c t)" 
  (is "?\<Sigma> t \<subseteq> lang (?A t)")
using assms
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then have IH: "\<And>i. i < length ts \<Longrightarrow> ?\<Sigma> (ts ! i) \<subseteq> lang (?A (ts ! i))"
    by (auto dest: nth_mem)
  { fix ss
    let ?rs = "\<lambda>A. (\<lambda>t. reachable_states A t)"
    assume l: "length ss = length ts"
      and ss: "\<forall>i < length ss. ss ! i \<in> ?\<Sigma> (ts ! i)"
    with IH have *: "\<forall>i < length ss. star c (ts ! i) \<in> ?rs (?A (ts ! i)) (fterm (ss ! i))"
      by (auto simp: lang_def)
    { fix i
      assume len: "i < length ss"
      then have s: "(Fun f ts) \<unrhd> ts ! i" by (auto simp: l)
      have 1: "ta_rules (?A (ts ! i)) \<subseteq> ta_rules (?A (Fun f ts))"
        using ground_instances_rules_mono [OF s] by (auto simp: ground_instances_ta_def)
      have 2: "ta_eps (?A (ts ! i)) \<subseteq> ta_eps (?A (Fun f ts))"
        by (auto simp: ground_instances_ta_def)
      have 3: "star c (ts ! i) \<in> ?rs (?A (ts ! i)) (fterm (ss ! i))"
        using * len by auto
      from reachable_states_mono [OF 1 2] 3
        have "star c (ts ! i) \<in> ?rs (?A (Fun f ts)) (fterm (ss ! i))" by blast
    }
    then have "\<forall>i < length ss. star c (ts ! i) \<in> ?rs (?A (Fun f ts)) (fterm (ss ! i))"
      by auto
    moreover have "TA_rule f (map (star c) ts) (star c (Fun f ts)) \<in> ta_rules (?A (Fun f ts))"
      by (auto simp: ground_instances_ta_def)
    ultimately have "star c (Fun f ts) \<in> ?rs (?A (Fun f ts)) (fterm (Fun f ss))"
      by (auto intro!: exI [of _ "star c (Fun f ts)"] exI [of _ "map (star c) ts"] simp: l)
    moreover have "ground (Fun f ss)"
      using ss by (auto simp: ground_instances_def) (metis ground_subst in_set_conv_nth)
    moreover have "{star c (Fun f ts)} = ta_final (?A (Fun f ts))" by auto
    ultimately have "Fun f ss \<in> lang (?A (Fun f ts))" by (auto simp: lang_def)
  }
  then show ?case using term_ground_instances_Fun [of F f ts] by (auto)
qed

(* A version of reachable_states which works on sets of rules and is equivalent to
   the other version if there are no epsilon-transitions. *)
fun reachable_states' :: "('q, 'f) ta_rule set \<Rightarrow> ('f + 'q, 'v) term \<Rightarrow> 'q set"
where
  "reachable_states' \<Delta> (State q) = {q}"
| "reachable_states' \<Delta> (Fun (Inl f) ts) =
    r_rhs ` {r \<in> \<Delta>. r_root r = f \<and> length (r_lhs_states r) = length ts \<and>
      (\<forall>i < length ts. (r_lhs_states r) ! i \<in> reachable_states' \<Delta> (ts ! i))}"
| "reachable_states' \<Delta> _ = {}"

export_code reachable_states' in Haskell

lemma reachable_states_reachable_states':
  assumes "ta_eps A = {}"
  shows "reachable_states A t = reachable_states' (ta_rules A) t"
using assms
proof (induct t rule: reachable_states.induct)
  case (2 A f ts)
  then show ?case
  apply auto
  defer
  apply (metis Tree_Automata.ta_rule.collapse)
  proof -
    fix x :: 'a and qs :: "'a list"
    assume a1: "\<forall>i<length ts. qs ! i \<in> reachable_states' (ta_rules A) (ts ! i)"
    assume a2: "f qs \<rightarrow> x \<in> ta_rules A"
    assume a3: "length qs = length ts"
    have f4: "\<forall>p t. \<not> p (t::('a, 'b) ta_rule) \<or> t \<in> Collect p"
      by (meson CollectI)
    have "\<forall>a f t T. ((a::'a) \<noteq> f (t::('a, 'b) ta_rule) \<or> t \<notin> T) \<or> a \<in> f ` T"
      by blast
    then show "x \<in> r_rhs ` {t \<in> ta_rules A. r_root t = f \<and> length (r_lhs_states t) = length ts \<and>
      (\<forall>n < length ts. r_lhs_states t ! n \<in> reachable_states' (ta_rules A) (ts ! n))}"
      using f4 a3 a2 a1 by force
  qed
qed (auto)

lemma reachable_states_reachable_states'_iff:
  assumes "ta_eps A = {}"
  shows "q \<in> reachable_states A t \<longleftrightarrow> q \<in> reachable_states' (ta_rules A) t"
using reachable_states_reachable_states' [OF assms] by (intro iffI) blast+

lemma reachable_states'_mono:
  assumes "\<Delta> \<subseteq> \<Delta>'"
  shows "reachable_states' \<Delta> t \<subseteq> reachable_states' \<Delta>' t"
using assms by (induct t rule: reachable_states'.induct, auto) blast


lemma star_reachable_states_ground_instances_ta_star:
  assumes "(a, 0) \<in> F" and "funas_term t \<subseteq> F"
  shows "star c t \<in> reachable_states (ground_instances_ta F c t) (fterm (star a t))"
using star_ground_instances [OF assms]
  and ground_instances_subseteq_lang_ground_instances_ta [OF assms(2)]
  by (auto simp: lang_def)

lemma subterm_star_reachable_states_ground_instances_ta:
  assumes "(a, 0) \<in> F" and "funas_term t \<subseteq> F"
    and "s \<unlhd> t"
  shows "star c s \<in> reachable_states (ground_instances_ta F c t) (fterm (star a s))"
using ground_instances_rules_mono [OF assms(3), of F c]
  and star_reachable_states_ground_instances_ta_star [of a F s c]
  and supteq_imp_funas_term_subset [OF assms(3)]
  and assms(1,2)
by (auto simp: ground_instances_ta_def reachable_states_reachable_states'
         dest: reachable_states'_mono)  

lemma const_fground:
  assumes "(a, 0) \<in> F"
  shows "fground F (Fun a [])"
using assms by auto

lemma accessible_ignores_ta_final:
  assumes "accessible TYPE('v) \<lparr> ta_final = X, ta_rules = Y, ta_eps = Z \<rparr> q"
    (is "accessible TYPE('v) ?A _")
  shows "accessible TYPE('v) \<lparr> ta_final = X', ta_rules = Y, ta_eps = Z \<rparr> q"
    (is "accessible TYPE('v) ?B _")
proof -
  thm assms [unfolded accessible_def]
  obtain t :: "('b, 'v) term" where g: "ground (fterm t)"
    and r: "q \<in> reachable_states ?A (fterm t)" using accessibleE [OF assms] .
  have 1: "ta_rules ?A \<subseteq> ta_rules ?B" by auto
  have 2: "ta_eps ?A \<subseteq> ta_eps ?B" by auto
  from r have "q \<in> reachable_states ?B (fterm t)" using reachable_states_mono [OF 1 2] by fast
  with g show "accessible TYPE('v) ?B q" by (auto simp: accessible_def)
qed

lemma accessible_ground_instances_ta:
  fixes t :: "('f, 'v) term"
  assumes "(a, 0) \<in> F" and "funas_term t \<subseteq> F"
  shows "\<forall>q \<in> ta_states (ground_instances_ta F c t). accessible TYPE('v) (ground_instances_ta F c t) q"
    (is "\<forall>q \<in> ?Q. ?acc q")
proof -
  { fix s
    assume "s \<unlhd> t"
    then have "?acc (star c s :: ('f, 'v) term)"
      using subterm_star_reachable_states_ground_instances_ta [of a F t s c] and assms
      by (force simp: accessible_def)
  }
  note * = this
  show ?thesis
  proof (cases "ground t")
    case (True)
    then have "?Q \<subseteq> {star c s | s. t \<unrhd> s}" by (rule ta_states_ground_instances_ta_ground)
    with * show ?thesis by blast
  next
    case (False)
    then have "?acc (Fun c [])" using not_ground_star_in_reachable_states [of t a F c] assms(1)
      by (auto dest: const_fground simp: accessible_def)
    moreover have "?Q \<subseteq> {Fun c []} \<union> {star c s | s. t \<unrhd> s}"
      by (rule ta_states_ground_instances_ta_subseteq)
    ultimately show ?thesis using * by blast
  qed
qed


lemma reachable_states_empty_ta [simp]:
  "reachable_states empty_ta (fterm t :: ('f + 'q, 'v) term) = {}"
by (induct "empty_ta :: ('q, 'f) ta" "fterm t :: ('f + 'q, 'v) term" arbitrary: t
    rule: reachable_states.induct)
   (auto simp: fterm_no_State)

locale etac =
  fixes c :: "'f" (* a fresh constant function symbol *)
    and F :: "'f sig"
    and R :: "('f, 'v) trs"
    and a :: "'f" (* the signature has to contain at least one constant *)
    and A :: "(('f, 'v) term, 'f) ta"
  assumes nonempty: "(a, 0) \<in> F"
    and fresh: "(c, 0) \<notin> F"
    and rinf: "funas_trs R \<subseteq> F"
    and ainf: "funas_ta A \<subseteq> F"
    and novar: "\<forall> (l, r) \<in> R. is_Fun l"
    and linear: "\<forall> (l, r) \<in> R. linear_term l \<and> linear_term r"
    and growing: "growing R"
    and accessible: "\<forall>q \<in> ta_states A. accessible TYPE('v) A q"
    and finiteF: "finite F"
    and finiteR: "finite R"
    and finite_qA: "finite (ta_states A)"
    and finite_tA: "finite (ta_rules A)"
begin

abbreviation "\<A>\<^sub>\<Sigma> t \<equiv> ground_instances_ta F c t"

abbreviation star_symbol ("\<star>") where "\<star> \<equiv> Fun c [] :: ('f, 'v) term"

definition restrict :: "('v \<Rightarrow> ('f, 'v) crterm) \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> ('f, 'v) crterm"
where
  "restrict \<theta> V = (\<lambda>x. (if x \<in> V then \<theta> x else State \<star>))"

lemma restrict_state_subst_eq:
  "t \<cdot> \<theta> = t \<cdot> (restrict \<theta> (vars_term t))"
proof (induct t)
  case (Var x)
  then show ?case by (auto simp: restrict_def)
next
  case (Fun f ts)
  { fix i
    assume "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    from Fun [OF this] have "ts ! i \<cdot> \<theta> = ts ! i \<cdot> (restrict \<theta> (vars_term (ts ! i)))"
      by (simp add: term_subst_eq_conv)
  }
  then have "\<forall>i < length ts. ts ! i \<cdot> \<theta> = ts ! i \<cdot> (restrict \<theta> (vars_term (ts ! i)))" by blast
  then show ?case using restrict_def term_subst_eq_conv by fastforce
qed


section \<open>Matching and propagating auxiliary tree automaton 'mp_ta'\<close>

lemma subseteq_r_states:
  assumes "X \<subseteq> Y"
  shows "\<Union>(r_states ` X) \<subseteq> \<Union>(r_states ` Y)"
using assms by (auto)

lemma ground_not_sig_rules_subseteq_ground_instances_rules:
  assumes "ground t" and "funas_term t \<subseteq> F"
  shows "\<not> sig_rules F \<star> \<subseteq> ground_instances_rules F c t" (is "\<not> ?L \<subseteq> ?R")
proof -
  from ground_instances_rules_r_states
    have "\<Union>(r_states ` ?R) \<subseteq> { star c s | s. t \<unrhd> s}" by fast
  then have 1: "\<star> \<notin> \<Union>(r_states ` ?R)" using assms fresh by force
  moreover from sig_rules_r_states [of _ F \<star>] have 2: "\<Union>(r_states ` ?L) = {\<star>}"
    by (metis ground_instances_rules.simps(1) nonempty ta_states_ground_instances_ta
        ta_states_ground_instances_ta_Var)
  ultimately have "\<not> \<Union>(r_states ` ?L) \<subseteq> \<Union>(r_states ` ?R)" by force
  then show ?thesis by auto
qed

lemma not_ground_sig_rules_subseteq_ground_instances_rules:
  assumes "\<not> ground t" and "funas_term t \<subseteq> F"
  shows "sig_rules F \<star> \<subseteq> ground_instances_rules F c t"
proof -
  from assms(1) obtain x where x: "t \<unrhd> Var x"
    by (auto simp: ground_vars_term_empty dest: vars_term_supteq)
  have "ground_instances_rules F c (Var x) = sig_rules F \<star>" by simp
  then show ?thesis using ground_instances_rules_mono [OF x] by auto
qed

lemma star_in_ground_instances_rules_or_ground:
  assumes "funas_term t \<subseteq> F"
  shows "\<star> \<in> \<Union>(r_states ` ground_instances_rules F c t) \<or> ground t"
proof (cases "ground t")
  case (True)
  then show ?thesis by auto
next
  case (False)
  with assms have "sig_rules F \<star> \<subseteq> ground_instances_rules F c t"
    using not_ground_sig_rules_subseteq_ground_instances_rules by auto
  then have "\<Union>(r_states ` sig_rules F \<star>) \<subseteq> \<Union>(r_states ` ground_instances_rules F c t)"
    (is "?L \<subseteq> ?R")
    by auto
  moreover from sig_rules_r_states [of _ F \<star>] have 2: "?L = {\<star>}"
    by (metis ground_instances_rules.simps(1) nonempty ta_states_ground_instances_ta
        ta_states_ground_instances_ta_Var)
  ultimately have "\<star> \<in> \<Union>(r_states ` ground_instances_rules F c t)" by auto
  then show ?thesis ..
qed

(* matching and propagating TA, called 'B' in AMs slides *)
definition mp_ta :: "(('f ,'v) term, 'f) ta"
where
"mp_ta = TA (\<Union>(ground_instances_rules F c ` lhss R))"

lemma mp_ta_ta_big_union:
  "mp_ta = ta_big_union ((\<lambda>l. (TA (ground_instances_rules F c l))) ` lhss R)"
by (auto simp: mp_ta_def ta_big_union_def)

lemma move_mp_ta_move_big_union_ground_instances_ta:
  "move mp_ta = move (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R))" (is "_ = move ?A")
proof -
  have "mp_ta = ta_big_union ((\<lambda>l. (TA (ground_instances_rules F c l))) ` lhss R)" (is "_ = ?B")
    using mp_ta_ta_big_union by auto
  then have "move mp_ta = move ?B" by simp
  also with move_ignores_ta_final have "move ?B = move ?A"
    by (auto simp: ground_instances_ta_def ta_big_union_def) blast+
  finally show ?thesis .
qed

lemma move_rtrancl_mp_ta_move_rtrancl_big_union_ground_instances_ta:
  "(move mp_ta)\<^sup>* = (move (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)))\<^sup>*"
using move_mp_ta_move_big_union_ground_instances_ta by metis

lemma reachable_states_mp_ta_reachable_states_big_union_ground_instances_ta:
  "reachable_states mp_ta t = reachable_states (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)) t"
using move_reachable_states move_rtrancl_mp_ta_move_rtrancl_big_union_ground_instances_ta
by fast

lemma ta_states_mp_ta':
  "ta_states mp_ta = ta_states (ta_big_union ((\<lambda>l. TA (ground_instances_rules F c l)) ` lhss R))"
using mp_ta_ta_big_union by auto

lemma ta_states_mp_ta'':
  "ta_states mp_ta = \<Union>((\<lambda>t. ta_states (TA (ground_instances_rules F c t))) ` lhss R)"
using ta_states_mp_ta' by (auto simp: ta_big_union_def ta_states_def)

lemma ta_states_ground_instances_ta':
  "ta_states (\<A>\<^sub>\<Sigma> t) = {star c s | s. s \<unlhd> t}"
unfolding ta_states_ground_instances_ta [OF nonempty]
apply (induct t)
apply (auto simp: sig_rules_def r_states_def Fun_supteq supteq_var_imp_eq)
apply (metis nonempty ta_rule.sel(3))
using star.simps(2) by fastforce

lemma ta_states_ground_instances_ta_ta_states_ground_instances_rules:
  "ta_states (\<A>\<^sub>\<Sigma> t) = ta_states (TA (ground_instances_rules F c t))"
using nonempty ta_states_def ta_states_ground_instances_ta by fastforce

lemma ta_states_mp_ta''':
  "ta_states mp_ta = \<Union>(ta_states ` \<A>\<^sub>\<Sigma> ` lhss R)"
using ta_states_mp_ta'' ta_states_ground_instances_ta_ta_states_ground_instances_rules
using image_cong image_image by auto

lemma ta_states_mp_ta'''':
  "ta_states mp_ta = ta_states (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R))"
using ta_states_ta_big_union ta_states_mp_ta''' by metis

(* lemma 3 from the whiteboard *)
lemma ta_states_mp_ta:
  "ta_states mp_ta = {star c s | s l r. (l, r) \<in> R \<and> l \<unrhd> s}"
proof -
  from ta_states_ground_instances_ta_ta_states_ground_instances_rules [symmetric]
    and ta_states_ground_instances_ta'
    have "\<forall>t. ta_states (TA (ground_instances_rules F c t)) = {star c s | s. t \<unrhd> s}" by blast
  with ta_states_mp_ta''
    have "ta_states mp_ta = \<Union>((\<lambda>t. {star c s | s. t \<unrhd> s}) ` lhss R)" by fastforce
  also have "\<dots> = {star c s | s l r. (l, r) \<in> R \<and> l \<unrhd> s}" by force 
  finally show ?thesis .
qed

lemma ta_states_mp_ta_sr:
  "ta_states mp_ta = {star c t | t. t \<in> sr R}"
using ta_states_mp_ta sr_def
by (auto, blast) auto

lemma funas_ta_mp_ta:
  "funas_ta mp_ta \<subseteq> F"
proof -
  have "funas_ta mp_ta = funas_ta (TA (\<Union>(ground_instances_rules F c ` lhss R)))"
    by (auto simp: mp_ta_def)
  { fix l
    assume l: "l \<in> lhss R"
    then have *: "funas_term l \<subseteq> F" using rinf lhs_wf by fastforce
    { fix r
      assume "r \<in> ground_instances_rules F c l"
      from funas_ta_rule_ground_instances_rules [OF * this] have "funas_ta_rule r \<subseteq> F" .
    }
    then have "\<forall>r \<in> ground_instances_rules F c l. funas_ta_rule r \<subseteq> F" by auto
  }
  then have "\<forall>l \<in> lhss R. (\<forall>r \<in> ground_instances_rules F c l. funas_ta_rule r \<subseteq> F)" by auto
  then show ?thesis by (auto simp: mp_ta_def funas_ta_def)
qed

lemma ta_states_mp_ta_accessible:
  assumes "q \<in> ta_states mp_ta"
  shows "accessible TYPE('v) mp_ta q"
proof -
  let ?\<Delta> = "\<lambda>t. ground_instances_rules F c t"
  { fix l
    assume l: "l \<in> lhss R"
    from ta_states_ground_instances_ta [OF nonempty, of c l]
      have * [simp]: "ta_states (\<A>\<^sub>\<Sigma> l) = ta_states (TA (?\<Delta> l))"
      by (auto simp: ta_states_def r_states_def)
    have "funas_term l \<subseteq> F" using l rinf lhs_wf by fastforce
    from accessible_ground_instances_ta [OF nonempty this, of c]
      have "\<forall>q \<in> ta_states (\<A>\<^sub>\<Sigma> l). accessible TYPE('v) (\<A>\<^sub>\<Sigma> l) q" .
    then have a: "\<forall>q \<in> ta_states (TA (?\<Delta> l)). accessible TYPE('v) (\<A>\<^sub>\<Sigma> l) q" by simp
    { fix q
      assume "q \<in> ta_states (TA (?\<Delta> l))"
      with a have "accessible TYPE('v) (\<A>\<^sub>\<Sigma> l) q" by auto
      then have "accessible TYPE('v) (TA (?\<Delta> l)) q"
        using accessible_ignores_ta_final [of "{star c l}" "?\<Delta> l" "{}" q "{}"]
        by (auto simp: ground_instances_ta_def)
      from accessibleE [OF this] obtain t :: "('f, 'v) term" where g: "ground t"
        and *: "q \<in> reachable_states (TA (?\<Delta> l)) (fterm t)" by auto
      have 1: "ta_rules (TA (?\<Delta> l)) \<subseteq> ta_rules mp_ta" using l by (auto simp: mp_ta_def)
      have 2: "ta_eps (TA (?\<Delta> l)) \<subseteq> ta_eps mp_ta" using l by (auto simp: mp_ta_def)
      from reachable_states_mono [OF 1 2] *
        have "q \<in> reachable_states mp_ta (fterm t)" by auto
      with g have "accessible TYPE('v) mp_ta q" by (auto simp: accessible_def)
    }
    then have "\<forall>q \<in> ta_states (TA (?\<Delta> l)). accessible TYPE('v) mp_ta q" by auto
  }
  then have "\<forall>l \<in> lhss R. (\<forall>q \<in> ta_states (TA (?\<Delta> l)). accessible TYPE('v) mp_ta q)" by auto
  then have "\<forall>q \<in> \<Union>((\<lambda>l. ta_states (TA (?\<Delta> l))) ` lhss R). accessible TYPE('v) mp_ta q" by fast
  moreover have "ta_states mp_ta = \<Union>((\<lambda>l. ta_states (TA (?\<Delta> l))) ` lhss R)"
    by (auto simp: mp_ta_def ta_states_def)
  ultimately show ?thesis using assms by fast
qed

lemma ta_eps_mp_ta_eq:
  assumes "(q, q') \<in> (ta_eps mp_ta)\<^sup>*"
  shows "q = q'"
using assms by (auto simp: mp_ta_def)

inductive gi
where
  "fground F t \<Longrightarrow> gi \<star> t"
| "length ss = length ts \<Longrightarrow> (f, length ts) \<in> F \<Longrightarrow> \<forall>i < length ts. gi (ss ! i) (ts ! i) \<Longrightarrow>
    gi (Fun f ss) (Fun f ts)"

lemma gi_fground:
  assumes "gi t s"
  shows "fground F s"
using assms
apply (induct)
apply auto
using in_set_idx apply force
by (metis in_set_idx subsetCE)

lemma TA_rule_ground_instances_ta:
  assumes "TA_rule f qs q \<in> ta_rules (\<A>\<^sub>\<Sigma> t)"
  shows "q = Fun f qs \<or> q = \<star>"
using assms
apply (auto simp: ground_instances_ta_def)
apply (induct t)
apply (auto simp: sig_rules_def)
done

lemma reachable_states_ta_big_union_ground_instances_ta_lhss_gi:
  assumes "star c s \<in> reachable_states (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)) (fterm u :: ('f + ('f, 'v) term, 'v) term)"
    (is "?s \<in> reachable_states ?A ?u")
  shows "gi (star c s) u"
proof -
  from assms have ner: "R \<noteq> {}" by (auto simp: ta_big_union_def)
  have "\<forall>q. ?u \<noteq> State q" by (auto simp: fterm_no_State)
  then have "reachable_states ?A ?u \<subseteq> ta_states ?A" using reachable_states_in_states by auto
  with assms have st: "star c s \<in> ta_states ?A" by auto
  have "ta_states mp_ta = ta_states ?A" using ta_states_mp_ta'''' .
  with st have "star c s \<in> {star c s | s. \<exists>l. (\<exists>r. (l, r) \<in> R) \<and> l \<unrhd> s}"
    using ta_states_mp_ta by auto
  then obtain l r s' where a1: "(l, r) \<in> R" and a2: "l \<unrhd> s'" and a3: "star c s = star c s'"
    using ner by blast
  from assms have "(?u, State ?s) \<in> (move ?A)\<^sup>*" using move_reachable_states by fast
  then have "(?u, State ?s) \<in> (move mp_ta)\<^sup>*"
    using move_rtrancl_mp_ta_move_rtrancl_big_union_ground_instances_ta by blast
  moreover have "funas_ta mp_ta \<subseteq> F" by (simp add: funas_ta_mp_ta)
  ultimately have *: "fground F u" using fterm_State_funas_imp_ta_fground by metis
  from assms a2 * a3 show ?thesis
  proof (induct u arbitrary: s s')
    case (Fun f us)
    note uFun = this
    let ?us = "map fterm us"
    consider (Var) x where "s = Var x"
      | (Fun) g ss where "s = Fun g ss" and "s \<noteq> \<star>"
      | (Star) "s = \<star>" by (cases s) auto
    then show ?case
    proof (cases)
      case (Var x)
      then show ?thesis using Fun by (auto simp: gi.intros)
    next
      case (Star)
      then show ?thesis using Fun by (auto simp: gi.intros)
    next
      case (Fun g ss)
      then obtain ss' where s': "s' = Fun g ss'" and ss': "map (star c) ss' = map (star c) ss"
        using uFun(5) by (cases s') auto
      let ?s = "star c (Fun g ss)"
      let ?ss = "map (star c) ss"
      let ?ss' = "map (star c) ss'"
      from uFun obtain qs where rl: "TA_rule f qs ?s \<in> ta_rules ?A"
        and "(?s, ?s) \<in> (ta_eps ?A)\<^sup>*"
        and l': "length qs = length ?us"
        and seq: "\<forall> i < length ?us. qs ! i \<in> reachable_states ?A (?us ! i)"
          by (auto simp: Fun ta_big_union_def)
      from rl obtain l' where "TA_rule f qs ?s \<in> ta_rules (\<A>\<^sub>\<Sigma> l')" by (auto simp: ta_big_union_def)
      then have f: "f = g" and qs: "qs = ?ss'"
        using Fun TA_rule_ground_instances_ta a1 fresh lhs_wf rinf uFun(3,4) ss' by fastforce+
      have "TA_rule f ?ss ?s \<in> ta_rules (\<A>\<^sub>\<Sigma> (Fun g ss))"
        by (auto simp: f ground_instances_ta_def)
      then have "TA_rule f ?ss ?s \<in> ta_rules (\<A>\<^sub>\<Sigma> l)"
        using  ground_instances_rules_mono [OF uFun(3) [unfolded Fun], of F c] ss' s'
        by (simp add: f ground_instances_ta_def)
      { fix i
        assume l: "i < length us"
        then have i: "us ! i \<in> set us" by auto
        have 2: "star c (ss' ! i) \<in> reachable_states ?A (fterm (us ! i))"
          using seq l l' qs ss' s' by fastforce
        have "i < length ss'" using l l' qs i by fastforce
        with uFun(3) [unfolded Fun] have 1: "l \<unrhd> ss' ! i" using s'
          by (meson arg_subteq nth_mem supteq_trans)
        from uFun(4) have 3: "fground F (us ! i)" using l by fastforce
        from uFun(1) [OF i 2 1 this] have "gi (star c (ss' ! i)) (us ! i)" by simp
      }
      then have "\<forall> i < length us. gi (star c (ss' ! i)) (us ! i)" by auto
      moreover have "length ?ss' = length us" using l' qs by auto
      moreover have "(f, length us) \<in> F" using uFun by auto 
      ultimately show ?thesis by (auto simp: Fun f ss' [symmetric] intro: gi.intros)
    qed
  qed (auto)
qed

lemma star_reachable_states_ground_instances_rules_gi:
  assumes "s \<unlhd> t" and "funas_term t \<subseteq> F"
  shows "star c s \<in> reachable_states (TA (ground_instances_rules F c t)) (fterm u) \<longleftrightarrow>
    gi (star c s) u" (is "?L \<longleftrightarrow> ?R")
proof
  let ?A = "\<lambda>t. TA (ground_instances_rules F c t)"
  assume a: ?R
  then show ?L using assms(1)
  proof (induct s arbitrary: u)
    case (Var x)
    note sVar = this
    then have u: "fground F u" by (auto elim: gi.cases)
    from fground_reachable_states_ground_instances_ta [OF this] have
      "\<star> \<in> reachable_states (ground_instances_ta F c (Var x)) (fterm u)" .
    then have "\<star> \<in> reachable_states (?A (Var x)) (fterm u)"
      using reachable_states_ignores_ta_final [of \<star>] by (auto simp: ground_instances_ta_def) blast
    then have *: "\<star> \<in> reachable_states (TA (sig_rules F \<star>)) (fterm u)" by auto
    from ground_instances_rules_mono [OF sVar(2)]
        have "sig_rules F \<star> \<subseteq> ground_instances_rules F c t" by auto
    then show ?case using * reachable_states_mono
      by (metis (no_types) star.simps(1) ta.select_convs(2,3) rev_subsetD subset_empty)
  next
    case (Fun f ss)
    let ?ss = "map (star c) ss"
    from Fun(2) have "gi (Fun f ?ss) u" by auto
    then obtain us where l: "length ?ss = length us"
      and "(f, length us) \<in> F"
      and a: "\<forall>i < length us. gi (?ss ! i) (us ! i)"
      and u: "u = Fun f us"
      using assms fresh Fun by (auto elim!: gi.cases)
    { fix i
      assume i: "i <length ss"
      then have s\<^sub>i: "ss ! i \<in> set ss" by auto
      moreover have "gi (star c (ss ! i)) (us ! i)" using Fun(2) [unfolded u] i a l by simp
      moreover have "t \<unrhd> ss ! i" using Fun(3) i by (auto elim: supteq_trans)
      ultimately have "star c (ss ! i) \<in> reachable_states (?A t) (fterm (us ! i))"
        using Fun(1) by simp
    }
    then have 1: "\<forall>i < length ss. star c (ss ! i) \<in> reachable_states (?A t) (fterm (us ! i))"
      by auto
    have "TA_rule f ?ss (star c (Fun f ss)) \<in> ground_instances_rules F c (Fun f ss)" by simp
    then have "TA_rule f ?ss (star c (Fun f ss)) \<in> ground_instances_rules F c t"
      using ground_instances_rules_mono [OF Fun(3), of F c] ..
    then show ?case unfolding u using l 1 by auto
  qed
next
  let ?A = "\<lambda>t. TA (ground_instances_rules F c t)"
  assume a: ?L
  then show ?R using assms(1)
  proof (induct s arbitrary: u)
    case (Var x)
    then have "(fterm u, State (star c (Var x))) \<in> (move (?A t))\<^sup>*"
      by (simp add: move_reachable_states)
    moreover have "funas_ta (?A t) \<subseteq> F" using funas_ta_rule_ground_instances_rules [OF assms(2)]
      by (auto simp: funas_ta_def)
    ultimately have "fground F u" using fterm_State_funas_imp_ta_fground [of u _ "?A t" F] by auto
    then show ?case by (auto intro: gi.intros)
  next
    case (Fun f ss)
    note sFun = this
    show ?case
    proof (cases u)
      case (Var y)
      from Fun [unfolded Var] show ?thesis by force
    next
      case (Fun h us)
      let ?us = "map fterm us"
      let ?qs = "map (star c) ss"
      let ?q = "star c (Fun f ss)"
      from sFun(2) [unfolded Fun] obtain q qs where r: "TA_rule h qs q \<in> ta_rules (?A t)"
        and e: "(q, ?q) \<in> (ta_eps (?A t))\<^sup>*"
        and l: "length qs = length ?us"
        and s: "\<forall>i < length ?us. qs ! i \<in> reachable_states (?A t) (?us ! i)" by auto
      have q: "q = ?q" using e by simp
      from r have "TA_rule h qs q \<in> ground_instances_rules F c t" by auto
      from ground_instances_rules_not_star_shape [OF this, unfolded q] obtain f' ss' where
        *: "TA_rule h qs ?q = TA_rule f' (map (star c) ss') (star c (Fun f' ss'))"
        using fresh star.simps(2) funas_term.simps(2) term.inject(2) ta_rule.sel(3) assms(2)
        const_fground contra_subsetD insertI1 le_sup_iff map_is_Nil_conv sFun(3) singletonD
        supteq_imp_funas_term_subset by force
      have f: "f' = f" using * by force
      then have h: "h = f" using * by blast
      have "star c (Fun f ss) = star c (Fun f' ss')" using * by blast
      with f have "?qs = map (star c) ss'" by auto
      with r * have qs: "qs = ?qs" by auto
      then have "TA_rule f ?qs ?q \<in> ta_rules (?A t)" using r [unfolded h q] by blast
      have l': "length ?us = length ss" using l qs by auto
      from s [unfolded qs] have **: "\<forall>i < length ?us. ?qs ! i \<in> reachable_states (?A t) (?us ! i)"
        by fastforce
      { fix i
        assume i: "i < length ss"
        then have a: "ss ! i \<in> set ss" by auto
        from l' i ** have "?qs ! i \<in> reachable_states (?A t) (?us ! i)" by auto
        then have 2: "star c (ss ! i) \<in> reachable_states (?A t) (fterm (us ! i))" using i l' by auto
        from sFun(3) have "t \<unrhd> ss ! i" using a
          by (meson supteq.refl supteq.subt supteq_trans)  
        from sFun(1) [OF a 2 this] have "gi (star c (ss ! i)) (us ! i)" .
      }
      then have "\<forall>i < length us. gi ((map (star c) ss) ! i) (us ! i)" using l' by auto
      moreover have "(f, length us) \<in> F" using assms(2) l qs sFun(3) by auto
      moreover have "length ?qs = length us" using l qs by simp
      ultimately show ?thesis unfolding Fun h by (auto intro: gi.intros)
    qed
  qed
qed

lemma reachable_states_ground_instances_ta_ta_states:
  "reachable_states (\<A>\<^sub>\<Sigma> t) (fterm s) \<subseteq> ta_states (\<A>\<^sub>\<Sigma> t)"
using reachable_states_in_states fterm_no_State by fast

(* Lemma 1 on whiteboard *)
lemma ta_states_ground_instances_ta_star:
  "q \<in> ta_states (\<A>\<^sub>\<Sigma> t) \<longleftrightarrow> (\<exists> s \<unlhd> t. q = star c s)"
using ta_states_ground_instances_ta' by auto

(* Lemma 2 on whiteboard *)
lemma reachable_states_ground_instances_ta_gi:
  assumes "q \<in> ta_states (\<A>\<^sub>\<Sigma> t)" and "funas_term t \<subseteq> F"
  shows "q \<in> reachable_states (\<A>\<^sub>\<Sigma> t) (fterm s) \<longleftrightarrow> gi q s"
proof -
  obtain u where "u \<unlhd> t" and [simp]: "q = star c u"
    using assms by (auto simp add: ta_states_ground_instances_ta' [of t])
  from star_reachable_states_ground_instances_rules_gi [OF this(1) assms(2), of s] show ?thesis
    by (simp add: ground_instances_ta_def reachable_states_reachable_states')
qed

lemma move_ta_big_union_ground_instances_ta_lhss_move_ground_instances_ta_l:
  fixes t :: "('f, 'v) term"
  assumes "(fterm t, State q) \<in> (move (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)))\<^sup>*"
    (is "(?t, State ?s) \<in> (move ?A)\<^sup>*")
  shows "\<exists>l \<in> lhss R. (fterm t, State ?s) \<in> (move (\<A>\<^sub>\<Sigma> l))\<^sup>*"
proof -
  from assms have ner: "R \<noteq> {}"
    by (auto simp: ta_big_union_def move_reachable_states)
  have "\<forall>q. ?t \<noteq> State q" by (auto simp: fterm_no_State)
  then have *: "reachable_states ?A ?t \<subseteq> ta_states ?A" using reachable_states_in_states by auto
  from assms have "?s \<in> reachable_states ?A ?t" by (auto simp: move_reachable_states)
  with * have st: "?s \<in> ta_states ?A" by auto
  have "ta_states mp_ta = ta_states ?A" using ta_states_mp_ta'''' .
  with st have "?s \<in> {star c s | s. \<exists>l. (\<exists>r. (l, r) \<in> R) \<and> l \<unrhd> s}"
    using ta_states_mp_ta by auto
  then obtain l r s' where a1: "(l, r) \<in> R" and a2: "l \<unrhd> s'" and a3: "?s = star c s'"
    using ner by blast
  have lhss: "l \<in> lhss R" using a1 by force
  have l: "funas_term l \<subseteq> F" using rinf a1 by (fastforce simp: funas_trs_def funas_rule_def)
    from assms have "?s \<in> reachable_states (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)) (fterm t)"
    using move_reachable_states by metis
  from reachable_states_ta_big_union_ground_instances_ta_lhss_gi [OF this [unfolded a3]]
    have 1: "gi ?s t" using a3 by blast
  from star_reachable_states_ground_instances_rules_gi [OF a2 l, unfolded a3 [symmetric], of t]
    and 1 have "?s \<in> reachable_states (TA (ground_instances_rules F c l)) ?t" by auto
  then have "(?t, State ?s) \<in> (move (TA (ground_instances_rules F c l)))\<^sup>*"
    by (auto simp: move_reachable_states)
  with move_rtrancl_ignores_ta_final have "(?t, State ?s) \<in> (move (\<A>\<^sub>\<Sigma> l))\<^sup>*"
    by (auto simp: ground_instances_ta_def) blast
  then show ?thesis using lhss by auto
qed

lemma fterm_State_move_rtrancl_conv:
  "(fterm s, State q) \<in> (move mp_ta)\<^sup>* \<longleftrightarrow> (fterm s, State q) \<in> (move mp_ta)\<^sup>+"
using fterm_no_State [of s q] by (auto dest: rtranclD)

(* lemma 4 on the whiteboard *)
lemma move_mp_ta_gi:
  fixes s :: "('f, 'v) term"
  assumes "\<exists>l \<in> lhss R. q \<in> ta_states (\<A>\<^sub>\<Sigma> l)"
  shows "(fterm s, State q) \<in> (move mp_ta)\<^sup>* \<longleftrightarrow> gi q s" (is "(?s, ?q) \<in> _ \<longleftrightarrow> _")
proof
  assume "(?s, ?q) \<in> (move mp_ta)\<^sup>*"
  then have "(?s, ?q) \<in> (move (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)))\<^sup>*"
    using move_rtrancl_mp_ta_move_rtrancl_big_union_ground_instances_ta by auto
  then obtain l where l: "l \<in> lhss R" and "(?s, ?q) \<in> (move (\<A>\<^sub>\<Sigma> l))\<^sup>*"
    using move_ta_big_union_ground_instances_ta_lhss_move_ground_instances_ta_l by metis
  then have 3: "q \<in> reachable_states (\<A>\<^sub>\<Sigma> l) ?s" by (auto simp: move_reachable_states)
  then have 1: "q \<in> ta_states (\<A>\<^sub>\<Sigma> l)" using reachable_states_ground_instances_ta_ta_states by blast 
  from l have 2: "funas_term l \<subseteq> F" using rinf by (fastforce simp: funas_trs_def funas_rule_def)
  show "gi q s" using reachable_states_ground_instances_ta_gi [THEN iffD1, OF 1 2 3] .
next
  assume a: "gi q s"
  from assms obtain l where l: "l \<in> lhss R" and 2: "q \<in> ta_states (\<A>\<^sub>\<Sigma> l)" by auto
  then have 1: "funas_term l \<subseteq> F" using rinf by (fastforce simp: funas_trs_def funas_rule_def)
  from reachable_states_ground_instances_ta_gi [THEN iffD2, OF 2 1 a]
    have "q \<in> reachable_states (\<A>\<^sub>\<Sigma> l) ?s" .
  moreover have "ta_rules (\<A>\<^sub>\<Sigma> l) \<subseteq> ta_rules (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R))"
    using l by (auto simp: ta_big_union_def)
  moreover have "ta_eps (\<A>\<^sub>\<Sigma> l) \<subseteq> ta_eps (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R))"
    using l by (auto simp: ta_big_union_def)
  ultimately  have "q \<in> reachable_states (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)) ?s"
    using reachable_states_mono by blast
  then have "(?s, ?q) \<in> (move (ta_big_union (\<A>\<^sub>\<Sigma> ` lhss R)))\<^sup>*" by (auto simp: move_reachable_states)
  then show "(?s, ?q) \<in> (move mp_ta)\<^sup>*"
    using move_rtrancl_mp_ta_move_rtrancl_big_union_ground_instances_ta by blast 
qed

lemma gi_ground_instances:
  assumes "linear_term t" and "funas_term t \<subseteq> F"
  shows "gi (star c t) s \<longleftrightarrow> s \<in> ground_instances F t" (is "?L \<longleftrightarrow> ?R")
using assms
proof (induct t arbitrary: s)
  case (Var x)
  show ?case by (auto elim: gi.cases intro: gi.intros)
next
  case (Fun f ts)
  then have "\<And>s. \<forall>t \<in> set ts. gi (star c t) s = (s \<in> ground_instances F t)" by auto blast+
  then show ?case unfolding linear_term_ground_instances_Fun [OF Fun(2)]
  using fresh \<open>funas_term (Fun f ts) \<subseteq> F\<close> by (auto elim!: gi.cases intro: gi.intros)
qed

lemma mp_ta_ta_states_accept_ground_instances:
  assumes "t \<in> sr R" and "funas_term s \<subseteq> F"
  shows "s \<in> ground_instances F t \<longleftrightarrow> (fterm s, State (star c t)) \<in> (move mp_ta)\<^sup>+" (is "?L \<longleftrightarrow> ?R")
proof -
  from assms(1) obtain l where *: "l \<in> lhss R" "t \<unlhd> l" by (force simp: sr_def)
  moreover then have "star c t \<in> ta_states (\<A>\<^sub>\<Sigma> l)" (is "?q \<in> _")
    unfolding ta_states_ground_instances_ta_star by auto
  ultimately have 3: "((fterm s, State ?q) \<in> (move mp_ta)\<^sup>*) = gi ?q s" using move_mp_ta_gi by blast
  have 1: "linear_term t" using * linear using subterm_linear by fastforce
  have 2: "funas_term t \<subseteq> F" using * rinf by (fastforce simp: funas_trs_def funas_rule_def)
  show ?thesis using 3 unfolding gi_ground_instances [symmetric, OF 1 2]
    by(auto simp:  fterm_State_move_rtrancl_conv)
qed

lemma c_in_ta_states_mp_ta_or_lhss_ground:
  "\<star> \<in> ta_states mp_ta \<or> (\<forall>l \<in> lhss R. ground l)"
unfolding ta_states_def mp_ta_def sig_rules_def r_states_def
using nonempty star_in_ground_instances_rules_or_ground
apply (auto)
by (metis fst_conv insert_iff lhs_wf r_states_def rinf)

lemma sr_Fun_in_ta_states_mp_ta:
  assumes "t \<in> sr R" and "t = Fun f ts"
  shows "star c t \<in> ta_states mp_ta"
using assms unfolding ta_states_mp_ta sr_def by force

lemma finite_sig_rules:
  "finite (sig_rules F x)"
proof -
  let ?f = "\<lambda>(f, n). TA_rule f (replicate n x) x"
  have **: "{TA_rule f (replicate n x) x |f n. (f, n) \<in> F} = ?f ` F"
    (is "?C = _") by auto
  from finite_imageI [OF finiteF, of ?f] have 2: "finite ?C" unfolding ** [symmetric] .
  then show ?thesis by (auto simp: sig_rules_def)
qed

lemma finite_ta_rules_ground_instances_ta:
  "finite (ta_rules (\<A>\<^sub>\<Sigma> t))"
apply (induct t)
using finite_sig_rules [of "Fun c []"]
apply (auto simp: ground_instances_ta_def)
done

lemma finite_ta_rules_mp_ta:
  "finite (ta_rules mp_ta)"
using finite_ta_rules_ground_instances_ta finiteR
by (auto simp: mp_ta_def ground_instances_ta_def)

lemma finite_ta_states_ground_instances_ta:
  "finite (ta_states (\<A>\<^sub>\<Sigma> t))"
using finite_ta_rules_ground_instances_ta
by (auto simp: ta_states_def r_states_def)

lemma finite_ta_states_mp_ta:
  "finite (ta_states mp_ta)"
using finite_ta_states_ground_instances_ta ta_states_mp_ta''' finiteR by auto

lemma non_empty_ta_rules_ground_instances_rules:
  "ta_rules (TA (ground_instances_rules F c t)) \<noteq> {}"
using nonempty by (induct t) (auto simp: sig_rules_def)

lemma non_empty_ta_rules_ground_instances_ta:
  "ta_rules (\<A>\<^sub>\<Sigma> t) \<noteq> {}"
using non_empty_ta_rules_ground_instances_rules
by (auto simp: ground_instances_ta_def)

section \<open>Second auxiliary tree automaton 'cr_ta'\<close>

definition cr_ta :: "(('f, 'v) term, 'f) ta" where
  "cr_ta = ta_union A mp_ta"

lemma funas_ta_cr_ta:
  "funas_ta cr_ta \<subseteq> F"
proof -
  have *: "funas_ta mp_ta \<subseteq> F" using funas_ta_mp_ta by blast
  have **: "funas_ta A \<subseteq> F" using ainf by blast
  from funas_ta_ta_union [OF ** *] show ?thesis unfolding cr_ta_def by simp
qed

lemma lang_cr_ta:
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "(lang cr_ta :: ('f, 'v) term set) = lang A"
proof -
  have "lang mp_ta = {}" by (auto simp: mp_ta_def)
  from lang_ta_union [OF assms, unfolded this cr_ta_def [symmetric]]
    show ?thesis by auto
qed

lemma cr_ta_ta_states_accept_ground_instances:
  assumes "t \<in> sr R" and "funas_term s \<subseteq> F"
    and "\<forall>q \<in> ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "s \<in> ground_instances F t \<longleftrightarrow> (fterm s, State (star c t)) \<in> (move cr_ta)\<^sup>+"
  (is "?L \<longleftrightarrow> ?R")
proof -
  let ?A = "A"
  let ?B = "mp_ta"
  let ?q = "star c t"
  let ?t = "fterm s"
  show ?thesis
  proof
    assume ?L
    then have "(?t, State ?q) \<in> (move ?B)\<^sup>*"
      using mp_ta_ta_states_accept_ground_instances [OF assms(1-2)] by simp
    then have **: "(?t, State ?q) \<in> (move ?A)\<^sup>* \<union> (move ?B)\<^sup>*" by auto 
    then have "(?t, State ?q) \<in> (move (ta_union ?A ?B))\<^sup>*"
      using moves_union [OF assms(3)] by auto
    then have "(?t, State ?q) \<in> (move (ta_union ?A ?B))\<^sup>+"
      by (simp add: fterm_no_State rtrancl_eq_or_trancl)
    then show ?R by (auto simp: cr_ta_def)
  next
    assume ?R
    then have "(?t, State ?q) \<in> (move cr_ta)\<^sup>*" by simp
    from move_reachable_states [THEN iffD1, OF this]
      have "?q \<in> reachable_states cr_ta ?t" .
    then have "?q \<in> reachable_states (ta_union ?A ?B) ?t"
      by (simp add: cr_ta_def)
    then have *: "?q \<in> reachable_states ?A ?t \<or> ?q \<in> reachable_states ?B ?t"
      using reachable_states_union [OF assms(3)] by force
    have s: "?q \<in> ta_states ?B" using ta_states_mp_ta_sr assms by auto
    consider (A) "?q \<in> reachable_states ?A ?t" | (B) "?q \<in> reachable_states ?B ?t" using * by auto
    then have "?q \<in> reachable_states ?B ?t"
    proof (cases)
      case (A)
      then have *: "?q \<in> ta_states ?A \<inter> ta_states ?B"
        using s reachable_states_in_states fterm_no_State by fast
      from A have "(?t, state TYPE('v) ?q) \<in> (move ?A)\<^sup>*" by (auto simp: move_reachable_states)
      then have "(?t, state TYPE('v) ?q) \<in> (move ?B)\<^sup>*" using assms(3) * by auto
      then show ?thesis by (auto simp: move_reachable_states)
    qed (auto)
    then have "(?t, state TYPE('v) ?q) \<in> (move ?B)\<^sup>*" by (auto simp: move_reachable_states)
    moreover have "?t \<noteq> state TYPE('v) ?q" by (simp add: fterm_no_State)
    ultimately have "(?t, state TYPE('v) ?q) \<in> (move mp_ta)\<^sup>+"
        by (simp add: \<open>?t \<noteq> state TYPE('v) ?q\<close> rtrancl_eq_or_trancl)
    with mp_ta_ta_states_accept_ground_instances [OF assms(1,2), symmetric] show ?L by simp
  qed
qed

fun qi :: "('f, 'v) term \<Rightarrow> ('v \<Rightarrow> ('f, 'v) term) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "qi t g (Var x) = (if x \<in> vars_term t then g x else \<star>)"
| "qi t g (Fun f ts) = (star c (Fun f ts))"

lemma ta_states_cr_ta:
  shows "ta_states cr_ta = ta_states A \<union> ta_states mp_ta"
unfolding cr_ta_def by auto

lemma finite_ta_states_cr_ta:
  "finite (ta_states cr_ta)"
proof -
  from finite_Un [THEN iffD2] finite_ta_states_mp_ta finite_qA
  show ?thesis unfolding ta_states_cr_ta by blast
qed

lemma finite_ta_rules_cr_ta:
  "finite (ta_rules cr_ta)"
proof -
  from finite_Un finite_tA finite_ta_rules_mp_ta
    show ?thesis by (auto simp: cr_ta_def ta_union_def)
qed

lemma sr_Fun_in_ta_states_cr_ta:
  assumes "t \<in> sr R" and "t = Fun f ts"
  shows "star c t \<in> ta_states cr_ta"
using sr_Fun_in_ta_states_mp_ta [OF assms] by (auto simp: cr_ta_def)

lemma Fun_lhs_subtD:
  assumes "l \<unrhd> Fun f ts" and "(l, r) \<in> R"
  shows "Fun f (map (star c) ts) \<in> ta_states cr_ta"
using assms sr_Fun_in_ta_states_cr_ta [of "Fun f ts"]
by (auto simp: sr_def)

lemma accessible_mono:
  fixes X Y :: "('q, 'f) ta"
  assumes "ta_rules X \<subseteq> ta_rules Y" and "ta_eps X \<subseteq> ta_eps Y"
    and "accessible TYPE('v) X q"
  shows "accessible TYPE('v) Y q"
proof -
  obtain t :: "('f, 'v) term" where g: "ground (fterm t)"
    and *: "q \<in> reachable_states X (fterm t)" using assms by auto
  from reachable_states_mono [OF assms(1,2)] *
    have "q \<in> reachable_states Y (fterm t)" by auto
  then show ?thesis using g by (auto simp: accessible_def)
qed

lemma ta_states_cr_ta_accessible:
  assumes "q \<in> ta_states cr_ta"
  shows "accessible TYPE('v) cr_ta q"
proof -
  consider (A) "q \<in> ta_states A" | (M) "q \<in> ta_states mp_ta" using assms by (auto simp: ta_states_cr_ta)
  then show ?thesis
  proof (cases)
    case (A)
    with accessible have "accessible TYPE('v) A q" by auto
    moreover have "ta_rules A \<subseteq> ta_rules cr_ta" and "ta_eps A \<subseteq> ta_eps cr_ta"
      by (auto simp: cr_ta_def)
    ultimately show ?thesis using accessible_mono by metis
  next
    case (M)
    with ta_states_mp_ta_accessible have "accessible TYPE('v) mp_ta q" by auto
    moreover have "ta_rules mp_ta \<subseteq> ta_rules cr_ta" and "ta_eps mp_ta \<subseteq> ta_eps cr_ta"
      by (auto simp: cr_ta_def)
    ultimately show ?thesis using accessible_mono by metis
  qed
qed

lemma finite_aux:
  assumes "finite Q"
  shows "finite {(f, qs) |f ls r qs. (Fun f ls, r) \<in> R \<and> set qs \<subseteq> Q \<and> length qs = length ls}"
    (is "finite ?A")
proof -
  have *: "?A = \<Union>{{(f, qs) |qs. set qs \<subseteq> Q \<and> length qs = length ls} | f ls r. (Fun f ls, r) \<in> R}"
    (is "_ = \<Union>?B") by auto
  show ?thesis unfolding *
  proof (intro finite_Union)
    let ?h = "\<lambda>(l, r). (case l of Fun f ls \<Rightarrow> {(f, qs) |qs. set qs \<subseteq> Q \<and> length qs = length ls} |
      Var _ \<Rightarrow> {})"
    have **: "?B = ?h ` R"
      using novar by (auto simp: image_iff split: term.splits prod.splits) fastforce+
    show "finite ?B" unfolding ** using finite_imageI [OF finiteR] .
  next
    fix M
    assume "M \<in> ?B"
    then show "finite M" using finite_lists_length_eq [OF assms] by auto
  qed
qed

lemma finite_lhs_ta_rules_over_finite_ta_states:
  assumes "finite Q"
  shows "finite { TA_rule f qs q | f ls r qs q.
    (Fun f ls, r) \<in> R \<and> set qs \<subseteq> Q \<and> length qs = length ls \<and> q \<in> Q}" (is "finite ?A")
proof -
  let ?h = "\<lambda>((f, qs), q). TA_rule f qs q"
  note * = finite_imageI [OF finite_cartesian_product [OF finite_aux [OF assms] assms], of ?h]
  show ?thesis by (rule finite_subset [OF _ *]) (force simp: image_iff)
qed

section \<open>The exactly completed tree automaton \<open>C\<^sub>R\<close>\<close>

inductive_set \<Delta>\<^sub>C where
  base: "r \<in> ta_rules cr_ta \<Longrightarrow> r \<in> \<Delta>\<^sub>C"
| step: "(Fun f ls, r) \<in> R \<Longrightarrow>
   range \<theta> \<subseteq> ta_states cr_ta \<Longrightarrow>
   q \<in> ta_states cr_ta \<Longrightarrow>
   (fterm r \<cdot> (State \<circ> \<theta>), (State q) :: ('f, 'v) crterm)
     \<in> (move (cr_ta\<lparr> ta_rules := \<Delta>\<^sub>C \<rparr>))\<^sup>* \<Longrightarrow> TA_rule f (map (\<lambda>li. qi r \<theta> li) ls) q \<in> \<Delta>\<^sub>C"

lemma \<Delta>\<^sub>C_subseteq_finite_set:
  "\<Delta>\<^sub>C \<subseteq> ta_rules cr_ta \<union> { TA_rule f qs q |f ls r qs q. (Fun f ls, r) \<in> R
    \<and> set qs \<subseteq> ta_states cr_ta
    \<and> length qs = length ls \<and> q \<in> ta_states cr_ta}" (is "_ \<subseteq> _ \<union> ?\<Delta>")
proof
  fix r
  assume "r \<in> \<Delta>\<^sub>C"
  then show "r \<in> ta_rules cr_ta \<union> ?\<Delta>"
  proof (induct)
    case (base r')
    then show ?case by auto
  next
    case (step f ls r' \<theta> q)
    { fix q
      assume "q \<in> set (map (qi r' \<theta>) ls)"
      then obtain l where l: "l \<in> set ls" and q: "q = qi r' \<theta> l"
        by (auto simp: in_set_conv_nth)
      consider (a) x where "l = Var x" and "q = \<theta> x" and "x \<in> vars_term r'"
        | (b) x where "l = Var x" and "q = \<star>" and "x \<notin> vars_term r'"
        | (c) g ts where "l = Fun g ts" and "q = (star c (Fun g ts))"
        using q by (induct l, auto)
      then have "q \<in> ta_states cr_ta"
      proof (cases)
        case (a)
        then show ?thesis using step(2) by auto
      next
        case (b)
        show ?thesis
        proof (cases "\<forall>l\<in>lhss R. ground l")
          case (True)
          then have "ground l" using step(1) l by auto
          then show ?thesis using b by auto
        next
          case (False)
          with c_in_ta_states_mp_ta_or_lhss_ground have "\<star> \<in> ta_states mp_ta" by auto
          then show ?thesis by (auto simp: b ta_states_cr_ta)
        qed
      next
        case (c)
        then have "star c (Fun g ts) \<in> ta_states mp_ta" unfolding ta_states_mp_ta using step(1) l by blast
        then show ?thesis by (auto simp: ta_states_cr_ta c)
      qed
    }
    then have 2: "set (map (qi r' \<theta>) ls) \<subseteq> ta_states cr_ta" by blast
    have 3: "length (map (qi r' \<theta>) ls) = length ls" by simp
    from step(1,3) 2 3 have "TA_rule f (map (qi r' \<theta>) ls) q \<in> ?\<Delta>" by blast
    then show ?case by auto
  qed
qed

lemma finite_\<Delta>\<^sub>C:
  "finite \<Delta>\<^sub>C"
using finite_qA and finite_tA
proof -
  let ?\<Delta> = "{ TA_rule f qs q |f ls r qs q. (Fun f ls, r) \<in> R \<and> set qs \<subseteq> ta_states cr_ta
    \<and> length qs = length ls \<and> q \<in> ta_states cr_ta}"
  from finite_ta_rules_cr_ta and finite_lhs_ta_rules_over_finite_ta_states [OF finite_ta_states_cr_ta]
    have "finite (ta_rules cr_ta \<union> ?\<Delta>)" by blast
  from finite_subset [OF \<Delta>\<^sub>C_subseteq_finite_set this] show ?thesis .
qed

lemma funas_ta_rule_\<Delta>\<^sub>C:
  assumes "r \<in> \<Delta>\<^sub>C"
  shows "funas_ta_rule r \<subseteq> F"
using assms
proof (cases)
  case (base)
  then show ?thesis using funas_ta_cr_ta unfolding funas_ta_def by blast
next
  case (step f ls r \<theta> q)
  from step(2) have "funas_rule (Fun f ls, r) \<subseteq> F" using rinf by (simp add: funas_trs_def) blast
  then have "funas_term (Fun f ls) \<subseteq> F" by (simp add: funas_rule_def)
  then show ?thesis using step(1) by (auto simp: funas_ta_rule_def)
qed

definition C\<^sub>R :: "(('f, 'v) term, 'f) ta"
  where
    "C\<^sub>R = cr_ta\<lparr> ta_rules := \<Delta>\<^sub>C \<rparr>"

lemma funas_ta_cr:
  "funas_ta C\<^sub>R \<subseteq> F"
unfolding C\<^sub>R_def funas_ta_def using funas_ta_rule_\<Delta>\<^sub>C by auto

lemma cr_ta_trans_subseteq_cr_trans:
  "ta_rules cr_ta \<subseteq> ta_rules C\<^sub>R" (is "?L \<subseteq> ?R")
proof
  fix t
  assume "t \<in> ?L"
  then show "t \<in> ?R" by (auto simp: C\<^sub>R_def intro: \<Delta>\<^sub>C.intros(1))
qed

lemma cr_ta_move_subseteq_cr_move:
  "move cr_ta \<subseteq> move C\<^sub>R" (is "?L \<subseteq> ?R")
proof
  fix s t
  assume "(s, t) \<in> ?L"
  then show "(s, t) \<in> ?R"
  apply (auto simp: C\<^sub>R_def)
  apply (induct rule: move.induct)
  apply (auto intro: move.intros)
  using subsetD[OF cr_ta_trans_subseteq_cr_trans] C\<^sub>R_def
  apply (auto simp: move.trans)
  done
qed

lemma cr_ta_move_rtrancl_subseteq_cr_move_rtrancl:
  "(move cr_ta)\<^sup>* \<subseteq> (move C\<^sub>R)\<^sup>*"
using cr_ta_move_subseteq_cr_move rtrancl_mono by blast

lemma reachable_states_cr_ta_subseteq_reachable_states_cr:
  "reachable_states cr_ta t \<subseteq> reachable_states C\<^sub>R t" (is "?L \<subseteq> ?R")
proof
  fix q
  assume "q \<in> ?L"
  from move_reachable_states [THEN iffD2, OF this] have "(t, State q) \<in> (move cr_ta)\<^sup>*" .
  then have "(t, State q) \<in> (move C\<^sub>R)\<^sup>*" using cr_ta_move_rtrancl_subseteq_cr_move_rtrancl by force
  from move_reachable_states [THEN iffD1, OF this] show "q \<in> ?R" .
qed

lemma cr_ta_lang_subseteq_cr_lang:
  "lang cr_ta \<subseteq> lang C\<^sub>R" (is "?L \<subseteq> ?R")
proof
  fix t
  assume "t \<in> ?L"
  then show "t \<in> ?R"
    apply (auto simp: lang_def)
    using C\<^sub>R_def reachable_states_cr_ta_subseteq_reachable_states_cr by fastforce
qed

lemma range_subseteq_qi:
  assumes "range \<theta> \<subseteq> ta_states cr_ta" and "t \<in> sr R"
  shows "qi r \<theta> t \<in> ta_states cr_ta"
proof -
consider (a) x where "t = Var x" and "qi r \<theta> t = \<theta> x" and "x \<in> vars_term r"
  | (b) x where "t = Var x" and "qi r \<theta> t = \<star>" and "x \<notin> vars_term r"
  | (c) f ts where "t = Fun f ts" and "qi r \<theta> t = star c (Fun f ts)"
  by (induct t) auto
  then show ?thesis
  proof (cases)
    case (a)
    then show ?thesis using assms(1) by auto
  next
    case (b)
    then show ?thesis
    proof (cases "\<forall>l\<in>lhss R. ground l")
      case (True)
      then have "ground t" using assms by (fastforce simp: sr_def)
      then show ?thesis using b by auto
    next
      case (False)
      with c_in_ta_states_mp_ta_or_lhss_ground have "\<star> \<in> ta_states mp_ta" by auto
      then show ?thesis by (auto simp: b ta_states_cr_ta)
    qed
  next
    case (c)
    then have "star c (Fun f ts) \<in> ta_states mp_ta" using assms unfolding ta_states_mp_ta sr_def by blast
    then show ?thesis by (auto simp: ta_states_cr_ta c)
  qed
qed

lemma r_states_deltac_subseteq_ta_states_cr_ta:
  assumes "r \<in> \<Delta>\<^sub>C"
  shows "r_states r \<subseteq> ta_states cr_ta"
using assms
proof (induct rule: \<Delta>\<^sub>C.induct)
  case (base r)
  then show ?case by (auto simp: ta_states_def)
next
  case (step f ls r \<theta> q)
  then show ?case using range_subseteq_qi by (auto simp: r_states_def sr_def) blast
qed

lemma ta_states_cr_eq [simp]:
  "ta_states C\<^sub>R = ta_states cr_ta" (is "?R = ?L")
proof -
  have *: "ta_rules C\<^sub>R = \<Delta>\<^sub>C" and
    **: "ta_final C\<^sub>R = ta_final cr_ta" and
    ***: "ta_eps C\<^sub>R = ta_eps cr_ta" by (simp add: C\<^sub>R_def)+
  show ?thesis
  proof (intro equalityI subsetI)
    fix q
    assume "q \<in> ?L"
    then show "q \<in> ?R"
      using cr_ta_trans_subseteq_cr_trans ** ***
      by (auto simp: ta_states_def r_states_def)
  next
    fix q
    assume "q \<in> ?R"
    then show "q \<in> ?L"
      unfolding ta_states_def *** ** * using r_states_deltac_subseteq_ta_states_cr_ta
      by (auto) (fastforce simp: ta_states_def)
  qed
qed

subsection \<open>An iterative inductive version of \<open>\<Delta>\<^sub>C\<close>\<close>

inductive it_k :: "nat \<Rightarrow> (('f, 'v) term, 'f) ta_rule \<Rightarrow> bool" where
  base: "r \<in> ta_rules cr_ta \<Longrightarrow> it_k k r"
| step: "(Fun f ls, r) \<in> R \<Longrightarrow>
    range \<theta> \<subseteq> ta_states cr_ta \<Longrightarrow>
    q \<in> ta_states cr_ta \<Longrightarrow>
    \<forall>r \<in> \<Delta>. (\<exists>n \<le> k. it_k n r) \<Longrightarrow>
    (fterm r \<cdot> (State \<circ> \<theta>), (State q) :: ('f, 'v) crterm)
      \<in> (move (cr_ta\<lparr> ta_rules := \<Delta> \<rparr>))\<^sup>* \<Longrightarrow>
    it_k (Suc k) (TA_rule f (map (\<lambda>l. qi r \<theta> l) ls) q)"

lemma it_k_0_ta_rules_cr_ta_nonempty:
  assumes "it_k 0 r"
  shows "ta_rules cr_ta \<noteq> {}"
using assms by (cases) auto

lemma it_k_Suc_mono:
  assumes "it_k n r"
  shows "it_k (Suc n) r"
using assms
apply (induct)
apply (auto intro: it_k.base)
apply (rule it_k.step)
apply auto
apply force
done

lemma it_k_mono: "m \<le> n \<Longrightarrow> it_k m r \<Longrightarrow> it_k n r"
apply (induct "n - m" arbitrary: m n)
apply auto
by (metis add_Suc diff_add_inverse2 it_k_Suc_mono le_add2 le_add_diff_inverse2)

lemma it_k_imp_\<Delta>\<^sub>C:
  assumes "it_k k r"
  shows "r \<in> \<Delta>\<^sub>C"
using assms
proof (induct)
  case (base r)
  then show ?case by (simp add: \<Delta>\<^sub>C.base)
next
  case (step f ls r \<theta> q \<Delta> k)
  from step(4) have "\<Delta> \<subseteq> \<Delta>\<^sub>C" by blast
  from move_mono [OF this, of cr_ta] and step(5) have
    "(fterm r \<cdot> (State \<circ> \<theta>), (State q) :: ('f, 'v) crterm)
      \<in> (move (cr_ta\<lparr>ta_rules := \<Delta>\<^sub>C\<rparr>))\<^sup>*" by blast  
  with step show ?case using \<Delta>\<^sub>C.step by simp
qed

lemma it_k_0 [simp]:
  "{r. it_k 0 r} = ta_rules cr_ta"
by (auto elim: it_k.cases simp: it_k.base)

lemma finite_it_k_0: "finite {r. it_k 0 r}" using finite_ta_rules_cr_ta it_k_0 by presburger

lemma it_k_0_subseteq_it_k: "{r. it_k 0 r} \<subseteq> {r. it_k k r}" using it_k_mono by force

lemma \<Delta>\<^sub>C_imp_ex_it_k:
  assumes "r \<in> \<Delta>\<^sub>C"
  shows "\<exists>k. it_k k r"
using assms
proof (induct)
  case (base r)
  from it_k.base [OF this] obtain k where "it_k k r" by simp
  then show ?case by blast
next
  case (step f ls r \<theta> q)
  let ?\<Delta> = "{r. \<exists>k. it_k k r}"
  have * [simp]: "{x \<in> \<Delta>\<^sub>C. \<exists>k. it_k k x} = ?\<Delta>" using it_k_imp_\<Delta>\<^sub>C by blast
  let ?A = "(\<lambda>r. SOME k. it_k k r) ` ?\<Delta>"
  show ?case
  proof (cases "?\<Delta> = {}")
    case (True)
    then have "\<forall>r \<in> ?\<Delta>. \<exists>k \<le> Max ?A. it_k k r" by auto
    from it_k.step [OF _ _ _ this] show ?thesis using step by (auto) blast
  next
    have "?\<Delta> \<subseteq> \<Delta>\<^sub>C" using * by blast
    from finite_subset [OF this finite_\<Delta>\<^sub>C] have "finite ?\<Delta>" .
    from finite_imageI [OF this] have "finite ?A" by blast
    moreover
    case (False)
    then have "?A \<noteq> {}" by blast
    ultimately have "finite ?A" and "?A \<noteq> {}" .
    then have *: "\<And>x. x \<in> ?A \<Longrightarrow> x \<le> Max ?A" by simp
    { fix x k assume "it_k k x" and x: "x \<in> ?\<Delta>"
      then have "it_k (SOME k. it_k k x) x" by (intro someI)
      from it_k_mono [OF _ this, of "Max ?A"]
        have "it_k (Max ?A) x" using * and x by auto }
    then have Delta: "?\<Delta> = {r. it_k (Max ?A) r}" by auto
    have "\<forall>r \<in> ?\<Delta>. \<exists>k \<le> Max ?A. it_k k r" by (subst Delta) auto
    from it_k.step [OF _ _ _ this] show ?thesis using step by (auto) blast
  qed
qed

primrec clean_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "clean_term (Var x) = Fun a []"
| "clean_term (Fun f ts) = (if (f, length ts) \<in> F then Fun f (map clean_term ts) else Fun a [])"

lemma clean_term_apply_subst:
  assumes "funas_term u \<subseteq> F"
  shows "clean_term (u \<cdot> \<sigma>) = u \<cdot> (clean_term \<circ> \<sigma>)"
using assms by (induct u) (auto)

lemma rstep_clean_term_imp:
  assumes "(s, t) \<in> rstep R"
  shows "(clean_term s, clean_term t) \<in> (rstep R)\<^sup>="
using assms
proof
  fix C \<sigma> l r
  presume *: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and **: "(l, r) \<in> R"
  from ** show "(clean_term s, clean_term t) \<in> (rstep R)\<^sup>=" unfolding *
  proof (induct C)
    case (Hole)
    then have "funas_term l \<subseteq> F" and "funas_term r \<subseteq> F" using funas_trs_def funas_rule_def rinf 
      by fastforce+
    then have 1: "clean_term (l \<cdot> \<sigma>) = l \<cdot> (clean_term \<circ> \<sigma>)"
      and 2: "clean_term (r \<cdot> \<sigma>) = r \<cdot> (clean_term \<circ> \<sigma>)"
      using clean_term_apply_subst by fast+
    from Hole have "(l \<cdot> (clean_term \<circ> \<sigma>), r \<cdot> (clean_term \<circ> \<sigma>)) \<in> rstep R" by fast
    then show ?case using 1 2 by simp
  next
    case (More f ts D ss)
    then show ?case
      apply auto
      apply (rule rstep_ctxt [where C = "More f (map clean_term ts) \<box> (map clean_term ss)", simplified])
      apply simp
      done
  qed
qed auto

lemma fground_clean_term [simp]:
  "fground F (clean_term t)"
using nonempty by (induct t) auto

lemma fground_imp_clean_term_eq:
  assumes "fground F s"
  shows "clean_term s = s"
using assms by (induct s, auto) (simp add: SUP_le_iff map_idI)

lemma rstep_fground_iff:
  assumes "fground F s" and "fground F t"
  shows "(s, t) \<in> ((rstep R) \<inter> {(s, t). fground F s \<and> fground F t})\<^sup>* \<longleftrightarrow> (s, t) \<in> (rstep R)\<^sup>*"
  (is "_ \<in> ?RTF \<longleftrightarrow> _")
proof
  assume "(s, t) \<in> ?RTF"
  then show "(s, t) \<in> (rstep R)\<^sup>*" using assms by (induct) (auto)
next
  assume "(s, t) \<in> (rstep R)\<^sup>*"
  then have "(s, clean_term t) \<in> ?RTF"
  using assms(1)
  proof (induct)
    case (step u t)
    note IH = step(3) [OF step(4)]
    have "(clean_term u, clean_term t) \<in> (rstep R)\<^sup>*" using rstep_clean_term_imp [OF step(2)] by auto
    moreover have "fground F (clean_term u)" by simp
    moreover have "fground F (clean_term t)" by simp
    ultimately have "(clean_term u, clean_term t) \<in> ?RTF"
      by (metis (mono_tags, lifting) IntI Un_iff mem_Collect_eq r_into_rtrancl
          rstep_clean_term_imp rtrancl_reflcl case_prodI step.hyps(2)) 
    then show ?case using IH by fastforce
  next
    case (base)
    from fground_imp_clean_term_eq [OF this] have "clean_term s = s" .
    then show ?case by auto
  qed
  then show "(s, t) \<in> ?RTF" using fground_imp_clean_term_eq [OF assms(2)] by auto
qed

lemma ancestors_subseteq_lang_cr:
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "ancestors F R (lang A) \<subseteq> lang C\<^sub>R" (is "?L \<subseteq> ?R")
proof
  fix t
  assume "t \<in> ?L"
  then obtain s where 1: "(t, s) \<in> (rstep R)\<^sup>*" and 2: "s \<in> (lang A)" and tfg: "fground F t"
    by (auto simp: ancestors_def)
  obtain q where "q \<in> reachable_states A (fterm s)" using 2 unfolding lang_def by blast
  from reachable_states_funas_ta [OF this] have sfg: "fground F s" using ainf 2
    by (auto simp: lang_def)
  from rstep_fground_iff [OF tfg sfg, THEN iffD2, OF 1] have
    "(t, s) \<in> (rstep R \<inter> {(s, t). fground F s \<and> fground F t})\<^sup>*" (is "(t, s) \<in> ?RTF") .
  then show "t \<in> ?R"
  proof (induct rule: converse_rtrancl_induct [case_names base step])
    case (base)
    then show ?case using cr_ta_lang_subseteq_cr_lang lang_cr_ta [OF assms] 2 by blast
  next
    case (step t u)
    from step(3) obtain q\<^sub>f where uq: "(fterm u, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" and qf: "q\<^sub>f \<in> ta_final C\<^sub>R" ..
    obtain C f ls r \<sigma> where t: "t = C\<langle>Fun f ls \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and
      rule: "(Fun f ls, r) \<in> R" using step(1) novar by fast
    with uq have "(fterm (C\<langle>r \<cdot> \<sigma>\<rangle>), State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" by blast
    then have "((fctxt C)\<langle>fterm (r \<cdot> \<sigma>)\<rangle>, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" (is "(?D\<langle>_\<rangle>, _) \<in> _") by simp
    from moves_State [OF this]
      obtain q where **: "(fterm (r \<cdot> \<sigma>), State q) \<in> (move C\<^sub>R)\<^sup>*"
      and "3'": "(?D\<langle>State q\<rangle>, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" by blast
    then have *: "(fterm r \<cdot> (fterm \<circ> \<sigma>), State q) \<in> (move C\<^sub>R)\<^sup>*"
      unfolding fterm_subst_distrib by simp
    have lin: "linear_term (fterm r)" using linear rule by fastforce
    from step(3) have "ground u" using lang_def by blast
    with u have g: "ground (r \<cdot> \<sigma>)" by simp
    have 1: "fground F (Fun f ls \<cdot> \<sigma>)" using step(1) unfolding t by (simp add: o_def)
    then have gli: "\<forall>i < length ls. ground ((ls ! i) \<cdot> \<sigma>)" by fastforce
    then have "\<forall>x \<in> vars_term (Fun f ls). funas_term (\<sigma> x) \<subseteq> F"
      using subst_image_subterm[of _ f ls \<sigma>] supt_imp_funas_term_subset 1 by blast
    then have "\<forall>x \<in> vars_term (Fun f ls). funas_term (\<sigma> x) \<subseteq> F" using nonempty by auto
    moreover have "funas_term (Fun f ls) \<subseteq> F" using lhs_wf rule rinf by blast
    ultimately have "funas_term (Fun f ls \<cdot> \<sigma>) \<subseteq> F"  using subst_sig_term_sig_imp by blast
    then have fli: "\<forall>i < length ls. funas_term ((ls ! i) \<cdot> \<sigma>) \<subseteq> F" by force
    { fix x
      assume x: "r \<cdot> \<sigma> = Var x"
      from move_reachable_states [THEN iffD1, OF **] have "q \<in> reachable_states C\<^sub>R (fterm (r \<cdot> \<sigma>))" .
      moreover then have "reachable_states C\<^sub>R (fterm (r \<cdot> \<sigma>)) = {}" using x reachable_states.simps(3)
        by fastforce
      ultimately have "q \<in> ta_states C\<^sub>R" by auto
    }
    moreover
    { fix f ts
      assume f: "r \<cdot> \<sigma> = Fun f ts"
      with ** have "(fterm (Fun f ts), State q) \<in> (move C\<^sub>R)\<^sup>*" by auto
      from move_reachable_states [THEN iffD1, OF this]
        have "q \<in> reachable_states C\<^sub>R (fterm (Fun f ts))" .
      then obtain f qs q' where
        trans: "TA_rule f qs q' \<in> ta_rules C\<^sub>R" and
        eps: "(q', q) \<in> (ta_eps C\<^sub>R)\<^sup>*" and
        len: "length qs = length (map fterm ts)" and
        qs: "\<forall>i < length (map fterm ts). qs ! i \<in> reachable_states C\<^sub>R ((map fterm ts) ! i)"
        using reachable_states.simps(2)[of C\<^sub>R f "map fterm ts"] by force
      have "q' \<in> ta_states C\<^sub>R" using r_states_in_states [OF trans] by blast
      with eps have "q \<in> ta_states C\<^sub>R"
      proof (cases "q' = q")
        case (False)
        with eps have "(q', q) \<in> (ta_eps C\<^sub>R)\<^sup>+"
          by (simp add: rtrancl_eq_or_trancl)
        from trancl_ta_epsD [OF this] have "{q', q} \<subseteq> ta_states C\<^sub>R" .
        then show ?thesis by blast
      qed (auto)
    }
    ultimately have state: "q \<in> ta_states C\<^sub>R" using term.exhaust by blast
    then have state': "q \<in> ta_states cr_ta" by simp
    obtain \<theta> where vars: "\<forall>x \<in> vars_term (fterm r). ((fterm \<circ> \<sigma>) x, (State \<circ> \<theta>) x) \<in> (move C\<^sub>R)\<^sup>*" and
      4: "(fterm r \<cdot> ((State \<circ> \<theta>) :: ('f + ('f, 'v) term, 'v) subst), State q) \<in> (move C\<^sub>R)\<^sup>*" and
      \<theta>: "range \<theta> \<subseteq> ta_states C\<^sub>R"
      using moves_state_subst [OF * state lin] by force
    from \<theta> have 3: "range \<theta> \<subseteq> ta_states cr_ta" using C\<^sub>R_def ta_states_cr_eq by auto
    from 4 have 5: "(fterm r \<cdot> ((State \<circ> \<theta>) :: ('f + ('f, 'v) term, 'v) subst), State q) \<in>
      (move (cr_ta\<lparr>ta_rules := \<Delta>\<^sub>C\<rparr>))\<^sup>*" unfolding C\<^sub>R_def by auto
    have rule': "TA_rule f (map (\<lambda>li. qi r \<theta> li) ls) q \<in> \<Delta>\<^sub>C" using \<Delta>\<^sub>C.intros(2) [OF rule 3 state' 5] .
    let ?ls = "map (fterm \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ls"
    let ?qs = "map (State \<circ> (qi r \<theta>)) ls"
    { fix i
      assume l: "i < length (map fterm ls)"
      then have l': "i < length ls" by simp
      have "(fterm (ls ! i) \<cdot> (fterm \<circ> \<sigma>), State (qi r \<theta> (ls ! i))) \<in> (move C\<^sub>R)\<^sup>*"
      proof (cases "ls ! i \<in> Var ` vars_term r")
        case (True)
        then have eq: "State (qi r \<theta> (ls ! i)) = fterm (ls ! i) \<cdot> (State \<circ> \<theta>)" by fastforce
        from True vars have "(fterm (ls ! i) \<cdot> (fterm \<circ> \<sigma>), fterm (ls ! i) \<cdot> (State \<circ> \<theta>)) \<in> (move C\<^sub>R)\<^sup>*"
          by fastforce
        then show ?thesis by (simp add: eq)
      next
        let ?t = "fterm (ls ! i)"
        let ?\<sigma> = "(fterm \<circ> \<sigma>)"
        let ?t' = "?t \<cdot> ?\<sigma>"
        case (False)
        then have eq: "qi r \<theta> (ls ! i) = star c (ls ! i)" by (cases "ls ! i") auto
        have 1: "ls ! i \<in> sr R" using rule sr_def [of R] l' by force
        moreover have 2: "funas_term (ls ! i \<cdot> \<sigma>) \<subseteq> F" using fli l' by blast
        moreover have 3: "ground (ls ! i \<cdot> \<sigma>)" using gli l' by blast
        ultimately have 4: "(ls ! i) \<cdot> \<sigma> \<in> ground_instances F (ls ! i)" using ground_instances_def
          by blast
        have "(fterm (ls ! i \<cdot> \<sigma>), State (star c (ls ! i))) \<in> (move cr_ta)\<^sup>+"
          using cr_ta_ta_states_accept_ground_instances [OF 1 2 assms, THEN iffD1, OF 4] .
        then have "(fterm (ls ! i \<cdot> \<sigma>), State (star c (ls ! i))) \<in> (move cr_ta)\<^sup>*" by fast
        then have "(fterm (ls ! i \<cdot> \<sigma>), State (star c (ls ! i))) \<in> (move C\<^sub>R)\<^sup>*"
          using cr_ta_move_rtrancl_subseteq_cr_move_rtrancl by auto
        then show ?thesis unfolding eq fterm_subst_distrib[of "ls ! i" \<sigma>] .
      qed
    }
    then have qis: "\<forall>i < length (map fterm ls).
      (fterm (ls ! i) \<cdot> (fterm \<circ> \<sigma>), State (qi r \<theta> (ls ! i))) \<in> (move C\<^sub>R)\<^sup>*" by blast
    moreover have "length (map fterm ls) = length ?ls" by simp
    ultimately have qis': "\<forall> i < length ?ls. (?ls ! i, ?qs ! i) \<in> (move C\<^sub>R)\<^sup>*" by (auto simp: o_def)
    have len': "length ?ls = length ?qs" by simp
    from args_steps_imp_steps [OF ctxt_closed_move len' qis', of "Inl f"]
      have 1: "(Fun (Inl f) ?ls, Fun (Inl f) ?qs) \<in> (move C\<^sub>R)\<^sup>*" .
    have "TA_rule f (map (qi r \<theta>) ls) q \<in> ta_rules C\<^sub>R" using rule' C\<^sub>R_def by force
    from move.trans[OF this, of \<box>] have 2: "(Fun (Inl f) ?qs, State q) \<in> (move C\<^sub>R)\<^sup>*" by auto
    have 3: "fterm t = ?D\<langle>Fun (Inl f) ?ls\<rangle>" using t by simp
    have "(Fun (Inl f) ?ls, State q) \<in> (move C\<^sub>R)\<^sup>*" using rtrancl_trans[OF 1 2] .
    from ctxt.closedD [OF ctxt.closed_rtrancl[OF ctxt_closed_move] this]
      have "(fterm t, ?D\<langle>State q\<rangle>) \<in> (move C\<^sub>R)\<^sup>*" using 3 by presburger
    then have "(fterm t, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" using "3'" by fastforce
    then have "q\<^sub>f \<in> reachable_states C\<^sub>R (fterm t)" by (simp add: move_reachable_states)
    with qf have "ta_final C\<^sub>R \<inter> reachable_states C\<^sub>R (fterm t) \<noteq> {}" by auto
    moreover have "ground t" using step(1) by blast
    ultimately show ?case unfolding lang_def by auto
  qed
qed

lemma cr_ta_rules:
  "ta_rules C\<^sub>R = ta_rules cr_ta \<union> (\<Delta>\<^sub>C - ta_rules cr_ta)"
unfolding C\<^sub>R_def by (auto simp: \<Delta>\<^sub>C.base)

lemma cr_move_iff'':
  "(s, t) \<in> move C\<^sub>R \<longleftrightarrow> (s, t) \<in> move (ta_union cr_ta (TA (\<Delta>\<^sub>C - ta_rules cr_ta)))"
unfolding ta_union_def using cr_ta_rules by (auto simp: C\<^sub>R_def cr_ta_def ta_union_def)

lemma cr_move_iff:
  "(s, t) \<in> (move C\<^sub>R)\<^sup>+ \<longleftrightarrow> (s, t) \<in> (move (ta_union cr_ta (TA (\<Delta>\<^sub>C - ta_rules cr_ta))))\<^sup>+"
unfolding ta_union_def using cr_ta_rules by (auto simp: C\<^sub>R_def cr_ta_def ta_union_def)

lemma cr_move_iff':
  "(s, t) \<in> (move C\<^sub>R)\<^sup>+ \<longleftrightarrow>
   (s, t) \<in> (move (cr_ta\<lparr> ta_rules := ta_rules cr_ta \<union> (\<Delta>\<^sub>C - ta_rules cr_ta)\<rparr>))\<^sup>+"
  (is "?L \<longleftrightarrow> ?R")
unfolding C\<^sub>R_def using cr_ta_rules by auto (metis Diff_partition \<Delta>\<^sub>C.base cr_ta_rules subsetI)+

lemma cr_moves_imp_it_k_moves:
  assumes "(s, t) \<in> (move C\<^sub>R)\<^sup>+"
  shows "\<exists>k. (s, t) \<in> (move (ta_union cr_ta (TA {r. it_k k r})))\<^sup>+"
proof -
  from assms show ?thesis
  proof (induct)
    case (base t)
    then show ?case
    proof (cases)
      case (trans f qs q C)
      from trans(3) show ?thesis unfolding cr_ta_rules
      proof
        assume "TA_rule f qs q \<in> ta_rules cr_ta"
        then show ?thesis using trans(1,2) 
          by (intro exI [of _ 0]) (simp add: move.trans trancl.r_into_trancl)
      next
        assume "TA_rule f qs q \<in> \<Delta>\<^sub>C - ta_rules cr_ta"
        then have "{TA_rule f qs q} \<subseteq> \<Delta>\<^sub>C - ta_rules cr_ta" by auto
        then obtain n where "{TA_rule f qs q} \<subseteq> {r. it_k n r} - {r. it_k 0 r}"
          using \<Delta>\<^sub>C_imp_ex_it_k by auto
        then have 1: "{TA_rule f qs q} \<subseteq> {r. it_k n r}" by auto
        have "(s, t) \<in> (move (ta_union cr_ta (TA {TA_rule f qs q})))\<^sup>+"
          using trans(1,2) unfolding ta_union_def by (simp add: move.trans trancl.r_into_trancl)
        moreover have "ta_rules (ta_union cr_ta (TA {TA_rule f qs q})) \<subseteq>
          ta_rules (ta_union cr_ta (TA {r. it_k n r}))" using 1 by (auto)
        moreover have "ta_eps (ta_union cr_ta (TA {TA_rule f qs q})) \<subseteq>
          ta_eps (ta_union cr_ta (TA {r. it_k n r}))" by (auto)
        ultimately show "\<exists>k. (s, t) \<in> (move (ta_union cr_ta (TA {r. it_k k r})))\<^sup>+"
          using move_mono'_trancl by blast
      qed
    next
      case (eps q q' C)
      from eps(3) have "(q, q') \<in> (ta_eps cr_ta)\<^sup>*" unfolding C\<^sub>R_def by simp
      moreover then have "(s, t) \<in> (move (ta_union cr_ta (TA {r. it_k 0 r})))\<^sup>+"
        using eps(1,2) by (auto simp: move.eps trancl.r_into_trancl)
      ultimately show ?thesis by blast
    qed
  next
    case (step u t)
    from step(3) obtain n where *: "(s, u) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+" by auto
    from step(2) show ?case
    proof (cases)
      case (trans f qs q C)
      from trans(3) show ?thesis unfolding cr_ta_rules
      proof
        assume "TA_rule f qs q \<in> ta_rules cr_ta"
        then have "TA_rule f qs q \<in> ta_rules (ta_union cr_ta (TA {r. it_k n r}))" by fastforce
        from move.trans [OF this, of C]
          have "(u, t) \<in> move (ta_union cr_ta (TA {r. it_k n r}))" using trans(1,2) by fast
        then have "(u, t) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+" by blast
        then have "(s, t) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+" using * by force
        then show ?thesis by blast
      next
        assume "TA_rule f qs q \<in> \<Delta>\<^sub>C - ta_rules cr_ta"
        then have "{TA_rule f qs q} \<subseteq> \<Delta>\<^sub>C - ta_rules cr_ta" by auto
        then obtain k where "{TA_rule f qs q} \<subseteq> {r. it_k k r} - {r. it_k 0 r}"
          using \<Delta>\<^sub>C_imp_ex_it_k by auto
        then have 1: "{TA_rule f qs q} \<subseteq> {r. it_k k r}" by auto
        have"(u, t) \<in> (move (ta_union cr_ta (TA {TA_rule f qs q})))\<^sup>+"
          using trans(1,2) by (simp add: move.trans trancl.r_into_trancl)
        moreover have "ta_rules (ta_union cr_ta (TA {TA_rule f qs q})) \<subseteq>
          ta_rules (ta_union cr_ta (TA {r. it_k k r}))" using 1 by (auto)
        moreover have "ta_eps (ta_union cr_ta (TA {TA_rule f qs q})) \<subseteq>
          ta_eps (ta_union cr_ta (TA {r. it_k k r}))" by (auto)
        ultimately have k: "(u, t) \<in> (move (ta_union cr_ta (TA {r. it_k k r})))\<^sup>+"
          using move_mono'_trancl by blast
        then show ?thesis
        proof (cases "k \<le> n")
          case (True)
          from it_k_mono [OF this] have s: "{r. it_k k r} \<subseteq> {r. it_k n r}" by blast
          then have "ta_rules (ta_union cr_ta (TA {r. it_k k r})) \<subseteq>
            ta_rules (ta_union cr_ta (TA {r. it_k n r}))" by (auto)
          moreover have "ta_eps (ta_union cr_ta (TA {r. it_k k r})) \<subseteq>
            ta_eps (ta_union cr_ta (TA {r. it_k n r}))" using s by (auto)
          ultimately have "(u, t) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+"
            using move_mono'_trancl k by blast
          then show ?thesis using * trancl_trans by fast
        next
          case (False)
          then have "n \<le> k" by auto
          from it_k_mono [OF this] have s: "{r. it_k n r} \<subseteq> {r. it_k k r}" by blast
          then have "ta_rules (ta_union cr_ta (TA {r. it_k n r})) \<subseteq>
            ta_rules (ta_union cr_ta (TA {r. it_k k r}))" by (auto)
          moreover have "ta_eps (ta_union cr_ta (TA {r. it_k n r})) \<subseteq>
            ta_eps (ta_union cr_ta (TA {r. it_k k r}))" using s by (auto)
          ultimately have "(s, u) \<in> (move (ta_union cr_ta (TA {r. it_k k r})))\<^sup>+"
            using move_mono'_trancl * by blast
          then show ?thesis using k trancl_trans by fast
        qed
      qed
    next
      case (eps q q' C)
      from eps(3) have "(q, q') \<in> (ta_eps cr_ta)\<^sup>*" unfolding C\<^sub>R_def by simp
      then have "(u, t) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+"
        using eps(1,2) by (auto simp: move.eps trancl.r_into_trancl)
      then have "(s, t) \<in> (move (ta_union cr_ta (TA {r. it_k n r})))\<^sup>+" using * by simp
      then show ?thesis by blast
    qed
  qed
qed

subsection \<open>in_k\<close>

(* A predicate which counts how often a specific ta_rule 'r' is used in a sequence. *)
inductive in_k :: "('b, 'a) ta \<Rightarrow> ('b, 'a) ta_rule \<Rightarrow> nat \<Rightarrow>
  ('a + 'b, 'c) term \<Rightarrow> ('a + 'b, 'c) term \<Rightarrow> bool"
for S r
where
  base: "(s, t) \<in> (move S)\<^sup>* \<Longrightarrow> in_k S r 0 s t"
| step: "in_k S r m s t \<Longrightarrow> (t, u) \<in> move (TA {r}) \<Longrightarrow> t \<noteq> u \<Longrightarrow> in_k S r k u v \<Longrightarrow>
  in_k S r (Suc (m + k)) s v"

lemma in_k_refl:
  shows "\<exists>m. in_k S r m s s"
using in_k.base by blast

lemma in_k_move:
  assumes "(s, u) \<in> (move S)\<^sup>*"
    and "in_k S r n u t"
  shows "in_k S r n s t"
using assms(2,1)
proof (induct)
  case (base u t)
  then have "(s, t) \<in> (move S)\<^sup>*" by auto
  then show ?case by (simp add: in_k.base)
qed (simp add: in_k.step)

lemma in_k_trans:
  assumes "in_k S r m s u"
    and "in_k S r n u t"
  shows "in_k S r (m + n) s t"
using assms
proof (induct)
  case (base s u)
  from in_k_move [OF this] show ?case by simp
next
  case (step k s v w l u)
  have "in_k S r (l + n) w t" using step by simp
  then have "in_k S r (Suc (k + (l + n))) s t" using step by (simp add: in_k.step)
  then show ?case by (simp add: add.assoc)
qed

lemma move_trancl_in_k_ex:
  assumes "(s, t) \<in> (move (ta_union S (TA {r})))\<^sup>+"
  shows "\<exists>m. in_k S r m s t"
using assms
proof (induct)
  case (base u)
  then have "(s, u) \<in> move (ta_union (TA {r}) S)" by simp
  then have "(s, u) \<in> move (TA {r}) \<or> (s, u) \<in> move S"
    using empty_ta_eps_move_union_iff [of "TA {r}" S] by auto
  then show ?case
  proof
    assume "(s, u) \<in> move S"
    then have "in_k S r 0 s u" by (simp add: in_k.base r_into_rtrancl) 
    then show ?thesis by auto
  next
    assume "(s, u) \<in> move (TA {r})"
    moreover obtain n m where "in_k S r m s s" and "in_k S r n u u" using in_k_refl by blast+
    ultimately show ?thesis by (cases "s = u") (auto intro: in_k.intros)
  qed
next
  case (step u t)
  then have "(u, t) \<in> move (ta_union (TA {r}) S)" by simp
  then have "(u, t) \<in> move (TA {r}) \<or> (u, t) \<in> move S"
    using empty_ta_eps_move_union_iff [of "TA {r}" S] by auto
  then show ?case
  proof
    assume "(u, t) \<in> move S"
    then have "in_k S r 0 u t" by (simp add: in_k.base r_into_rtrancl)
    moreover obtain n where "in_k S r n s u" using step(3) by blast
    ultimately show ?thesis using in_k_trans by fast
  next
    assume "(u, t) \<in> move (TA {r})"
    moreover obtain n where "in_k S r n s u" using step(3) by blast
    moreover obtain m where "in_k S r m t t" using in_k_refl by blast
    ultimately show ?thesis by (cases "u = t") (auto intro: in_k.intros)
  qed
qed

lemma in_k_Suc_ex:
  assumes "in_k S r (Suc m) s t"
  shows "\<exists>k u v l. (in_k S r k s u \<and> (u, v) \<in> move (TA {r}) \<and> u \<noteq> v \<and> in_k S r l v t) \<and> m = k + l"
using assms by (cases) (blast)

lemma in_kE:
  assumes "in_k S r m s t"
  shows "m = 0 \<or> (\<exists>u v. in_k S r 0 s u \<and> (u, v) \<in> move (TA {r}) \<and> u \<noteq> v \<and> in_k S r (m - 1) v t)"
using assms
proof (induct)
  case (step m s' t' u k v)
  moreover
  { assume "m = 0"
    then have ?case using step by auto
  }
  moreover
  { fix u' v'
    assume "in_k S r 0 s' u'"
      and "(u', v') \<in> move (TA {r})"
      and " u' \<noteq> v'"
      and "in_k S r (m - 1) v' t'"
    moreover then have "in_k S r ( Suc((m - 1) + k)) v' v" using step by (simp add: in_k.step)
    ultimately have ?case by (simp) (metis One_nat_def add_eq_if step(1,3,4,5))
  }
  ultimately show ?case by blast
qed (simp)

lemma in_k_SucE:
  assumes "in_k S r (Suc k) s t"
  shows "\<exists>u v. in_k S r 0 s u \<and> (u, v) \<in> move (TA {r}) \<and> u \<noteq> v \<and> in_k S r k v t"
using in_kE [OF assms] by auto

lemma in_kE2:
  assumes "in_k S r m s t"
  shows "(s, t) \<in> (move (ta_union S (TA {r})))\<^sup>*"
using assms
proof (induct)
  case (base s t)
  show ?case using move_mono'_rtrancl [OF base, of "ta_union S (TA {r})"] by (auto)
next
  case (step m s t u k v) 
  have "(t, u) \<in> move (ta_union S (TA {r}))" using move_mono' [OF step(3)] by (auto)
  then show ?case using step by fastforce
qed

lemma in_ancestors_of_State:
  assumes "(fterm s, State (star c t)) \<in> (move C\<^sub>R)\<^sup>+"
    and "t \<in> sr R" and "funas_term s \<subseteq> F"
    and "\<forall>q\<in>ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "s \<in> ancestors F R (ground_instances F t)"
proof -
  obtain k where "(fterm s, State (star c t)) \<in> (move (ta_union cr_ta (TA ({r. it_k k r}))))\<^sup>+"
    using cr_moves_imp_it_k_moves [OF assms(1)] by blast
  then show ?thesis using assms(2,3)
  proof (induct k arbitrary: s t)
    case (0)
    then have "(fterm s, State (star c t)) \<in> (move cr_ta)\<^sup>+"by (auto simp: move_mono'_trancl)
    then have "s \<in> ground_instances F t" using 0 cr_ta_ta_states_accept_ground_instances assms(4)
      by blast
    moreover then have "fground F s" unfolding ground_instances_def by blast
    ultimately show ?case unfolding ancestors_def by blast
  next
    case (Suc k)
    note IH\<^sub>0 = this(1)
    have "{r. it_k (Suc k) r} = ({r. it_k (Suc k) r} - {r. it_k k r}) \<union> {r. it_k k r}"
      (is "?\<Gamma>\<^sub>1 = ?\<Gamma>\<^sub>2 \<union> ?\<Gamma>\<^sub>3") by (auto simp: it_k_Suc_mono)
    let ?A\<^sub>1 = "ta_union cr_ta (TA ?\<Gamma>\<^sub>1)" and ?A\<^sub>2 = "ta_union cr_ta (ta_union (TA ?\<Gamma>\<^sub>2) (TA ?\<Gamma>\<^sub>3))"
    have "ta_rules ?A\<^sub>1 \<subseteq> ta_rules ?A\<^sub>2" and "ta_eps ?A\<^sub>1 \<subseteq> ta_eps ?A\<^sub>2" by auto
    then have 3: "(fterm s, State (star c t)) \<in> (move ?A\<^sub>2)\<^sup>+"
      using move_mono'_trancl [OF Suc(2)] by auto
    have "finite ?\<Gamma>\<^sub>2" using it_k_imp_\<Delta>\<^sub>C by (intro finite_subset [OF _ finite_\<Delta>\<^sub>C]) auto
    moreover have "?\<Gamma>\<^sub>2 \<subseteq> ?\<Gamma>\<^sub>2" ..
    ultimately show ?case using 3 Suc(3,4)
    proof (induct arbitrary: s t rule: finite_subset_induct')
      case (empty)
      then show ?case using IH\<^sub>0 by (auto simp: move_mono'_trancl)
    next
      case (insert r' \<Gamma>)
      note IH\<^sub>1 = this(5)
      let ?D = "TA (insert r' \<Gamma>)" and ?D\<^sub>1 = "TA \<Gamma>" and ?D\<^sub>2 = "TA {r'}" and ?G = "TA ?\<Gamma>\<^sub>3"
      let ?E = "ta_union cr_ta (ta_union ?D\<^sub>1 ?G)"
      have "?D = ta_union ?D\<^sub>1 ?D\<^sub>2" by auto
      then have *: "ta_union cr_ta (ta_union ?D ?G) = ta_union ?E ?D\<^sub>2" by simp
      have 1: "r' \<in> {r. it_k (Suc k) r}" and 2: "r' \<notin> ta_rules cr_ta"
        using Diff_iff [THEN iffD1, OF set_mp[OF insert(3)]] it_k_0 it_k_0_subseteq_it_k
        using insert(2) it_k.base by auto
      obtain f ls r \<theta> q' \<Delta>' where rule: "r' = TA_rule f (map (qi r \<theta>) ls) q'"
      and r'': "(Fun f ls, r) \<in> R"
      and range: "range \<theta> \<subseteq> ta_states cr_ta"
      and "q' \<in> ta_states cr_ta"
      and \<Delta>': "\<forall>r \<in> \<Delta>'. (\<exists>n \<le> k. it_k n r)"
      and seq: "(fterm r \<cdot> ((State \<circ> \<theta>) :: 'v \<Rightarrow> ('f, 'v) crterm), State q')
           \<in> (move (cr_ta\<lparr>ta_rules := \<Delta>'\<rparr>))\<^sup>*" using 1 2 by (auto elim: it_k.cases)
      let ?\<theta> = "(State \<circ> \<theta>) :: 'v \<Rightarrow> ('f, 'v) crterm"
      define \<Delta>\<^sub>k' where "\<Delta>\<^sub>k' \<equiv> (in_k ?E r') :: nat \<Rightarrow> ('f, 'v) crterm \<Rightarrow> ('f, 'v) crterm \<Rightarrow> bool"
      from insert(6) have "(fterm s, State (star c t)) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>+"
        by (simp add: *)
      from move_trancl_in_k_ex [OF this]
        obtain m where "\<Delta>\<^sub>k' m (fterm s) (State (star c t))" unfolding \<Delta>\<^sub>k'_def by blast
      then show ?case using insert(2,7,8)
      proof (induction m arbitrary: s t)
        case (0)
        then have "(fterm s, State (star c t)) \<in> (move ?E)\<^sup>*"
          by (auto simp: \<Delta>\<^sub>k'_def dest: in_k.cases)
        then have "(fterm s, State (star c t)) \<in> (move ?E)\<^sup>+"
          by (simp add: fterm_no_State rtrancl_eq_or_trancl)
        from IH\<^sub>1 [OF this] 0 show ?case by simp
      next
        case (Suc m')
        note IH\<^sub>2 = this(1) [OF _ Suc(3)]
        let ?s = "fterm s" and ?t = "State (star c t)"
        obtain qs q where r': "r' = TA_rule f qs q" using rule by auto
        from in_k_SucE [OF Suc(2) [unfolded \<Delta>\<^sub>k'_def]] obtain u v where 1: "\<Delta>\<^sub>k' 0 (fterm s) u"
          and uv: "(u, v) \<in> move (TA {r'})"
          and ne': "u \<noteq> v"
          and tail: "\<Delta>\<^sub>k' m' v ?t" unfolding \<Delta>\<^sub>k'_def by blast
        obtain C where u: "u = C\<langle>fqterm f qs\<rangle>"
          and v: "v = C\<langle>State q\<rangle>"
          and "(C\<langle>fqterm f qs\<rangle>, C\<langle>State q\<rangle>) \<in> move (TA {r'})"
          using uv ne' apply (cases rule: move.cases) using uv by (auto simp: r')
        from 1 have 2: "(?s, C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*" unfolding u \<Delta>\<^sub>k'_def by cases blast
        then obtain s' :: "('f, 'v) crterm" where s': "s' = ?s" and wf: "s' \<in> wf_terms"
          using fterm_in_wf_terms [of s] by blast
        have "(s', C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*" using 2 unfolding s' by blast
        from distr_moves'' [OF this wf] obtain D ss where s'': "s' = D\<langle>Fun (Inl f) ss\<rangle>"
          and l'': "length (map State qs) = length ss"
          and sqs: "\<forall>i < length ss. (ss ! i, map State qs ! i) \<in> (move ?E)\<^sup>*"
          and "(D\<langle>fqterm f qs\<rangle>, C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*"
          and mc: "(D, C) \<in> move_comp ?E" by force
        from move_comp_imp_moves [OF mc] have dc: "\<forall>t. (D\<langle>t\<rangle>, C\<langle>t\<rangle>) \<in> (move ?E)\<^sup>*" ..
        have len': "length ls = length ss" using l'' rule r' by auto
        have "fterm s = D\<langle>Fun (Inl f) ss\<rangle>" using s' s'' by auto
        then obtain ss' where 9: "ss = map fterm ss'"
          by (metis fterm_args_fterm map_funs_term_ctxt_decomp)
        have x: "fterm s = D\<langle>fterm (Fun f ss')\<rangle>" using s' s'' 9 by auto
        then obtain D' where 12: "D\<langle>fterm (Fun f ss')\<rangle> = (fctxt D')\<langle>fterm (Fun f ss')\<rangle>"
          and D': "D = fctxt D'" using map_funs_term_ctxt_decomp by blast
        then have y: "?s = (fterm D'\<langle>Fun f ss'\<rangle> :: ('f, 'v) crterm)" by (auto simp: x)
        have "inj fterm" using map_funs_term_inj[OF inj_Inl [of UNIV]] .
        from inj_onD [OF this y] have s: "s = D'\<langle>Fun f ss'\<rangle>" by auto
        { fix i
          assume i: "i < length ls"
          { assume "ls ! i \<in> Var ` vars_term r"
            moreover define \<tau> where "\<tau> = (\<lambda>y. if Var y = ls ! i then ss' ! i else Var y)"
            ultimately have "(ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
              \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i)" by force
          }
          moreover
          { assume a: "ls ! i \<notin> Var ` vars_term r"
            have "qs ! i = qi r \<theta> (ls ! i)" using i rule r' nth_map by auto
            also have "\<dots> = star c (ls ! i)" using a by (induct r \<theta> "ls ! i" rule: qi.induct) auto
            finally have "qs ! i = star c (ls ! i)" .
            then have "(fterm (ss' ! i), State (star c (ls ! i))) \<in> (move ?E)\<^sup>*"
              using sqs i l'' rule r' by (auto simp: 9)
            moreover have "fterm (ss' ! i) \<noteq> State (star c (ls ! i))" using fterm_no_State by fast
            ultimately have b: "(fterm (ss' ! i), State (star c (ls ! i))) \<in> (move ?E)\<^sup>+"
              by (auto simp: rtrancl_eq_or_trancl)
            have c: "ls ! i \<in> sr R" unfolding sr_def using i r'' nth_mem by blast
            have "i < length ss'" using i len' 9 by auto
            then have "(ss' ! i) \<unlhd> s" using s by (meson arg_subteq ctxt_supteq nth_mem supteq_trans) 
            then have d: "funas_term (ss' ! i) \<subseteq> F" using Suc by force
            from IH\<^sub>1 [OF b c d] have "ss' ! i \<in> ancestors F R (ground_instances F (ls ! i))" .
            then have "\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
              unfolding ground_instances_def ancestors_def by auto
          }
          ultimately have "\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
            \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i)" by blast
        }
        then have "\<forall>i < length ls. (\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
          \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i))" by blast
        then obtain \<tau>\<^sub>0 where 11: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> (\<tau>\<^sub>0 i)) \<in> (rstep R)\<^sup>*" 
          and 14: "\<forall>i < length ls. (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau>\<^sub>0 i y = ss' ! i)"
          by metis+
        have "is_partition (map vars_term ls)" using linear r'' by fastforce
        from subst_merge [OF this] obtain \<tau>\<^sub>l
          where 16: "\<forall>i < length ls. \<forall>x \<in> vars_term (ls ! i). \<tau>\<^sub>l x = \<tau>\<^sub>0 i x" by blast
        then have \<tau>\<^sub>l: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> \<tau>\<^sub>l) \<in> (rstep R)\<^sup>*"
          using 11 term_subst_eq by (metis (mono_tags, lifting))
        have 15: "\<forall>i < length ls. (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau>\<^sub>l y = ss' ! i)"
          using 14 16 by auto
        { fix x
          assume "x \<in> vars_term r - vars_term (Fun f ls)"
          from range have "\<theta> x \<in> ta_states cr_ta" by auto
          from ta_states_cr_ta_accessible [OF this, THEN accessible_ground_move_rtrancl]
            have "\<exists>u. ground (fterm u) \<and>
              (fterm u, (State (\<theta> x)) :: ('f, 'v) crterm) \<in> (move cr_ta)\<^sup>*"
            by auto
        }
        then obtain u where ux: "\<forall>x \<in> vars_term r - vars_term (Fun f ls).
          ground (fterm (u x))
          \<and> (fterm (u x), (State (\<theta> x)) :: ('f, 'v) crterm) \<in> (move cr_ta)\<^sup>*"
          by metis
        define \<tau>' where "\<tau>' = (\<lambda>y. if y \<in> vars_term r - vars_term (Fun f ls) then u y else Var y)"
        define \<tau> where "\<tau> = (\<lambda>y. if y \<in> vars_term r - vars_term (Fun f ls) then \<tau>' y else \<tau>\<^sub>l y)"
        have "\<forall>i < length ls. ls ! i \<cdot> \<tau> = ls ! i \<cdot> \<tau>\<^sub>l" by (auto simp: term_subst_eq_conv \<tau>_def)
        then have *: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" using \<tau>\<^sub>l by auto
        have l'': "length ss' = length (map (\<lambda>x. x \<cdot> \<tau>) ls)" using 9 len' by auto
        then have "\<forall>i < length ss'. (ss' ! i, (map (\<lambda>x. x \<cdot> \<tau>) ls) ! i) \<in> (rstep R)\<^sup>*" using *
          by auto
        from args_steps_imp_steps [OF ctxt_closed_rstep l'' this, of f] have
          "(s, D'\<langle>Fun f ls \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" by (simp add: rsteps_closed_ctxt s)
        moreover have "(D'\<langle>Fun f ls \<cdot> \<tau>\<rangle>, D'\<langle>r \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" using r'' by blast
        ultimately have r2: "(s, D'\<langle>r \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" by auto
        { fix x
          assume x: "x \<in> vars_term r"
          { assume x': "x \<in> vars_term (Fun f ls)"
            from vars_term_var_poss_iff [THEN iffD1, OF this] obtain p where
              p: "p \<in> var_poss (Fun f ls)" and p': "Var x = Fun f ls |_ p" by auto
            have p2: "p \<in> poss (Fun f ls)" using var_poss_imp_poss [OF p] .
            have p'': "p \<noteq> []" using p' by fastforce
            from bspec [OF growing [unfolded growing_def] r''] have
              "\<forall>x \<in> vars_term r. \<forall>p \<in> var_poss (Fun f ls). Var x = (Fun f ls) |_ p \<longrightarrow> size p \<le> 1"
              by auto
            from bspec [OF bspec [OF this x] p] p' have "size p \<le> 1" by blast
            then have "size p = 1" using p'' by (simp add: Suc_leI le_antisym)
            from Var_Fun_pos_size_One [OF p' p2 this] obtain i where i: "i < length ls"
              and x'': "ls ! i = Var x" by auto
            then have "Var x \<cdot> \<tau> = ls ! i \<cdot> \<tau>\<^sub>l" using \<tau>_def x x' by auto
            also have "\<dots> = ss' ! i" using 15 i x x'' by auto
            finally have 14: "Var x \<cdot> \<tau> = ss' ! i" .
            have "State (qs ! i) = State (qi r \<theta> (ls ! i))" using i rule r' nth_map by auto
            also have "\<dots> = State (\<theta> x)"
              unfolding x'' using x by (induct r \<theta> "Var x :: ('f ,'v) term" rule: qi.induct) auto
            also have "\<dots> = Var x \<cdot> ?\<theta>" by simp
            finally have "State (qs ! i) = Var x \<cdot> ?\<theta>" .
            then have 13: "qs ! i = \<theta> x" by auto
            have "(fterm (ss' ! i), State (qs ! i)) \<in> (move ?E)\<^sup>*"
              using sqs len' rule r' i by (auto simp: 9)
            then have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*"
              unfolding 13 14 [symmetric] by auto
          }
          moreover
          { assume x': "x \<notin> vars_term (Fun f ls)"
            then have "\<tau>' x = \<tau> x" using \<tau>'_def \<tau>_def x by auto
            moreover then have *: "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move cr_ta)\<^sup>*"
              by auto (metis DiffI \<tau>'_def ux x x')
            ultimately have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*"
              using x x' move_mono'_rtrancl [OF *] by (auto simp: \<tau>'_def)
          }
          ultimately have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*" by auto
        }
        then have "(fterm r \<cdot> (fterm \<circ> \<tau>), fterm r \<cdot> ?\<theta>) \<in> (move ?E)\<^sup>*"
          by (intro vars_move_imp_move) auto
        then have "(C\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>, C\<langle>fterm r \<cdot> ?\<theta>\<rangle>) \<in> (move ?E)\<^sup>*"
          using move_ctxt_rtrancl by blast
        moreover have "(D\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>, C\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>) \<in> (move ?E)\<^sup>*"
          using dc by auto
        moreover have "D\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle> = fterm D'\<langle>r \<cdot> \<tau>\<rangle>" using D'
          by (metis fterm_subst_distrib map_funs_term_ctxt_distrib)
        ultimately have x2: "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, C\<langle>fterm r \<cdot> ?\<theta>\<rangle>) \<in> (move ?E)\<^sup>*" by fastforce
        have q': "q = q'" using rule r' by simp
        have "?\<Gamma>\<^sub>1 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>2 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>3 \<subseteq> \<Delta>\<^sub>C" using it_k_imp_\<Delta>\<^sub>C by blast+
        then have "\<Gamma> \<subseteq> \<Delta>\<^sub>C" and "r' \<in> \<Delta>\<^sub>C" using insert(2,3) by blast+
        then have tt: "ta_rules (ta_union ?E ?D\<^sub>2) \<subseteq> ta_rules C\<^sub>R"
          by (auto simp: \<Delta>\<^sub>C.base it_k_imp_\<Delta>\<^sub>C C\<^sub>R_def)
        have s2: "(?s, ?t) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>*"
          using in_kE2 [OF Suc(2) [unfolded \<Delta>\<^sub>k'_def]] by blast
        have et: "ta_eps (ta_union ?E ?D\<^sub>2) \<subseteq> ta_eps C\<^sub>R" by (auto simp: C\<^sub>R_def)
        from move_mono'_rtrancl [OF s2 tt this] have "(?s, ?t) \<in> (move C\<^sub>R)\<^sup>*" .
        from fterm_State_funas_imp_ta_fground [OF this funas_ta_cr] have fgs: "fground F s" .
        have "\<Delta>' \<subseteq> ?\<Gamma>\<^sub>3" using \<Delta>' it_k_mono by blast
        from move_mono [OF this, of cr_ta] seq have
          "(fterm r \<cdot> ?\<theta>, State q') \<in> (move (cr_ta\<lparr>ta_rules := ?\<Gamma>\<^sub>3\<rparr>))\<^sup>*" by blast
        from move_mono'_rtrancl [OF this, of ?E] have
          "(fterm r \<cdot> ?\<theta>, State q') \<in> (move ?E)\<^sup>*" by (auto)
        then have "(C\<langle>fterm r \<cdot> ?\<theta>\<rangle>, C\<langle>State q'\<rangle>) \<in> (move ?E)\<^sup>*"
          using move_mono'_rtrancl [of _ _ ?E] move_ctxt_rtrancl by blast
        with x2 have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, C\<langle>State q'\<rangle>) \<in> (move ?E)\<^sup>*" by fastforce
        then have "\<Delta>\<^sub>k' 0 (fterm D'\<langle>r \<cdot> \<tau>\<rangle>) C\<langle>State q'\<rangle>" by (auto simp: \<Delta>\<^sub>k'_def intro: in_k.intros)
        with tail [unfolded v q'] have *: "\<Delta>\<^sub>k' m' (fterm D'\<langle>r \<cdot> \<tau>\<rangle>) ?t"
          using in_k_trans unfolding \<Delta>\<^sub>k'_def by fastforce
        from in_kE2 [OF this [unfolded \<Delta>\<^sub>k'_def]]
          have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, ?t) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>*" by (auto)
        from move_mono'_rtrancl [OF this tt et] have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, ?t) \<in> (move C\<^sub>R)\<^sup>*" .
        from fterm_State_funas_imp_ta_fground [OF this funas_ta_cr] have "fground F D'\<langle>r \<cdot> \<tau>\<rangle>" .
        then have "funas_term D'\<langle>r \<cdot> \<tau>\<rangle> \<subseteq> F" by blast
        from IH\<^sub>2 [OF * Suc(4) this] have "D'\<langle>r \<cdot> \<tau>\<rangle> \<in> ancestors F R (ground_instances F t)" .
        then obtain w where "(D'\<langle>r \<cdot> \<tau>\<rangle>, w) \<in> (rstep R)\<^sup>*" and "w \<in> ground_instances F t"
          and "fground F D'\<langle>r \<cdot> \<tau>\<rangle>" unfolding ancestors_def by blast
        moreover then have "(s, w) \<in> (rstep R)\<^sup>*" using r2 by simp
        ultimately show ?case using fgs ancestors_def by blast
      qed
    qed
  qed
qed

lemma in_ancestors_of_final_State:
  assumes "(fterm s, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>+"
    and "q\<^sub>f \<in> ta_final C\<^sub>R" and "funas_term s \<subseteq> F"
    and "\<forall>q\<in>ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "s \<in> ancestors F R (lang A)"
proof -
  obtain k where "(fterm s, State q\<^sub>f) \<in> (move (ta_union cr_ta (TA ({r. it_k k r}))))\<^sup>+"
    using cr_moves_imp_it_k_moves [OF assms(1)] by blast
  then show ?thesis using assms(2,3)
  proof (induct k arbitrary: s q\<^sub>f)
    case (0)
    then have "(fterm s, State q\<^sub>f) \<in> (move cr_ta)\<^sup>+" by (auto simp: move_mono'_trancl)
    then have 1: "(fterm s, State q\<^sub>f) \<in> (move cr_ta)\<^sup>*" by fast
    have 3: "fground F s" using fterm_State_funas_imp_ta_fground [OF 1 funas_ta_cr_ta] by simp
    from move_reachable_states [THEN iffD1, OF 1]
      have "q\<^sub>f \<in> reachable_states cr_ta (fterm s)" .
    then have "s \<in> lang cr_ta" using 0(2) 3 by (auto simp: lang_def C\<^sub>R_def)
    then have "s \<in> lang A" using lang_cr_ta [OF assms(4)] by auto
    from ancestors_refl [OF this 3, of R] show ?case .
  next
    case (Suc k)
    note IH\<^sub>0 = this(1)
    have *: "{r. it_k (Suc k) r} = ({r. it_k (Suc k) r} - {r. it_k k r}) \<union> {r. it_k k r}"
      (is "?\<Gamma>\<^sub>1 = ?\<Gamma>\<^sub>2 \<union> ?\<Gamma>\<^sub>3") by (auto simp: it_k_Suc_mono)
    let ?A\<^sub>1 = "ta_union cr_ta (TA ?\<Gamma>\<^sub>1)" and ?A\<^sub>2 = "ta_union cr_ta (ta_union (TA ?\<Gamma>\<^sub>2) (TA ?\<Gamma>\<^sub>3))"
    have "ta_rules ?A\<^sub>1 \<subseteq> ta_rules ?A\<^sub>2" by (auto)
    moreover have "ta_eps ?A\<^sub>1 \<subseteq> ta_eps ?A\<^sub>2" by (auto)
    ultimately have 3: "(fterm s, State q\<^sub>f) \<in> (move ?A\<^sub>2)\<^sup>+" using move_mono'_trancl Suc(2) by blast
    have "finite ?\<Gamma>\<^sub>2" using it_k_imp_\<Delta>\<^sub>C by (intro finite_subset [OF _ finite_\<Delta>\<^sub>C]) auto
    moreover have "?\<Gamma>\<^sub>2 \<subseteq> ?\<Gamma>\<^sub>2" ..
    ultimately show ?case using 3 Suc(3,4)
    proof (induct arbitrary: s q\<^sub>f rule: finite_subset_induct')
      case (empty)
      let ?D = "ta_union cr_ta (TA {r. it_k k r})"
      from move_mono'_trancl [OF empty(1)] have "(fterm s, State q\<^sub>f) \<in> (move ?D)\<^sup>+" by (auto)
      then show ?case using IH\<^sub>0 empty by blast
    next
      case (insert r' \<Gamma>)
      note IH\<^sub>1 = this(5)
      let ?D = "TA (insert r' \<Gamma>)" and ?D\<^sub>1 = "TA \<Gamma>" and ?D\<^sub>2 = "TA {r'}" and ?G = "TA ?\<Gamma>\<^sub>3"
      let ?E = "ta_union cr_ta (ta_union ?D\<^sub>1 ?G)"
      have "?\<Gamma>\<^sub>1 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>2 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>3 \<subseteq> \<Delta>\<^sub>C" using it_k_imp_\<Delta>\<^sub>C by blast+
      then have "\<Gamma> \<subseteq> \<Delta>\<^sub>C" and "r' \<in> \<Delta>\<^sub>C" using insert(2,3) by blast+
      have t1: "ta_rules ?E \<subseteq> ta_rules C\<^sub>R" and t2: "ta_rules (ta_union ?E ?D\<^sub>2) \<subseteq> ta_rules C\<^sub>R"
        by (auto simp: \<Delta>\<^sub>C.base \<open>r' \<in> \<Delta>\<^sub>C\<close> \<open>\<Gamma> \<subseteq> \<Delta>\<^sub>C\<close> it_k_imp_\<Delta>\<^sub>C C\<^sub>R_def)
      have e1: "ta_eps ?E \<subseteq> ta_eps C\<^sub>R" and e2: "ta_eps (ta_union ?E ?D\<^sub>2) \<subseteq> ta_eps C\<^sub>R"
        by (auto simp: C\<^sub>R_def)
      have *: "ta_union cr_ta (ta_union ?D ?G) = ta_union ?E ?D\<^sub>2" by simp
      have 1: "r' \<in> {r. it_k (Suc k) r}" and 2: "r' \<notin> ta_rules cr_ta"
        using Diff_iff [THEN iffD1, OF set_mp[OF insert(3)]] it_k_0 it_k_0_subseteq_it_k
        using insert(2) it_k.base by auto      
      obtain f ls r \<theta> q' \<Delta>' where rule: "r' = TA_rule f (map (qi r \<theta>) ls) q'"
      and r'': "(Fun f ls, r) \<in> R"
      and range: "range \<theta> \<subseteq> ta_states cr_ta"
      and "q' \<in> ta_states cr_ta"
      and \<Delta>': "\<forall>r \<in> \<Delta>'. (\<exists>n \<le> k. it_k n r)"
      and seq: "(fterm r \<cdot> ((State \<circ> \<theta>) :: 'v \<Rightarrow> ('f, 'v) crterm), State q')
           \<in> (move (cr_ta\<lparr>ta_rules := \<Delta>'\<rparr>))\<^sup>*" using 1 2 by (auto elim: it_k.cases)
      let ?\<theta> = "(State \<circ> \<theta>) :: 'v \<Rightarrow> ('f, 'v) crterm"
      define \<Delta>\<^sub>k' where "\<Delta>\<^sub>k' = ((in_k ?E r') :: nat \<Rightarrow> ('f, 'v) crterm \<Rightarrow> ('f, 'v) crterm \<Rightarrow> bool)"
      from insert(6) have "(fterm s, State q\<^sub>f) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>+" by (simp add: *)
      from move_trancl_in_k_ex [OF this]
        obtain m where "\<Delta>\<^sub>k' m (fterm s) (State q\<^sub>f)" unfolding \<Delta>\<^sub>k'_def by blast
      then show ?case using insert(2,7,8)
      proof (induction m arbitrary: s q\<^sub>f)
        case (0)
        then have "(fterm s, State q\<^sub>f) \<in> (move ?E)\<^sup>*"
          unfolding \<Delta>\<^sub>k'_def using in_k.simps by blast
        moreover have "fterm s \<noteq> State q\<^sub>f" using fterm_no_State by fast
        ultimately have "(fterm s, State q\<^sub>f) \<in> (move ?E)\<^sup>+"
          by (simp add: \<open>fterm s \<noteq> State q\<^sub>f\<close> rtrancl_eq_or_trancl)
        from IH\<^sub>1 [OF this 0(3,4)] show ?case .
      next
        case (Suc m')
        note IH\<^sub>2 = this(1) [OF _ Suc(3)]
        let ?s = "fterm s" and ?q\<^sub>f = "State q\<^sub>f"
        obtain qs q where r': "r' = TA_rule f qs q" using rule by auto
        from in_k_SucE [OF Suc(2) [unfolded \<Delta>\<^sub>k'_def]] obtain u v where 1: "\<Delta>\<^sub>k' 0 ?s u"
          and uv: "(u, v) \<in> move (TA {r'})"
          and ne': "u \<noteq> v"
          and tail: "\<Delta>\<^sub>k' m' v ?q\<^sub>f" unfolding \<Delta>\<^sub>k'_def by blast
        obtain C where u: "u = C\<langle>fqterm f qs\<rangle>"
          and v: "v = C\<langle>State q\<rangle>"
          and "(C\<langle>fqterm f qs\<rangle>, C\<langle>State q\<rangle>) \<in> move (TA {r'})"
          using uv ne' rule apply (cases rule: move.cases) using uv and r' by auto
        from 1 have 2: "(?s, C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*" unfolding u \<Delta>\<^sub>k'_def by cases blast
        then obtain s' :: "('f, 'v) crterm" where s': "s' = ?s"
          and wf: "s' \<in> wf_terms" using fterm_in_wf_terms [of s] by blast
        have "(s', C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*" using 2 unfolding s' by blast
        from distr_moves'' [OF this wf] obtain D ss where s'': "s' = D\<langle>Fun (Inl f) ss\<rangle>"
          and l'': "length (map State qs) = length ss"
          and sqs: "\<forall>i < length ss. (ss ! i, map State qs ! i) \<in> (move ?E)\<^sup>*"
          and "(D\<langle>fqterm f qs\<rangle>, C\<langle>fqterm f qs\<rangle>) \<in> (move ?E)\<^sup>*"
          and mc: "(D, C) \<in> move_comp ?E" by force
        from move_comp_imp_moves [OF mc] have dc: "\<forall>t. (D\<langle>t\<rangle>, C\<langle>t\<rangle>) \<in> (move ?E)\<^sup>*" ..
        have len': "length ls = length ss" using l'' rule r' by auto
        have "fterm s = D\<langle>Fun (Inl f) ss\<rangle>" using s' s'' by auto
        then obtain ss' where 9: "ss = map fterm ss'"
          by (metis fterm_args_fterm map_funs_term_ctxt_decomp)
        have x: "?s = D\<langle>fterm (Fun f ss')\<rangle>" using s' s'' 9 by auto
        then obtain D' where 12: "D\<langle>fterm (Fun f ss')\<rangle> = (fctxt D')\<langle>fterm (Fun f ss')\<rangle>"
          and D': "D = fctxt D'" using map_funs_term_ctxt_decomp by blast
        then have "D\<langle>fterm (Fun f ss')\<rangle> = (fterm D'\<langle>Fun f ss'\<rangle>)" by simp
        then have y: "?s = (fterm D'\<langle>Fun f ss'\<rangle> :: ('f, 'v) crterm)" unfolding x [symmetric] .
        have "inj fterm" using map_funs_term_inj [OF inj_Inl [of UNIV]] .
        from inj_onD [OF this y] have s: "s = D'\<langle>Fun f ss'\<rangle>" by auto
        { fix i
          assume i: "i < length ls"
          { assume "ls ! i \<in> Var ` vars_term r"
            moreover define \<tau> where "\<tau> = (\<lambda>y. if Var y = ls ! i then ss' ! i else Var y)"
            ultimately have "(ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
              \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i)" by force
          }
          moreover
          { assume a: "ls ! i \<notin> Var ` vars_term r"
            have "qs ! i = qi r \<theta> (ls ! i)" using i rule r' nth_map by auto
            also have "\<dots> = star c (ls ! i)" using a by (induct r \<theta> "ls ! i" rule: qi.induct) auto
            finally have "qs ! i = star c (ls ! i)" .
            then have "(fterm (ss' ! i), State (star c (ls ! i))) \<in> (move ?E)\<^sup>*"
              using sqs i l'' rule r' by (auto simp: 9)
            moreover have "fterm (ss' ! i) \<noteq> State (star c (ls ! i))" using fterm_no_State by fast
            ultimately have b: "(fterm (ss' ! i), State (star c (ls ! i))) \<in> (move ?E)\<^sup>+"
              by (auto simp: rtrancl_eq_or_trancl)
            have c: "ls ! i \<in> sr R" unfolding sr_def using i r'' nth_mem by blast
  
            have "i < length ss'" using i len' 9 by auto
            then have "(ss' ! i) \<unlhd> s" using s by (meson arg_subteq ctxt_supteq nth_mem supteq_trans) 
            then have d: "funas_term (ss' ! i) \<subseteq> F" using Suc by force
            from move_mono'_trancl [OF b t1 e1]
              have b': "(fterm (ss' ! i), State (star c (ls ! i))) \<in> (move C\<^sub>R)\<^sup>+" .
            from in_ancestors_of_State [OF b' c d assms(4)]
              have "ss' ! i \<in> ancestors F R (ground_instances F (ls ! i))" .
            then have "\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
              unfolding ground_instances_def ancestors_def by auto
          }
          ultimately have "\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
            \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i)" by blast
        }
        then have "\<forall>i < length ls. (\<exists>\<tau>. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*
          \<and> (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau> y = ss' ! i))" by blast
        then obtain \<tau>\<^sub>0 where 11: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> (\<tau>\<^sub>0 i)) \<in> (rstep R)\<^sup>*" 
          and 14: "\<forall>i < length ls. (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau>\<^sub>0 i y = ss' ! i)"
          by metis+
        have "is_partition (map vars_term ls)" using linear r'' by fastforce
        from subst_merge [OF this] obtain \<tau>\<^sub>l
          where 16: "\<forall>i < length ls. \<forall>x \<in> vars_term (ls ! i). \<tau>\<^sub>l x = \<tau>\<^sub>0 i x" by blast
        then have \<tau>\<^sub>l: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> \<tau>\<^sub>l) \<in> (rstep R)\<^sup>*"
          using 11 term_subst_eq by (metis (mono_tags, lifting))
        have 15: "\<forall>i < length ls. (\<forall>y. ls ! i \<in> Var ` vars_term r \<and> Var y = ls ! i \<longrightarrow> \<tau>\<^sub>l y = ss' ! i)"
          using 14 16 by auto
        { fix x
          assume "x \<in> vars_term r - vars_term (Fun f ls)"
          from range have "\<theta> x \<in> ta_states cr_ta" by auto
          from ta_states_cr_ta_accessible [OF this, THEN accessible_ground_move_rtrancl]
            have "\<exists>u. ground (fterm u) \<and>
              (fterm u, (State (\<theta> x)) :: ('f, 'v) crterm) \<in> (move cr_ta)\<^sup>*"
            by auto
        }
        then obtain u where ux: "\<forall>x \<in> vars_term r - vars_term (Fun f ls).
          ground (fterm (u x))
          \<and> (fterm (u x), (State (\<theta> x)) :: ('f, 'v) crterm) \<in> (move cr_ta)\<^sup>*"
          by metis
        define \<tau>' where "\<tau>' = (\<lambda>y. if y \<in> vars_term r - vars_term (Fun f ls) then u y else Var y)"
        define \<tau> where "\<tau> = (\<lambda>y. if y \<in> vars_term r - vars_term (Fun f ls) then \<tau>' y else \<tau>\<^sub>l y)"
        have "\<forall>i < length ls. ls ! i \<cdot> \<tau> = ls ! i \<cdot> \<tau>\<^sub>l" by (auto simp: term_subst_eq_conv \<tau>_def)
        then have *: "\<forall>i < length ls. (ss' ! i, ls ! i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" using \<tau>\<^sub>l by auto
        have l'': "length ss' = length (map (\<lambda>x. x \<cdot> \<tau>) ls)" using 9 len' by auto
        then have "\<forall>i < length ss'. (ss' ! i, (map (\<lambda>x. x \<cdot> \<tau>) ls) ! i) \<in> (rstep R)\<^sup>*" using *
          by auto
        from args_steps_imp_steps [OF ctxt_closed_rstep l'' this, of f] have
          "(s, D'\<langle>Fun f ls \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" by (simp add: rsteps_closed_ctxt s)
        moreover have "(D'\<langle>Fun f ls \<cdot> \<tau>\<rangle>, D'\<langle>r \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" using r'' by blast
        ultimately have r2: "(s, D'\<langle>r \<cdot> \<tau>\<rangle>) \<in> (rstep R)\<^sup>*" by auto
        { fix x
          assume x: "x \<in> vars_term r"
          { assume x': "x \<in> vars_term (Fun f ls)"
            from vars_term_var_poss_iff [THEN iffD1, OF this] obtain p where
              p: "p \<in> var_poss (Fun f ls)" and p': "Var x = Fun f ls |_ p" by auto
            have p2: "p \<in> poss (Fun f ls)" using var_poss_imp_poss [OF p] .
            have p'': "p \<noteq> []" using p' by fastforce
            from bspec [OF growing [unfolded growing_def] r''] have
              "\<forall>x \<in> vars_term r. \<forall>p \<in> var_poss (Fun f ls). Var x = (Fun f ls) |_ p \<longrightarrow> size p \<le> 1"
              by auto
            from bspec [OF bspec [OF this x] p] p' have
              "size p = 1" using p'' by (simp add: Suc_leI le_antisym)
            from Var_Fun_pos_size_One [OF p' p2 this] obtain i where i: "i < length ls"
              and x'': "ls ! i = Var x" by auto
            then have "Var x \<cdot> \<tau> = ls ! i \<cdot> \<tau>\<^sub>l" using \<tau>_def x x' by auto
            also have "\<dots> = ss' ! i" using 15 i x x'' by auto
            finally have 14: "Var x \<cdot> \<tau> = ss' ! i" .
            have "State (qs ! i) = State (qi r \<theta> (ls ! i))" using i rule r' nth_map by auto
            also have "\<dots> = State (\<theta> x)"
              unfolding x'' using x by (induct r \<theta> "Var x :: ('f ,'v) term" rule: qi.induct) auto
            also have "\<dots> = Var x \<cdot> ?\<theta>" by simp
            finally have "State (qs ! i) = Var x \<cdot> ?\<theta>" .
            then have 13: "qs ! i = \<theta> x" by auto
            have "(fterm (ss' ! i), State (qs ! i)) \<in> (move ?E)\<^sup>*"
              using sqs len' rule r' i by (auto simp: 9)
            then have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*"
              unfolding 13 14 [symmetric] by auto
          }
          moreover
          { assume x': "x \<notin> vars_term (Fun f ls)"
            then have "\<tau>' x = \<tau> x" using \<tau>'_def \<tau>_def x by auto
            moreover then have *: "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move cr_ta)\<^sup>*"
              by auto (metis DiffI \<tau>'_def ux x x')
            ultimately have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*"
              using x x' move_mono'_rtrancl [OF *] by (auto simp: \<tau>'_def)
          }
          ultimately have "((fterm \<circ> \<tau>) x, ?\<theta> x) \<in> (move ?E)\<^sup>*" by auto
        }
        then have "(fterm r \<cdot> (fterm \<circ> \<tau>), fterm r \<cdot> ?\<theta>) \<in> (move ?E)\<^sup>*"
          by (intro vars_move_imp_move) auto
        then have "(C\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>, C\<langle>fterm r \<cdot> ?\<theta>\<rangle>) \<in> (move ?E)\<^sup>*"
          using move_ctxt_rtrancl by blast
        moreover have w: "D\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle> = fterm D'\<langle>r \<cdot> \<tau>\<rangle>" using D'
          by (metis fterm_subst_distrib map_funs_term_ctxt_distrib)
        moreover have "(D\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>, C\<langle>fterm r \<cdot> (fterm \<circ> \<tau>)\<rangle>) \<in> (move ?E)\<^sup>*"
          using dc by auto
        ultimately have x2: "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, C\<langle>fterm r \<cdot> ?\<theta>\<rangle>) \<in> (move ?E)\<^sup>*" by fastforce
        have q': "q = q'" using rule r' by simp
        have "?\<Gamma>\<^sub>1 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>2 \<subseteq> \<Delta>\<^sub>C" and "?\<Gamma>\<^sub>3 \<subseteq> \<Delta>\<^sub>C" using it_k_imp_\<Delta>\<^sub>C by blast+
        then have "\<Gamma> \<subseteq> \<Delta>\<^sub>C" and "r' \<in> \<Delta>\<^sub>C" using insert(2,3) by blast+
        then have tt: "ta_rules (ta_union ?E ?D\<^sub>2) \<subseteq> ta_rules C\<^sub>R"
          by (auto simp: \<Delta>\<^sub>C.base it_k_imp_\<Delta>\<^sub>C C\<^sub>R_def)
        have s2: "(?s, ?q\<^sub>f) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>*"
          using in_kE2 [OF Suc(2) [unfolded \<Delta>\<^sub>k'_def]] by blast
        have et: "ta_eps (ta_union ?E ?D\<^sub>2) \<subseteq> ta_eps C\<^sub>R" by (auto simp: C\<^sub>R_def)
        from move_mono'_rtrancl [OF s2 tt this] have "(?s, ?q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" .
        from fterm_State_funas_imp_ta_fground [OF this funas_ta_cr] have fgs: "fground F s" .
        have "\<Delta>' \<subseteq> ?\<Gamma>\<^sub>3" using \<Delta>' it_k_mono by blast
        from move_mono [OF this, of cr_ta] seq have
          "(fterm r \<cdot> ?\<theta>, State q') \<in> (move (cr_ta\<lparr>ta_rules := ?\<Gamma>\<^sub>3\<rparr>))\<^sup>*" by blast
        from move_mono'_rtrancl [OF this, of ?E] have
          "(fterm r \<cdot> ?\<theta>, State q') \<in> (move ?E)\<^sup>*" by (auto)
        then have "(C\<langle>fterm r \<cdot> ?\<theta>\<rangle>, C\<langle>State q'\<rangle>) \<in> (move ?E)\<^sup>*" using move_ctxt_rtrancl by blast
        with x2 have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, C\<langle>State q'\<rangle>) \<in> (move ?E)\<^sup>*" by fastforce
        then have "\<Delta>\<^sub>k' 0 (fterm D'\<langle>r \<cdot> \<tau>\<rangle>) C\<langle>State q'\<rangle>" by (auto simp: \<Delta>\<^sub>k'_def intro: in_k.intros)
        with tail [unfolded v q'] have *: "\<Delta>\<^sub>k' m' (fterm D'\<langle>r \<cdot> \<tau>\<rangle>) (State q\<^sub>f)"
          using in_k_trans unfolding \<Delta>\<^sub>k'_def w by fastforce
        from in_kE2 [OF this [unfolded \<Delta>\<^sub>k'_def]]
          have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, ?q\<^sub>f) \<in> (move (ta_union ?E ?D\<^sub>2))\<^sup>*" by (auto)
        from move_mono'_rtrancl [OF this tt et] have "(fterm D'\<langle>r \<cdot> \<tau>\<rangle>, ?q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" .
        from fterm_State_funas_imp_ta_fground [OF this funas_ta_cr] have "fground F D'\<langle>r \<cdot> \<tau>\<rangle>" .
        then have "funas_term D'\<langle>r \<cdot> \<tau>\<rangle> \<subseteq> F" by blast
        from IH\<^sub>2 [OF * Suc(4) this] have "D'\<langle>r \<cdot> \<tau>\<rangle> \<in> ancestors F R (lang A)" .
        then obtain w where "(D'\<langle>r \<cdot> \<tau>\<rangle>, w) \<in> (rstep R)\<^sup>*" and "w \<in> lang A"
          and "fground F D'\<langle>r \<cdot> \<tau>\<rangle>" unfolding ancestors_def by blast
        moreover then have "(s, w) \<in> (rstep R)\<^sup>*" using r2 by simp
        ultimately show ?case using fgs ancestors_def by blast
      qed
    qed
  qed
qed

lemma etac_ancestors:
  assumes "\<forall>q \<in> ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
  shows "lang C\<^sub>R = ancestors F R (lang A)" (is "?L = ?R")
proof (intro equalityI subsetI)
  fix s
  assume "s \<in> ?L"
  from langE [OF this] obtain q\<^sub>f where 1: "(fterm s, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>*" and 2: "q\<^sub>f \<in> ta_final C\<^sub>R"
    by blast
  have "fground F s" using fterm_State_funas_imp_ta_fground [OF 1 funas_ta_cr] by simp
  then have 3: "funas_term s \<subseteq> F" by simp
  have 4: "(fterm s, State q\<^sub>f) \<in> (move C\<^sub>R)\<^sup>+" using 1
    by (simp add: fterm_no_State rtrancl_eq_or_trancl) 
  from in_ancestors_of_final_State [OF 4 2 3 assms] show "s \<in> ?R" .
next
  fix s
  assume "s \<in> ?R"
  then show "s \<in> ?L" using ancestors_subseteq_lang_cr [OF assms] by blast
qed

lemma State_move_in_ta_states:
  assumes "(fterm t, State q) \<in> move B" (is "(?t, ?q) \<in> _")
  shows "q \<in> ta_states B"
using assms
proof (induct ?t ?q rule: move.induct)
  case (trans f qs p C)
  then have "C = \<box>" by (metis Fun_Nil_supt ctxt_supt)
  then have "p = q" using trans by simp
  moreover have "p \<in> ta_states B" using trans by (auto simp: ta_states_def r_states_def)+
  ultimately show ?case by auto
next
  case (eps p p' C)
  with fterm_contains_no_Inr show ?case by metis
qed

lemma ground_instances_nonempty:
  assumes "funas_term t \<subseteq> F"
  shows "ground_instances F t \<noteq> {}"
proof (cases "ground t")
  case (True)
  with assms have "t \<in> ground_instances F t"
    apply (auto simp: ground_instances_def)
    apply (rule exI [of _ "\<lambda>x. Fun a []"])
    by (simp add: ground_subst_apply)
  then show ?thesis using assms by auto
next
  case (False)
  with assms nonempty show ?thesis
  apply (auto simp: ground_instances_def)
  apply (rule exI [of _ "\<lambda>x. Fun a []"])
  by (simp add: subst_sig_term_sig_imp)
qed

lemma ancestors_ground_instances_intersection_nonequal_terms:
  assumes "ancestors F R (ground_instances F t) \<inter> ground_instances F s = {}"
    and "funas_term t \<subseteq> F"
  shows "s \<noteq> t"
using assms(1) ground_instances_subseteq_ancestors_ground_instances [of F t R]
  ground_instances_nonempty [OF assms(2)] by (auto)

lemma ctxt_ta_states_term:
  fixes t :: "('f + ('f, 'v) term, 'v) term"
  assumes "t = C\<langle>State q\<rangle>"
  shows "q \<in> ta_states_term t"
using assms
proof (induct t arbitrary: C rule: ta_states_term.induct)
  case (1 p ts C)
  from 1(2) consider (More) us vs D where "C = More (Inr p) us D vs" and "ts \<noteq> []"
      | (Hole) "C = \<box>" and "p = q" and "ts = []"
      by (cases C) (auto)
  then show ?case
  proof (cases)
    case (Hole)
    then show ?thesis using 1 by fastforce
  next
    case (More)
    then have "ts = us @ D\<langle>State q\<rangle> # vs" using 1(2) by simp
    then obtain i where i: "ts ! i = D\<langle>State q\<rangle>" and i': "i < length ts"
      by (metis in_set_conv_decomp in_set_idx)
    from i' have "ts ! i \<in> set ts" by auto
    from 1(1) [OF this i] have "q \<in> ta_states_term (ts ! i)" .
    then show ?thesis using i' by fastforce
  qed
next
  case (2 f ts C)
  from 2(2) obtain us vs D where "C = More (Inl f) us D vs" and "ts \<noteq> []" by (cases C) auto
  then have "ts = us @ D\<langle>State q\<rangle> # vs" using 2(2) by simp
  then obtain i where i: "ts ! i = D\<langle>State q\<rangle>" and i': "i < length ts"
    by (metis in_set_conv_decomp in_set_idx)
  from i' have "ts ! i \<in> set ts" by auto
  from 2(1) [OF this i] have "q \<in> ta_states_term (ts ! i)" .
  then show ?case using i' by fastforce
next
  case (3 x)
  then show ?case using ctxt_supteq supteq_Var_id by fast
qed

fun ta_states_ctxt :: "('f + 'q, 'v) ctxt \<Rightarrow> 'q set" where
  "ta_states_ctxt Hole = {}"
| "ta_states_ctxt (More (Inr q) us D vs) = { q } \<union> ta_states_ctxt D \<union> \<Union>(ta_states_term ` set (us @ vs))"
| "ta_states_ctxt (More (Inl f) us D vs) = ta_states_ctxt D \<union> \<Union>(ta_states_term ` set (us @ vs))"

lemma ta_states_term_ctxt_apply_term [simp]:
  "ta_states_term (C\<langle>t\<rangle>) = ta_states_term t \<union> ta_states_ctxt C"
proof (induct C)
  case (More f ss D ts)
  then show ?case by (cases f) auto
qed simp

lemma ta_states_term_ta_states_ctxt_subseteq:
  assumes "ta_states_term t \<subseteq> X" and "ta_states_ctxt C \<subseteq> X"
  shows "ta_states_term C\<langle>t\<rangle> \<subseteq> X"
using assms by auto

lemma star_Fun_not_star:
  assumes "(f, n) \<in> F" and "n = length ts"
  shows "star c (Fun f ts) \<noteq> \<star>"
using assms fresh by auto

lemma TA_rule_star_in_sig_rules':
  assumes "TA_rule f qs \<star> \<in> ground_instances_rules F c u"
    and "(f, length qs) \<in> F"
  shows "TA_rule f qs \<star> \<in> sig_rules F \<star> \<and> qs = replicate (length qs) \<star>"
using assms(1)
proof (induct u)
  case (Var x)
  then show ?case by (auto simp: ground_instances_ta_def sig_rules_def)
next
  case (Fun g us)
  then consider "TA_rule f qs \<star> = TA_rule g (map (star c) us) (star c (Fun g us))"
    and "star c (Fun g us) = \<star>"
    | i where "TA_rule f qs \<star> \<in> ground_instances_rules F c (us ! i)" and "i < length us"
    by (force dest: in_set_idx simp: ground_instances_ta_def)
  then show ?case
  proof (cases)
    case (1)
    with assms(2) obtain n where "(f, n) \<in> F" and "n = length us" by auto
    from star_Fun_not_star [OF this] have "star c (Fun f us) \<noteq> \<star>" .
    moreover from 1 have "f = g" and "\<star> = star c (Fun g us)" by auto
    ultimately show ?thesis by auto
  next
    case (2)
    moreover from 2 have "TA_rule f qs \<star> \<in> ta_rules (TA (ground_instances_rules F c (us ! i)))"
      by (auto)
    moreover from 2 have "us ! i \<in> set us" by auto
    ultimately show ?thesis using Fun(1) by blast
  qed
qed

lemma TA_rule_star_in_sig_rules:
  assumes "TA_rule f qs \<star> \<in> ta_rules (\<A>\<^sub>\<Sigma> u)" and "(f, length qs) \<in> F"
  shows "TA_rule f qs \<star> \<in> sig_rules F \<star> \<and> qs = replicate (length qs) \<star>"
using assms(1)
proof (induct u)
  case (Var x)
  then show ?case by (auto simp: ground_instances_ta_def sig_rules_def)
next
  case (Fun g us)
  then consider "TA_rule f qs \<star> = TA_rule g (map (star c) us) (star c (Fun g us))"
    and "star c (Fun g us) = \<star>"
    | i where "TA_rule f qs \<star> \<in> ground_instances_rules F c (us ! i)" and "i < length us"
    by (force dest: in_set_idx simp: ground_instances_ta_def)
  then show ?case
  proof (cases)
    case (1)
    with assms(2) obtain n where "(f, n) \<in> F" and "n = length us" by auto
    from star_Fun_not_star [OF this] have "star c (Fun f us) \<noteq> \<star>" .
    moreover from 1 have "f = g" and "\<star> = star c (Fun g us)" by auto
    ultimately show ?thesis by auto
  next
    case (2)
    moreover from 2 have "TA_rule f qs \<star> \<in> ta_rules (\<A>\<^sub>\<Sigma> (us ! i))"
      by (auto simp: ground_instances_ta_def)
    moreover from 2 have "us ! i \<in> set us" by auto
    ultimately show ?thesis using Fun(1) by blast
  qed
qed

lemma star_sig_rules_ground_instances_ta:
  assumes "\<star> \<in> ta_states (\<A>\<^sub>\<Sigma> u)" and "funas_term u \<subseteq> F"
  shows "sig_rules F \<star> \<subseteq> ta_rules (\<A>\<^sub>\<Sigma> u)"
proof -
  from assms ta_states_ground_instances_ta' obtain s where s: "\<star> = star c s" and u: "u \<unrhd> s" by blast
  from assms(2) u have "funas_term s \<subseteq> F" by force
  then obtain x where "Var x = s" using s fresh by (induct s) (auto)
  then have "\<not> ground u" using u by fastforce
  with assms(2) show ?thesis
    using not_ground_sig_rules_subseteq_ground_instances_rules
    by (auto simp: ground_instances_ta_def)
qed

lemma star_sig_rules_mp_ta:
  assumes "\<star> \<in> ta_states mp_ta"
  shows "sig_rules F \<star> \<subseteq> ta_rules mp_ta"
proof -
  from assms ta_states_mp_ta obtain s l where s: "\<star> = star c s" and l1: "l \<in> lhss R"
    and l2: "l \<unrhd> s" by force
  have l3: "funas_term l \<subseteq> F" using rinf l1 by (force simp: funas_trs_def funas_rule_def)
  then have "funas_term s \<subseteq> F" using l2 by force
  then obtain x where "Var x = s" using s fresh by (induct s) (auto)
  then have "\<not> ground l" using l2 by fastforce
  with l3 have "sig_rules F \<star> \<subseteq> ta_rules (\<A>\<^sub>\<Sigma> l)"
    using not_ground_sig_rules_subseteq_ground_instances_rules
    by (auto simp: ground_instances_ta_def)
  then have "sig_rules F \<star> \<subseteq> ground_instances_rules F c l" by (auto simp: ground_instances_ta_def)
  then show ?thesis using l1 by (auto simp: mp_ta_def)
qed

lemma in_ground_instances_rulesD:
  "g qs \<rightarrow> Fun f (map (star c) ss) \<in> ground_instances_rules F c l \<Longrightarrow> (f, length ss) \<in> F \<Longrightarrow>
    g = f \<and> qs = map (star c) ss"
using fresh by (induct l) (auto simp: sig_rules_def)

lemma ta_states_ground_instances_ta_ta_rules:
  fixes ts :: "('f, 'v) term list"
  assumes "star c (Fun f ts) \<in> ta_states (\<A>\<^sub>\<Sigma> u)" and "(f, length ts) \<in> F"
    and "funas_term u \<subseteq> F"
  shows "TA_rule f (map (star c) ts) (star c (Fun f ts)) \<in> ta_rules (\<A>\<^sub>\<Sigma> u)"
proof -
  from assms ta_states_ground_instances_ta' [of u] obtain s where s: "star c s = star c (Fun f ts)"
    and l2: "u \<unrhd> s" by fastforce
  with assms(3) have "funas_term s \<subseteq> F" by force
  from assms(2) obtain n where n1: "(f, n) \<in> F" and n2: "n = length ts" by blast
  from s obtain ss where "Fun f ss = s" and ss: "map (star c) ss = map (star c) ts"
    using fresh star_Fun_not_star [OF n1 n2]  by (auto elim: star.elims)
  then have "star c (Fun f ss) \<in> ta_states (\<A>\<^sub>\<Sigma> u)" (is "?q \<in> _") using assms(1) s by presburger
  with accessible_ground_instances_ta [OF nonempty assms(3), of c] obtain t :: "('f, 'v) term"
    where "ground t"
    and r: "?q \<in> reachable_states (\<A>\<^sub>\<Sigma> u) (fterm t)" by (auto simp: accessible_def)
  show ?thesis
  proof (cases t)
    case (Var x)
    then show ?thesis using r by fastforce
  next
    case (Fun g us)
    let ?us = "map fterm us"
    from Fun r have "?q \<in> reachable_states (\<A>\<^sub>\<Sigma> u) (Fun (Inl g) ?us)" by force
    then obtain q qs where "TA_rule g qs q \<in> ta_rules (\<A>\<^sub>\<Sigma> u)"
      and "(q, ?q) \<in> (ta_eps (\<A>\<^sub>\<Sigma> u))\<^sup>*"
      and "length qs = length ?us"
      and "\<forall> i < length ?us. qs ! i \<in> reachable_states (\<A>\<^sub>\<Sigma> u) (?us ! i)"
      by auto
    then have *: "TA_rule g qs ?q \<in> ground_instances_rules F c u"
      by (auto simp: ground_instances_ta_def)
    then have "g = f \<and> qs = map (star c) ss"
      using n1 n2 ss by (auto simp: mp_ta_def dest: in_ground_instances_rulesD)
    then show ?thesis using * ss by (auto simp: ground_instances_ta_def)
  qed
qed

lemma ta_states_mp_ta_ta_rules:
  assumes "star c (Fun f ts) \<in> ta_states mp_ta" and "(f, length ts) \<in> F"
  shows "TA_rule f (map (star c) ts) (star c (Fun f ts)) \<in> ta_rules mp_ta"
proof -
  from assms ta_states_mp_ta obtain s l where s: "star c s = star c (Fun f ts)" and l1: "l \<in> lhss R"
    and l2: "l \<unrhd> s" by force
  have l3: "funas_term l \<subseteq> F" using rinf l1 by (force simp: funas_trs_def funas_rule_def)
  then have "funas_term s \<subseteq> F" using l2 by force
  from assms(2) obtain n where n1: "(f, n) \<in> F" and n2: "n = length ts" by blast
  from s obtain ss where "Fun f ss = s" and ss: "map (star c) ss = map (star c) ts"
    using fresh star_Fun_not_star [OF n1 n2] by (auto elim: star.elims)
  then have "star c (Fun f ss) \<in> ta_states mp_ta" (is "?q \<in> _") using assms(1) s by presburger
  from ta_states_mp_ta_accessible [OF this] obtain t :: "('f, 'v) term" where "ground t"
    and r: "?q \<in> reachable_states mp_ta (fterm t)" by (auto simp: accessible_def)
  show ?thesis
  proof (cases t)
    case (Var x)
    then show ?thesis using r by fastforce
  next
    case (Fun g us)
    let ?us = "map fterm us"
    from Fun r have "?q \<in> reachable_states mp_ta (Fun (Inl g) ?us)" by force
    then obtain q qs where "TA_rule g qs q \<in> ta_rules mp_ta"
      and "(q, ?q) \<in> (ta_eps mp_ta)\<^sup>*"
      and "length qs = length ?us"
      and "\<forall> i < length ?us. qs ! i \<in> reachable_states mp_ta (?us ! i)"
      by auto
    then have *: "TA_rule g qs ?q \<in> ta_rules mp_ta" by (auto simp: mp_ta_def)
    then have "g = f \<and> qs = map (star c) ss"
      using n1 n2 ss by (auto simp: mp_ta_def dest: in_ground_instances_rulesD)
    then show ?thesis using * ss by auto
  qed
qed

lemma ground_instances_ta_imp_mp_ta:
  fixes s t :: "('f, 'v) crterm"
  assumes "(s, t) \<in> (move (\<A>\<^sub>\<Sigma> u))" and "ta_states_term t \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta"
    and "funas_term u \<subseteq> F"
  shows "ta_states_term s \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta \<and> (s, t) \<in> (move mp_ta)"
    (is "_ \<subseteq> ?I \<and> _")
proof -
  from assms(3) have **: "funas_ta (\<A>\<^sub>\<Sigma> u) \<subseteq> F" by (auto simp: funas_ta_ground_instances_ta)
  have *: "ta_eps (\<A>\<^sub>\<Sigma> u) = {}" by auto
  consider (trans) f qs q C where "C\<langle>fqterm f qs\<rangle> = s" and "C\<langle>State q\<rangle> = t"
    and "TA_rule f qs q \<in> ta_rules (\<A>\<^sub>\<Sigma> u)"
    | (eps) q C where "C\<langle>State q\<rangle> = s" and "C\<langle>State q\<rangle> = t" and "(q, q) \<in> (ta_eps (\<A>\<^sub>\<Sigma> u))\<^sup>*"
    using assms(1) by (auto elim: move.cases)
  then show ?thesis
  proof (cases)
    case (trans)
    with assms have C: "ta_states_ctxt C \<subseteq> ?I" and "ta_states_term (State q) \<subseteq> ?I" by auto
    from trans(3) have "TA_rule f qs q \<in> ground_instances_rules F c u"
      by (auto simp: ground_instances_ta_def)
    with assms(3) have f: "(f, length qs) \<in> F" by (induct u) (auto simp: sig_rules_def)
    from trans(3) have qs: "set qs \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u)" by (auto simp: ta_states_def r_states_def)
    have m: "q \<in> ta_states mp_ta" and a: "q \<in> ta_states (\<A>\<^sub>\<Sigma> u)"
      using assms(2) ctxt_ta_states_term [OF trans(2) [symmetric]] by auto
    from m obtain v' l where "star c v' = q" and "l \<in> lhss R" and "l \<unrhd> v'" using ta_states_mp_ta
      by force
    consider (sig) "qs = replicate (length qs) \<star>" and "q = \<star>"
      | (non_sig) ts where "qs = map (star c) ts" and "q = star c (Fun f ts)" and "u \<unrhd> Fun f ts"
      using trans(3) by (induct u) (auto simp: ground_instances_ta_def sig_rules_def)
    then show ?thesis
    proof (cases)
      case (sig)
      from star_sig_rules_mp_ta [OF m [unfolded sig(2)]]
        have "sig_rules F \<star> \<subseteq> ta_rules mp_ta" .
      moreover from trans(3) [unfolded sig(2)] and f and TA_rule_star_in_sig_rules
        have "TA_rule f qs \<star> \<in> sig_rules F \<star>" by blast
      ultimately have 1: "TA_rule f qs q \<in> ta_rules mp_ta" by (auto simp: sig(2))
      then have "set qs \<subseteq> ta_states mp_ta" by (auto simp: ta_states_def r_states_def)
      with qs have "ta_states_term (fqterm f qs) \<subseteq> ?I" by auto
      then have "ta_states_term s \<subseteq> ?I" using C unfolding trans(1) [symmetric] by auto
      moreover from trans(1,2) 1 have "(s, t) \<in> move mp_ta" by (auto intro: move.intros)
      ultimately show ?thesis by auto
    next
      case (non_sig)
      then have f': "(f, length ts) \<in> F" using f by fastforce
      from non_sig m have "star c (Fun f ts) \<in> ta_states mp_ta" by blast
      from ta_states_mp_ta_ta_rules [OF this f']
        have 1: "TA_rule f qs q \<in> ta_rules mp_ta" using non_sig by auto
      then have "set qs \<subseteq> ta_states mp_ta" by (auto simp: ta_states_def r_states_def)
      with qs have "ta_states_term (fqterm f qs) \<subseteq> ?I" by auto
      then have "ta_states_term s \<subseteq> ?I" using C unfolding trans(1) [symmetric] by auto
      moreover from trans(1,2) 1 have "(s, t) \<in> move mp_ta" by (auto intro: move.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (eps)
    with assms have 1: "ta_states_term s \<subseteq> ?I" by auto
    from eps have "(q, q) \<in> (ta_eps mp_ta)\<^sup>*" by blast
    then have "(s, t) \<in> move mp_ta" using eps(1,2) by (auto intro: move.intros)
    then show ?thesis using 1 by auto
  qed
qed

lemma ground_instances_ta_imp_mp_ta':
  fixes s t :: "('f, 'v) crterm"
  assumes "(s, t) \<in> (move (\<A>\<^sub>\<Sigma> u))\<^sup>*" and "ta_states_term t \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta"
    and "funas_term u \<subseteq> F"
  shows "(s, t) \<in> (move mp_ta)\<^sup>*"
using assms by (induct) (auto dest: ground_instances_ta_imp_mp_ta)

lemma mp_ta_imp_ground_instances_ta:
  fixes s t :: "('f, 'v) crterm"
  assumes "(s, t) \<in> (move mp_ta)" and "ta_states_term t \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta"
    and "funas_term u \<subseteq> F"
  shows "ta_states_term s \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta \<and> (s, t) \<in> (move (\<A>\<^sub>\<Sigma> u))"
    (is "_ \<subseteq> ?I \<and> _")
proof -
  from assms(3) have **: "funas_ta (\<A>\<^sub>\<Sigma> u) \<subseteq> F" by (auto simp: funas_ta_ground_instances_ta)
  have *: "ta_eps mp_ta = {}" by (auto simp: mp_ta_def)
  consider (trans) f qs q C where "C\<langle>fqterm f qs\<rangle> = s" and "C\<langle>State q\<rangle> = t"
    and "TA_rule f qs q \<in> ta_rules mp_ta"
    | (eps) q C where "C\<langle>State q\<rangle> = s" and "C\<langle>State q\<rangle> = t" and "(q, q) \<in> (ta_eps mp_ta)\<^sup>*"
    using assms(1) by (auto elim: move.cases simp: mp_ta_def)
  then show ?thesis
  proof (cases)
    case (trans)
    with assms have C: "ta_states_ctxt C \<subseteq> ?I" and "ta_states_term (State q) \<subseteq> ?I" by auto
    from trans(3) obtain l where l: "l \<in> lhss R"
      and r: "TA_rule f qs q \<in> ground_instances_rules F c l"
      by (auto simp: mp_ta_def)
    from rinf l have "funas_term l \<subseteq> F" by (force simp: funas_trs_def funas_rule_def)
    with r have f: "(f, length qs) \<in> F" by (induct l) (auto simp: sig_rules_def)
    from trans(3) have qs: "set qs \<subseteq> ta_states mp_ta" by (auto simp: ta_states_def r_states_def)
    have m: "q \<in> ta_states mp_ta" and a: "q \<in> ta_states (\<A>\<^sub>\<Sigma> u)"
      using assms(2) ctxt_ta_states_term [OF trans(2) [symmetric]] by auto
    consider (sig) "qs = replicate (length qs) \<star>" and "q = \<star>"
      | (non_sig) ts where "qs = map (star c) ts" and "q = star c (Fun f ts)" and "l \<unrhd> Fun f ts"
      using r by (induct l) (auto simp: sig_rules_def)
    then show ?thesis
    proof (cases)
      case (sig)
      from star_sig_rules_ground_instances_ta [OF a [unfolded sig(2)] assms(3)]
        have "sig_rules F \<star> \<subseteq> ta_rules (\<A>\<^sub>\<Sigma> u)" .
      moreover from r [unfolded sig(2)] and f and TA_rule_star_in_sig_rules'
        have "TA_rule f qs \<star> \<in> sig_rules F \<star>" by blast
      ultimately have 1: "TA_rule f qs q \<in> ta_rules (\<A>\<^sub>\<Sigma> u)" by (auto simp: sig(2))
      then have "set qs \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u)" by (auto simp: ta_states_def r_states_def)
      with qs have "ta_states_term (fqterm f qs) \<subseteq> ?I" by auto
      then have "ta_states_term s \<subseteq> ?I" using C unfolding trans(1) [symmetric] by auto
      moreover from trans(1,2) 1 have "(s, t) \<in> move (\<A>\<^sub>\<Sigma> u)" by (auto intro: move.intros)
      ultimately show ?thesis by auto
    next
      case (non_sig)
      then have f': "(f, length ts) \<in> F" using f by fastforce
      from non_sig a have "star c (Fun f ts) \<in> ta_states (\<A>\<^sub>\<Sigma> u)" by blast
      from ta_states_ground_instances_ta_ta_rules [OF this f' assms(3)]
        have 1: "TA_rule f qs q \<in> ta_rules (\<A>\<^sub>\<Sigma> u)" using non_sig by auto
      then have "set qs \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u)" by (auto simp: ta_states_def r_states_def)
      with qs have "ta_states_term (fqterm f qs) \<subseteq> ?I" by auto
      then have "ta_states_term s \<subseteq> ?I" using C unfolding trans(1) [symmetric] by auto
      moreover from trans(1,2) 1 have "(s, t) \<in> move (\<A>\<^sub>\<Sigma> u)" by (auto intro: move.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (eps)
    with assms have 1: "ta_states_term s \<subseteq> ?I" by auto
    from eps have "(q, q) \<in> (ta_eps (\<A>\<^sub>\<Sigma> u))\<^sup>*" by blast
    then have "(s, t) \<in> move (\<A>\<^sub>\<Sigma> u)" using eps(1,2) by (auto intro: move.intros)
    then show ?thesis using 1 by auto
  qed
qed

lemma mp_ta_imp_ground_instances_ta':
  fixes s t :: "('f, 'v) crterm"
  assumes "(s, t) \<in> (move mp_ta)\<^sup>*" and "ta_states_term t \<subseteq> ta_states (\<A>\<^sub>\<Sigma> u) \<inter> ta_states mp_ta"
    and "funas_term u \<subseteq> F"
  shows "(s, t) \<in> (move (\<A>\<^sub>\<Sigma> u))\<^sup>*"
using assms by (induct) (auto dest: mp_ta_imp_ground_instances_ta)

lemma ta_states_intersection_reachable_from_same_terms:
  assumes "q \<in> ta_states (\<A>\<^sub>\<Sigma> s) \<inter> ta_states mp_ta" and "funas_term s \<subseteq> F"
  shows "sterms TYPE('v) (\<A>\<^sub>\<Sigma> s) q = sterms TYPE('v) mp_ta q" (is "?A = ?B")
proof -
  from assms have *: "ta_states_term (state TYPE('v) q) \<subseteq> ta_states (\<A>\<^sub>\<Sigma> s) \<inter> ta_states mp_ta" by auto
  then obtain t u where "star c t = q" and "t \<in> sr R" and "star c u = q" and "u \<unlhd> s"
    by (auto simp: ta_states_mp_ta_sr ta_states_ground_instances_ta')
  { fix v
    have "(v, state TYPE('v) q) \<in> (move (\<A>\<^sub>\<Sigma> s))\<^sup>* \<longleftrightarrow> (v, state TYPE('v) q) \<in> (move mp_ta)\<^sup>*"
      using mp_ta_imp_ground_instances_ta' [OF _ * assms(2)]
      and ground_instances_ta_imp_mp_ta' [OF _ * assms(2)]
      by (auto)
  }
  then show ?thesis by blast
qed

lemma etac_nonreachable:
  fixes s t :: "('f, 'v) term"
  assumes "funas_term s \<subseteq> F"
    and t: "ground_instances F t \<subseteq> lang A"
    and comp: "\<forall>q\<in>ta_states A \<inter> ta_states mp_ta. sterms TYPE('v) A q = sterms TYPE('v) mp_ta q"
    and empty: "lang (\<A>\<^sub>\<Sigma> s) \<inter> lang C\<^sub>R = ({}::('f, 'v) term set)"
  shows "\<not> (\<exists>\<sigma> \<tau>. fground F (s \<cdot> \<sigma>) \<and> fground F (t \<cdot> \<tau>) \<and> (s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*)"
proof -
  note [simp] = etac_ancestors [OF comp]

  have "ground_instances F s \<subseteq> lang (ground_instances_ta F c s)"
    using \<open>funas_term s \<subseteq> F\<close> by (intro ground_instances_subseteq_lang_ground_instances_ta)
  then have *: "ancestors F R (ground_instances F t) \<inter> ground_instances F s = {}"
    using empty and ancestors_lang_mono [OF t, of F R] by auto
  show ?thesis (is "\<not> (\<exists>\<sigma> \<tau>. ?P \<sigma> \<tau>)")
  proof
    assume "\<exists>\<sigma> \<tau>. ?P \<sigma> \<tau>"
    then obtain \<sigma> \<tau> where "?P \<sigma> \<tau>" by blast
    then have "s \<cdot> \<sigma> \<in> ancestors F R (ground_instances F t)"
      and "s \<cdot> \<sigma> \<in> ground_instances F s" by (auto simp: ancestors_def ground_instances_def)
    with * show False by blast
  qed
qed

end

end
