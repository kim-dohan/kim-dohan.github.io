(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Tree_Automata 
imports
  Certification_Monads.Check_Monad
  First_Order_Rewriting.Multihole_Context
  Auxx.Util
begin

subsection \<open>Basic definitions and Lemmas\<close>

datatype ('q, 'f) ta_rule = TA_rule (r_root: 'f) (r_lhs_states: "'q list") (r_rhs: 'q) ("_ _ \<rightarrow> _" [51, 51, 51] 52)

lemma infinite_ta_rule_UNIV[simp, intro]: "infinite (UNIV :: ('q,'f)ta_rule set)"
proof -
  fix f :: 'f                                          
  fix q :: 'q
  let ?map = "\<lambda> n. (f (replicate n q) \<rightarrow> q)"
  have "inj ?map" unfolding inj_on_def by auto
  from infinite_super[OF _ range_inj_infinite[OF this]]
  show ?thesis by blast
qed

record ('q, 'f) ta = 
  ta_final :: "'q set"
  ta_rules :: "('q,'f) ta_rule set"
  ta_eps   :: "('q \<times> 'q)set"

(* use prefix r for rule *)
fun r_sym where "r_sym (f qs \<rightarrow> q) = (f, length qs)"
definition r_states where "r_states \<equiv> \<lambda> ta_rule. insert (r_rhs ta_rule) (set (r_lhs_states ta_rule))"

definition ta_states :: "('q,'f)ta \<Rightarrow> 'q set" where 
  "ta_states TA \<equiv> \<Union> (r_states ` ta_rules TA) \<union> \<Union> ((\<lambda> (q,q'). {q,q'}) ` ta_eps TA) \<union> ta_final TA"

definition ta_rhs_states :: "('q,'f)ta \<Rightarrow> 'q set"
where "ta_rhs_states TA \<equiv> {q'. \<exists> q. (q \<in> r_rhs ` ta_rules TA) \<and> (q,q') \<in> (ta_eps TA)^*}"

lemma r_rhs_states:
  assumes "f qs \<rightarrow> q \<in> ta_rules TA"
    shows "q \<in> ta_states TA"
using assms unfolding ta_states_def r_states_def by fastforce

lemma ta_rhs_states_subset_states: "ta_rhs_states TA \<subseteq> ta_states TA"
proof
  fix q
  assume "q \<in> ta_rhs_states TA" 
  from this[unfolded ta_rhs_states_def]
  obtain q' where q': "q' \<in> r_rhs ` ta_rules TA" and qq': "(q', q) \<in> (ta_eps TA)\<^sup>*" by blast
  from q' have q': "q' \<in> ta_states TA" unfolding ta_states_def by (auto simp: r_states_def)
  from qq' have "q' = q \<or> (\<exists> q''. (q'', q) \<in> ta_eps TA)" by (metis rtranclE)
  then show "q \<in> ta_states TA" using q' unfolding ta_states_def by blast
qed

definition ta_syms :: "('q,'f)ta \<Rightarrow> 'f sig"
where "ta_syms TA \<equiv> r_sym ` ta_rules TA"

lemma finite_ta_syms: assumes "finite (ta_rules TA)" shows "finite (ta_syms TA)"
  unfolding ta_syms_def using assms by auto

definition ta_diff :: "(_,_)ta \<Rightarrow> _" where
  "ta_diff TA rs = \<lparr>ta_final = ta_final TA, ta_rules = ta_rules TA - rs, ta_eps = ta_eps TA\<rparr>"

lemma ta_diff_simps[simp]:
  "ta_diff TA {} = TA"
  "ta_eps (ta_diff TA rs) = ta_eps TA"
  "ta_final (ta_diff TA rsi) = ta_final TA"
  "ta_rhs_states (ta_diff TA (ta_rules TA)) = {}"
by (auto simp: ta_diff_def ta_rhs_states_def)

lemma ta_diff_rules: "ta_rules (ta_diff TA rs) = ta_rules TA - rs" by (simp add: ta_diff_def)

(* the reachable states of some term: ta_res, variables in terms encode states *)
fun ta_res :: "('q,'f)ta \<Rightarrow> ('f,'q)term \<Rightarrow> 'q set"
where "ta_res TA (Var q) = {q'. (q,q') \<in> (ta_eps TA)^*}"
  | "ta_res TA (Fun f ts) = {q' | q' q qs. 
    (f qs \<rightarrow> q) \<in> ta_rules TA \<and> 
    (q,q') \<in> ((ta_eps TA)^*) \<and> 
    length qs = length ts \<and> 
    (\<forall> i < length ts. qs ! i \<in> (map (ta_res TA) ts) ! i)}"

(* we require a function which adapts the type of variables of a term,
   so that states of the automaton and variables in the term language can be
   chosen independently *)
definition adapt_vars :: "('f,'q)term \<Rightarrow> ('f,'v)term" where 
  [code del]: "adapt_vars \<equiv> map_vars_term (\<lambda>_. undefined)"

lemma adapt_vars2:
  "adapt_vars (adapt_vars t) = adapt_vars t"
  by (induct t) (auto simp add: adapt_vars_def)

lemma adapt_vars_simps[code, simp]: "adapt_vars (Fun f ts) = Fun f (map adapt_vars ts)"
  by (induct ts, auto simp: adapt_vars_def)

lemma adapt_vars_reverse: "ground t \<Longrightarrow> adapt_vars t' = t \<Longrightarrow> adapt_vars t = t'"
  unfolding adapt_vars_def 
proof (induct t arbitrary: t')
  case (Fun f ts)
  then show ?case by (cases t') (auto simp add: map_vars_term_as_subst map_idI)
qed auto

lemma ground_adapt_vars[simp]: "ground (adapt_vars t) = ground t" by (simp add: adapt_vars_def)
lemma funas_term_adapt_vars[simp]: "funas_term (adapt_vars t) = funas_term t" by (simp add: adapt_vars_def)

lemma adapt_vars_adapt_vars[simp]: fixes t :: "('f,'v)term"
  assumes g: "ground t"
  shows "adapt_vars (adapt_vars t :: ('f,'w)term) = t"
proof -
  let ?t' = "adapt_vars t :: ('f,'w)term"
  have gt': "ground ?t'" using g by auto
  from adapt_vars_reverse[OF gt', of t] show ?thesis by blast
qed

definition adapt_vars_ctxt :: "('f,'q)ctxt \<Rightarrow> ('f,'v)ctxt" where
  [code del]: "adapt_vars_ctxt = map_vars_ctxt (\<lambda>_. undefined)"

lemma adapt_vars_ctxt_simps[simp, code]: 
  "adapt_vars_ctxt (More f bef C aft) = More f (map adapt_vars bef) (adapt_vars_ctxt C) (map adapt_vars aft)"
  "adapt_vars_ctxt Hole = Hole" unfolding adapt_vars_ctxt_def adapt_vars_def by auto

lemma adapt_vars_ctxt[simp]: "adapt_vars (C \<langle> t \<rangle> ) = (adapt_vars_ctxt C) \<langle> adapt_vars t \<rangle>"
  by (induct C, auto)

lemma adapt_vars_subst[simp]: "adapt_vars (l \<cdot> \<sigma>) = l \<cdot> (\<lambda> x. adapt_vars (\<sigma> x))"
  unfolding adapt_vars_def by simp


(* the language of an automaton *)
definition ta_lang :: "('q,'f)ta \<Rightarrow> ('f,'v)terms" where 
  [code del]: "ta_lang TA = {adapt_vars t | t. ground t \<and> ta_final TA \<inter> ta_res TA t \<noteq> {}}"

lemma ta_langE: assumes "t \<in> ta_lang TA"
  obtains t' q where "ground t'" "q \<in> ta_final TA" "q \<in> ta_res TA t'" "t = adapt_vars t'"
  using assms unfolding ta_lang_def by blast

lemma ta_lang_def2: "(ta_lang (TA :: ('q,'f)ta) :: ('f,'v)terms) = {t. ground t \<and> ta_final TA \<inter> ta_res TA (adapt_vars t) \<noteq> {}}" (is "?l = ?r")
proof -
  note d = ta_lang_def
  {
    fix t
    assume "t \<in> ?l"
    from ta_langE[OF this] obtain t' q where *: "ground t'" "q \<in> ta_final TA" "q \<in> ta_res TA t'" and id: "t = adapt_vars t'" . 
    from *(1) id have "ground t" by (metis ground_adapt_vars)
    with arg_cong[OF id, of "adapt_vars :: ('f,'v)term \<Rightarrow> ('f,'q)term"] *(1)
    have t': "t' = adapt_vars t" by auto
    have "t \<in> ?r" unfolding id using t' * by auto
  }
  moreover
  {
    fix t
    assume "t \<in> ?r" 
    then obtain q where *: "ground t" "q \<in> ta_final TA" "q \<in> ta_res TA (adapt_vars t)" by auto
    from * have id: "t \<in> ?l \<longleftrightarrow> adapt_vars (adapt_vars t :: ('f,'q)term) \<in> ?l"
      by auto
    have "t \<in> ?l" unfolding id unfolding d
      by (rule, intro exI conjI, rule refl, insert *, auto)
  }
  ultimately show ?thesis by blast
qed

lemma ta_langE2: fixes TA :: "('q,'f)ta" 
  assumes ass: "(t :: ('f,'v)term) \<in> ta_lang TA"
  obtains q where "ground t" "q \<in> ta_final TA" "q \<in> ta_res TA (adapt_vars t)"
  using ass[unfolded ta_lang_def2] by blast

lemma ta_langE3: fixes TA :: "('q,'f)ta" 
  assumes ass: "(adapt_vars t :: ('f,'v)term) \<in> ta_lang TA"
  obtains q where "ground t" "q \<in> ta_final TA" "q \<in> ta_res TA t" 
  using ta_langE2[OF ass] by auto

lemma ta_langI: assumes "ground t'" "q \<in> ta_final TA" "q \<in> ta_res TA t'" "t = adapt_vars t'"
  shows "t \<in> ta_lang TA"
  using assms unfolding ta_lang_def by blast

lemma ta_langI2: assumes *: "ground t" "q \<in> ta_final TA" "q \<in> ta_res TA (adapt_vars t)" 
  shows "t \<in> ta_lang TA" unfolding ta_lang_def2 using assms by blast

(* deterministic TA: no epsilon rules, no overlapping rules *)
definition ta_det :: "('q,'f)ta \<Rightarrow> bool" where
  "ta_det TA \<equiv> ta_eps TA = {} \<and> 
    (\<forall> f qs q q'. (f qs \<rightarrow> q) \<in> ta_rules TA \<longrightarrow> (f qs \<rightarrow> q') \<in> ta_rules TA \<longrightarrow> q = q')"

(* determinism implies unique results *)
lemma ta_detE[elim, consumes 1]: assumes det: "ta_det TA"
  shows "q \<in> ta_res TA t \<Longrightarrow> q' \<in> ta_res TA t \<Longrightarrow> q = q'"
proof -
  note det = det[unfolded ta_det_def]
  from det have [simp]: "ta_eps TA = {}" by simp
  show "q \<in> ta_res TA t \<Longrightarrow> q' \<in> ta_res TA t \<Longrightarrow> q = q'"
  proof (induct t arbitrary: q q')
    case (Var x q q')
    then show ?case by simp
  next
    case (Fun f ts q1 q2)
    from Fun(2)
    obtain qs1 where rule1: "(f qs1 \<rightarrow> q1) \<in> ta_rules TA"
      and len1: "length qs1 = length ts"
      and rec1: "\<And> i. i < length ts \<Longrightarrow> qs1 ! i \<in> ta_res TA (ts ! i)" by auto
    from Fun(3)
      obtain qs2 where rule2: "(f qs2 \<rightarrow> q2) \<in> ta_rules TA"
      and len2: "length qs2 = length ts"
      and rec2: "\<And> i. i < length ts \<Longrightarrow> qs2 ! i \<in> ta_res TA (ts ! i)" by auto
    {
      fix i
      assume i: "i < length ts"
      then have mem: "ts ! i \<in> set ts" by auto
      from Fun(1)[OF this rec1 rec2] have "qs1 ! i = qs2 ! i" using i by auto
    }
    with len1 have "qs1 = qs2" unfolding len2[symmetric] unfolding list_eq_iff_nth_eq by auto
    with rule2 have rule2: "(f qs1 \<rightarrow> q2) \<in> ta_rules TA" by auto
    from rule1 rule2 det show "q1 = q2" by auto
  qed
qed

(* we can always add epsilon transitions at the end *)
lemma ta_res_eps: assumes q: "q \<in> ta_res TA t" and q': "(q,q') \<in> (ta_eps TA)^*"
  shows "q' \<in> ta_res TA t"
  using q
proof (induct t)
  case (Var q'')
  from this[simplified] q' 
  show ?case by simp
next
  case (Fun f ts)
  from Fun(2)
  obtain q'' qs where rule: "(f qs \<rightarrow> q'') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)"
    and q: "(q'',q) \<in> (ta_eps TA)^*"
    by auto
  from q q' have q': "(q'',q') \<in> (ta_eps TA)^*" by auto
  with rule len rec show ?case by auto
qed

(* a resulting state is always some rhs of a rule (or epsilon transition) *)
lemma ta_rhs_states_res: assumes "is_Fun t" 
  shows "ta_res TA t \<subseteq> ta_rhs_states TA"
proof
  fix q 
  assume q: "q \<in> ta_res TA t"
  from \<open>is_Fun t\<close> obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from q[unfolded t] obtain q' qs where "(f qs \<rightarrow> q') \<in> ta_rules TA" 
    and q: "(q',q) \<in> (ta_eps TA)^*" by auto
  then show "q \<in> ta_rhs_states TA" unfolding ta_rhs_states_def by fastforce
qed

lemma ta_res_states: assumes "ground t"
  shows "ta_res TA t \<subseteq> ta_states TA" 
proof -
  from assms have "is_Fun t" by (cases t, auto)
  from subset_trans[OF ta_rhs_states_res[OF this] ta_rhs_states_subset_states, of TA]
  show ?thesis .
qed

lemma ta_res_vars_states:
  assumes res: "q \<in> ta_res TA t"
      and q: "q \<in> ta_states TA"
  shows "vars_term t \<subseteq> ta_states TA"
using assms proof (induction t arbitrary: q)
  case (Var x)
    then show ?case by (simp) (cases rule: converse_rtranclE, auto simp: ta_states_def) next
  case (Fun f ts)
    from this obtain qs p where rule: "f qs \<rightarrow> p \<in> ta_rules TA" "length ts = length qs"
      and res: "\<And>i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" by auto
    {
      fix i assume i: "i < length ts"
      with rule have "qs ! i \<in> ta_states TA" by (fastforce simp: ta_states_def r_states_def)
      with res i have "vars_term (ts ! i) \<subseteq> ta_states TA" by (intro Fun.IH) auto
    }
    then show ?case by (auto simp: set_conv_nth)
qed

(* only terms can be reduced to a state, if all symbols appear in the automaton *)
lemma ta_syms_res: "q \<in> ta_res TA t \<Longrightarrow> funas_term t \<subseteq> ta_syms TA"
proof (induct t arbitrary: q)
  case (Var x)
  show ?case by simp
next
  case (Fun f ts)
  from Fun(2)
  obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<forall> i < length ts. qs ! i \<in> ta_res TA (ts ! i)"
    by auto
  {
    fix t 
    assume mem: "t \<in> set ts"
    then obtain i where i: "i < length ts"
      and t: "t = ts ! i" unfolding set_conv_nth by auto
    from Fun(1)[OF mem[unfolded t] rec[THEN spec, THEN mp[OF _ i]]]
    have "funas_term t \<subseteq> ta_syms TA" unfolding t by auto
  } note rec = this
  from rule len have f: "(f,length ts) \<in> ta_syms TA" unfolding ta_syms_def
    by force
  show ?case using f rec by auto
qed

(* only terms can be accepted, if all symbols appear in the automaton *)
lemma ta_syms_lang: assumes "t \<in> ta_lang TA" shows "funas_term t \<subseteq> ta_syms TA"
proof -
  from ta_langE[OF assms]
  obtain q t' where "q \<in> ta_res TA t'" "t = adapt_vars t'" .
  from ta_syms_res[OF this(1)] this(2) show ?thesis by auto
qed

definition "ta_subset TA TA' \<equiv> ta_final TA \<subseteq> ta_final TA' \<and> ta_rules TA \<subseteq> ta_rules TA' \<and> ta_eps TA \<subseteq> ta_eps TA'"

lemma ta_diff_subset_simp[simp]:
  "ta_subset (ta_diff TA rs) TA"
by (auto simp: ta_subset_def ta_diff_def)

lemma ta_res_mono': assumes eps: "ta_eps TA \<subseteq> ta_eps TA'" and rules: "ta_rules TA \<subseteq> ta_rules TA'"
  shows "ta_res TA t \<subseteq> ta_res TA' t"
proof -
  note eps = rtrancl_mono[OF eps]
  show ?thesis
  proof (induct t)
    case (Fun f ts)
    show ?case 
    proof
      fix q 
      assume "q \<in> ta_res TA (Fun f ts)"
      from this[simplified] obtain qa qs where
        rule: "(f qs \<rightarrow> qa) \<in> ta_rules TA \<and> (qa, q) \<in> (ta_eps TA)\<^sup>*"  
        and len: "length qs = length ts" 
        and steps: "\<And> i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" by auto
      with eps rules have 
        rule: "(f qs \<rightarrow> qa) \<in> ta_rules TA' \<and> (qa, q) \<in> (ta_eps TA')\<^sup>*" by auto
      {
        fix i
        assume "i < length ts"
        with Fun[unfolded set_conv_nth, of "ts ! i"] steps[OF this]
        have "qs ! i \<in> ta_res TA' (ts ! i)" by auto
      }
      with rule len show "q \<in> ta_res TA' (Fun f ts)" by auto
    qed
  qed (insert eps, auto)
qed

lemma ta_res_mono: assumes "ta_subset TA TA'"
  shows "ta_res TA t \<subseteq> ta_res TA' t"
  using assms[unfolded ta_subset_def] ta_res_mono' by auto

lemma ta_lang_mono: assumes "ta_subset TA TA'"
  shows "ta_lang TA \<subseteq> ta_lang TA'"
  using ta_res_mono[OF assms] assms[unfolded ta_subset_def] unfolding ta_lang_def 
  by blast

(* the restriction of an automata to a given set of states *)
definition ta_restrict where 
  "ta_restrict TA Q = \<lparr> ta_final = ta_final TA \<inter> Q, 
    ta_rules = { r. r \<in> ta_rules TA \<and> r_states r \<subseteq> Q },
    ta_eps = ta_eps TA \<inter> (Q \<times> Q)
    \<rparr>"

lemma ta_restrict_subset: "ta_subset (ta_restrict TA Q) TA"
  unfolding ta_subset_def ta_restrict_def Let_def by auto

lemma ta_restrict_states_Q: "ta_states (ta_restrict TA Q) \<subseteq> Q"
  unfolding ta_states_def ta_restrict_def Let_def by auto

lemma ta_restrict_states: "ta_states (ta_restrict TA Q) \<subseteq> ta_states TA"
  unfolding ta_states_def ta_restrict_def Let_def by auto


lemma ta_subset_refl[simp]: "ta_subset TA TA" 
  unfolding ta_subset_def by auto

lemma ta_subset_trans: "ta_subset TA TA' \<Longrightarrow> ta_subset TA' TA'' \<Longrightarrow> ta_subset TA TA''"
  unfolding ta_subset_def by auto

lemma ta_subset_ta_states: "ta_subset TA TA' \<Longrightarrow> ta_states TA \<subseteq> ta_states TA'" 
  unfolding ta_subset_def ta_states_def by blast

lemma ta_restrict_states_eq_imp_eq: assumes eq: "ta_states (ta_restrict TA Q) = ta_states TA"
  shows "ta_restrict TA Q = TA"
  by (cases TA, insert assms, unfold ta_restrict_def ta_states_def, auto)

lemma ta_subset_det: "ta_subset TA TA' \<Longrightarrow> ta_det TA' \<Longrightarrow> ta_det TA"
  unfolding ta_det_def ta_subset_def by blast

(* composing filling of contexts *)
lemma ta_res_ctxt: assumes p: "p \<in> ta_res TA t"
  shows "q \<in> ta_res TA (C \<langle> Var p \<rangle>) \<Longrightarrow> q \<in> ta_res TA (C \<langle> t \<rangle>)"
proof (induct C arbitrary: q)
  case Hole
  then show ?case using p ta_res_eps by auto
next
  case (More f bef C aft)
  let ?n = "length bef"
  let ?m = "Suc (?n + length aft)"
  from More(2)
  obtain q' qs where 
    rule: "(f qs \<rightarrow> q') \<in> ta_rules TA" and
    eps: "(q', q) \<in> (ta_eps TA)\<^sup>*" and
    len: "length qs = ?m" and
    rec: "\<And> i. i < ?m \<Longrightarrow> qs ! i \<in> (map (ta_res TA) bef @ ta_res TA C\<langle>Var p\<rangle> # map (ta_res TA) aft) ! i" 
    by auto
  from rec[of ?n] len have "qs ! ?n \<in> ta_res TA (C \<langle> Var p \<rangle>)" by (simp add: nth_append)
  from More(1)[OF this] have IH: "qs ! ?n \<in> ta_res TA C\<langle>t\<rangle>" .
  show ?case 
  proof (simp, intro exI conjI, rule rule, rule eps, rule len, clarify)
    fix i
    assume "i < ?m"
    from rec[OF this] IH
    show "qs ! i \<in> (map (ta_res TA) bef @ ta_res TA C\<langle>t\<rangle> # map (ta_res TA) aft) ! i"
      by (cases "i = ?n", auto simp: nth_append)
  qed
qed

subsection \<open>Reachable and productive states: There always is a trim automaton\<close>

definition ta_reachable :: "('q,'f)ta \<Rightarrow> 'q set" where
  "ta_reachable TA \<equiv> {q. \<exists> t. ground t \<and> q \<in> ta_res TA t}"

lemma ta_reachableE: assumes "q \<in> ta_reachable TA"
  obtains t where "ground t" "q \<in> ta_res TA t"
  using assms[unfolded ta_reachable_def] by auto

lemma ta_reachableI_rule: assumes sub: "set qs \<subseteq> ta_reachable TA" and 
  rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
  shows "q \<in> ta_reachable TA"
proof -
  {
    fix i
    assume i: "i < length qs"
    then have "qs ! i \<in> set qs" by auto
    with sub have "qs ! i \<in> ta_reachable TA" by auto
    from ta_reachableE[OF this] have "\<exists> t. ground t \<and> qs ! i \<in> ta_res TA t" by auto
  }
  then have "\<forall> i. \<exists> t. i < length qs \<longrightarrow> ground t \<and> qs ! i \<in> ta_res TA t" by auto
  from choice[OF this] obtain ts where ts: "\<And> i. i < length qs \<Longrightarrow> ground (ts i) \<and> qs ! i \<in> ta_res TA (ts i)" by blast
  let ?t = "Fun f (map ts [0 ..< length qs])"
  have gt: "ground ?t" using ts by auto
  have "q \<in> ta_res TA ?t" unfolding ta_res.simps
    by (rule, intro exI conjI, rule refl, rule rule, insert ts, auto)
  with gt show ?thesis unfolding ta_reachable_def by blast
qed

lemma ta_reachableI_eps': assumes reach: "q \<in> ta_reachable TA" and 
  eps: "(q,q') \<in> (ta_eps TA)^*"  
  shows "q' \<in> ta_reachable TA"
proof -
  from ta_reachableE[OF reach] obtain t where g: "ground t" and res: "q \<in> ta_res TA t" by auto
  from ta_res_eps[OF res eps] g show ?thesis unfolding ta_reachable_def by auto
qed

lemma ta_reachableI_eps: assumes reach: "q \<in> ta_reachable TA" and 
  eps: "(q,q') \<in> ta_eps TA"  
  shows "q' \<in> ta_reachable TA"
  by (rule ta_reachableI_eps'[OF reach], insert eps, auto)

definition ta_productive :: "('q,'f)ta \<Rightarrow> 'q set" where
  "ta_productive TA \<equiv> {q . \<exists> q' C. q' \<in> ta_res TA (C\<langle>Var q\<rangle>) \<and> q' \<in> ta_final TA}"

lemma ta_productiveE: assumes "q \<in> ta_productive TA"
  obtains q' C where "q' \<in> ta_res TA (C\<langle>Var q\<rangle>)" "q' \<in> ta_final TA" 
  using assms[unfolded ta_productive_def] by auto

lemma ta_productiveI: 
  assumes "q' \<in> ta_res TA (C\<langle>Var q\<rangle>)" "q' \<in> ta_final TA" 
  shows "q \<in> ta_productive TA"
  using assms unfolding ta_productive_def by auto

(* Definition 6 in paper *)
definition ta_trim :: "('q,'f)ta \<Rightarrow> bool" where 
  "ta_trim TA \<equiv> \<forall> q \<in> ta_states TA. q \<in> ta_reachable TA \<and> q \<in> ta_productive TA"


abbreviation ta_only_reach :: "('q,'f)ta \<Rightarrow> ('q,'f)ta" where
  "ta_only_reach TA \<equiv> ta_restrict TA (ta_reachable TA)"

lemma ta_reachable_empty_rules[simp]:
assumes "ta_rules TA = {}"
  shows "ta_reachable TA = {}"
proof(rule equals0I)
  fix q
  assume "q \<in> ta_reachable TA"
  from ta_reachableE[OF this] obtain t where "ground t" "q \<in> ta_res TA t" by auto
  from this obtain r where "r \<in> ta_rules TA" by (cases t) auto
  then show False using assms by auto
qed

lemma ta_reachable_mono:
assumes "ta_subset TA TA'"
  shows "ta_reachable TA \<subseteq> ta_reachable TA'"
proof
  fix q
  assume "q \<in> ta_reachable TA"
  from ta_reachableE[OF this] obtain t where ground: "ground t" and "q \<in> ta_res TA t" by auto
  with ta_res_mono[OF assms] have "q \<in> ta_res TA' t" by auto
  with ground show "q \<in> ta_reachable TA'" unfolding ta_reachable_def by auto
qed

lemma ta_reachabe_rhs_states:
  shows "ta_reachable TA \<subseteq> ta_rhs_states TA"
proof
  fix p assume "p \<in> ta_reachable TA"
  from ta_reachableE[OF this] obtain t where "ground t" and res: "p \<in> ta_res TA t" by auto
  then have "is_Fun t" by auto
  from res ta_rhs_states_res[OF this] show "p \<in> ta_rhs_states TA" by auto
qed

lemma ta_reachable_eps: assumes Q: "Q = ta_reachable TA"
  and q: "q \<in> Q" shows "(q,q') \<in> (ta_eps TA)^* \<Longrightarrow> q' \<in> Q \<and> (q,q') \<in> (ta_eps TA \<inter> Q \<times> Q)^*"
proof (induct rule: rtrancl_induct)
  case (step q' q'')
  from q[unfolded Q] have "q \<in> ta_reachable TA" by auto
  from ta_reachableE[OF this] obtain t where gt: "ground t" and qt: "q \<in> ta_res TA t" by auto
  let ?rel = "(ta_eps TA \<inter> Q \<times> Q)"
  from step(1-2) have "(q,q'') \<in> (ta_eps TA)^*" by auto
  from ta_res_eps[OF qt this] gt have "q'' \<in> ta_reachable TA" unfolding ta_reachable_def by auto
  with step(2) have q'': "q'' \<in> Q" unfolding Q ta_states_def by auto
  with step(2-3) have "(q,q') \<in> ?rel^*" "(q',q'') \<in> ?rel" by auto
  then have "(q,q'') \<in> ?rel^*" by (rule rtrancl_into_rtrancl)
  with q'' show ?case by simp
qed (insert q, auto)

(* major lemma to show that one can restrict to reachable states *)
lemma ta_res_only_reach: assumes Q: "Q = ta_reachable TA"
  shows "vars_term t \<subseteq> Q \<Longrightarrow> q \<in> ta_res TA t \<Longrightarrow> q \<in> Q \<and> q \<in> ta_res (ta_only_reach TA) t"
proof (induct t arbitrary: q)
  case (Var q q')
  from Var(2) have qq': "(q,q') \<in> (ta_eps TA)^*" by simp
  from Var(1) have q: "q \<in> Q" by simp
  from ta_reachable_eps[OF Q q qq'] show ?case unfolding ta_restrict_def Let_def Q by simp
next
  case (Fun f ts)
  let ?TA = "ta_only_reach TA"
  from Fun(3)[simplified] obtain qa qs where
        rule: "(f qs \<rightarrow> qa) \<in> ta_rules TA" and eps: "(qa, q) \<in> (ta_eps TA)\<^sup>*"  
        and len: "length qs = length ts" 
        and steps: "\<And> i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" by auto
  {
    fix i
    assume i: "i < length ts"
    then have mem: "ts ! i \<in> set ts" by auto
    with Fun(2) have "vars_term (ts ! i) \<subseteq> Q" by auto
    from Fun(1)[OF mem this steps[OF i]]
    have qi: "qs ! i \<in> Q" and qti: "qs ! i \<in> ta_res ?TA (ts ! i)" by auto
    note qti qi
  } note IH = this
  from IH(2)[folded len] have qs: "set qs \<subseteq> ta_reachable TA" unfolding Q set_conv_nth by auto
  from ta_reachableI_rule[OF this rule] qs rule 
  have qa: "qa \<in> Q" and "r_states (f qs \<rightarrow> qa) \<subseteq> Q" unfolding r_states_def Q by auto
  with rule have rule: "(f qs \<rightarrow> qa) \<in> ta_rules ?TA" unfolding ta_restrict_def Let_def Q by auto
  from ta_reachable_eps[OF Q qa eps] have q: "q \<in> Q" and eps: "(qa, q) \<in> (ta_eps ?TA)\<^sup>*" 
    unfolding ta_restrict_def Let_def Q by auto
  have "q \<in> ta_res ?TA (Fun f ts)"
    by (simp, intro exI conjI, rule rule, rule eps, insert len IH(1), auto)
  with q show ?case by auto
qed  

lemma ta_only_reach_reachable: "ta_states (ta_only_reach TA) \<subseteq> ta_reachable (ta_only_reach TA)"
proof
  let ?TA = "ta_only_reach TA"
  fix q
  assume "q \<in> ta_states ?TA"
  from set_mp[OF ta_restrict_states_Q this] have "q \<in> ta_reachable TA" .
  from ta_reachableE[OF this] obtain t where
    tq: "q \<in> ta_res TA t" and gt: "ground t" by auto
  from ta_res_only_reach[OF refl _ tq] gt[unfolded ground_vars_term_empty] have "q \<in> ta_res ?TA t" by auto
  then show "q \<in> ta_reachable ?TA" unfolding ta_reachable_def using gt by auto
qed


(* It is sound to restrict to reachable states. *)
lemma ta_only_reach_lang: "ta_lang (ta_only_reach TA) = ta_lang TA" (is "ta_lang ?TA = _")
proof
  show "ta_lang ?TA \<subseteq> ta_lang TA" by (rule ta_lang_mono[OF ta_restrict_subset])
  show "ta_lang TA \<subseteq> ta_lang ?TA" 
  proof
    fix t
    assume "t \<in> ta_lang TA"
    from ta_langE2[OF this] obtain q where gt: "ground t" and f: "q \<in> ta_final TA" 
    and q: "q \<in> ta_res TA (adapt_vars t)" .
    have *: "q \<in> ta_reachable TA \<and> q \<in> ta_res ?TA (adapt_vars t)"
      by (rule ta_res_only_reach[OF refl _ q], insert gt, induct t, auto)
    show "t \<in> ta_lang ?TA"
      by (rule ta_langI2[OF gt, of q], insert * f, auto simp: ta_restrict_def)
  qed
qed

abbreviation ta_only_prod :: "('q,'f)ta \<Rightarrow> ('q,'f)ta" where
  "ta_only_prod TA \<equiv> ta_restrict TA (ta_productive TA)"

lemma ta_only_prod_eps: assumes "(q,q') \<in> (ta_eps TA)^*" and "q' \<in> ta_productive TA"
  shows "q \<in> ta_productive TA \<and> (q,q') \<in> (ta_eps (ta_only_prod TA))^*"
  using assms
proof (induct)
  case (step q1 q2)
  from ta_productiveE[OF step(4)] obtain p'' C where 
   other: "p'' \<in> ta_res TA C\<langle>Var q2\<rangle>" "p'' \<in> ta_final TA" by auto
  from step(2) have "q2 \<in> ta_res TA (Var q1)" by auto
  from ta_productiveI[OF ta_res_ctxt[OF this other(1)] other(2)]
  have q1: "q1 \<in> ta_productive TA" .
  from step(3)[OF q1] have q: "q \<in> ta_productive TA" and qq1: "(q, q1) \<in> (ta_eps (ta_only_prod TA))\<^sup>*" by blast+
  from q1 step(2,4) have "(q1,q2) \<in> ta_eps (ta_only_prod TA)" unfolding ta_restrict_def by auto
  with qq1 have "(q,q2) \<in> (ta_eps (ta_only_prod TA))\<^sup>*" by auto
  with q show ?case by simp
qed simp

(* Major lemma to show that it is sound to restrict to productive states. *)
lemma ta_res_only_prod: 
  shows "q \<in> ta_res TA t \<Longrightarrow> q \<in> ta_productive TA \<Longrightarrow> q \<in> ta_res (ta_only_prod TA) t"
proof (induct t arbitrary: q)
  case (Var q' q)
  let ?TA = "ta_only_prod TA"
  from Var have "(q',q) \<in> (ta_eps TA)^*" and "q \<in> ta_productive TA" by auto
  from ta_only_prod_eps[OF this] show ?case by simp
next
  case (Fun f ts)
  let ?TA = "ta_only_prod TA"
  from Fun(2) obtain qa qs where
        rule: "(f qs \<rightarrow> qa) \<in> ta_rules TA" and eps: "(qa, q) \<in> (ta_eps TA)\<^sup>*"  
        and len: "length qs = length ts" 
        and steps: "\<And> i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" by auto
  from Fun(3) have q: "q \<in> ta_productive TA" .
  from ta_productiveE[OF q] obtain q'' C where qq'': "q'' \<in> ta_res TA (C \<langle>Var q\<rangle>)" and q'': "q'' \<in> ta_final TA"
    by blast
  {
    fix i
    assume i: "i < length ts"
    then have [simp]: "Suc (i + (length ts - Suc i)) = length ts" "min (length ts) i = i" by arith+
    let ?D = "C \<circ>\<^sub>c More f (take i ts) \<box> (drop (Suc i) ts)"
    have id: "(C \<circ>\<^sub>c More f (take i ts) \<box> (drop (Suc i) ts))\<langle>Var (qs ! i)\<rangle> = C\<langle>Fun f (take i ts @ Var (qs ! i) # drop (Suc i) ts)\<rangle>" by simp 
    have [simp]: "qs ! i \<in> ta_res TA (Var (qs ! i))" by auto
    note ta_res.simps(1)[simp del]
    have qsi: "(qs ! i) \<in> ta_productive TA "
    proof (rule ta_productiveI[OF _ q'', of ?D], unfold id, rule ta_res_ctxt[OF _ qq''], simp, intro exI conjI,
      rule rule, rule eps, simp add: len, intro allI impI)
      fix j
      assume j: "j < length ts"
      let ?l = "map (ta_res TA) (take i ts) @ ta_res TA (Var (qs ! i)) # map (ta_res TA) (drop (Suc i) ts)"
      show "qs ! j \<in> ?l ! j"
      proof (cases "j = i")
        case False
        with j i have "?l ! j = ta_res TA (ts ! j)" by (auto simp: nth_append)
        with steps[OF j] show ?thesis by auto
      next
        case True
        with i have "?l ! j = ta_res TA (Var (qs ! i))" by (auto simp: nth_append)
        then show ?thesis using True by simp
      qed
    qed
    from Fun(1)[OF _ steps[OF i] qsi] i have "qs ! i \<in> ta_res ?TA (ts ! i)" by auto
    note this qsi
  } note IH = this
  from ta_only_prod_eps[OF eps q]
  have "(qa,q) \<in> (ta_eps ?TA)^* \<and> qa \<in> ta_productive TA" by simp
  then have eps: "(qa,q) \<in> (ta_eps ?TA)^*" and qa: "qa \<in> ta_productive TA" by auto
  with IH(2) len have "r_states (f qs \<rightarrow> qa) \<subseteq> ta_productive TA" by (auto simp: r_states_def set_conv_nth)
  with rule have rule: "(f qs \<rightarrow> qa) \<in> ta_rules ?TA" unfolding ta_restrict_def Let_def by auto
  show ?case
    by (simp, intro exI conjI, rule rule, rule eps, insert len IH(1), auto)
qed

lemma ta_productive_final: assumes q: "q \<in> ta_final TA"
  shows "q \<in> ta_productive TA"
  by (rule ta_productiveI[OF _ q, of \<box>], auto)

(* It is sound to restrict to productive states. *)
lemma ta_only_prod_lang: "ta_lang (ta_only_prod TA) = ta_lang TA" (is "ta_lang ?TA = _")
proof
  show "ta_lang ?TA \<subseteq> ta_lang TA" by (rule ta_lang_mono[OF ta_restrict_subset])
  show "ta_lang TA \<subseteq> ta_lang ?TA" 
  proof
    fix t
    assume "t \<in> ta_lang TA"
    from ta_langE2[OF this] obtain q where gt: "ground t" and f: "q \<in> ta_final TA" 
      and q: "q \<in> ta_res TA (adapt_vars t)" .
    from ta_res_only_prod[OF q ta_productive_final[OF f]]
    have q: "q \<in> ta_res ?TA (adapt_vars t)" by auto
    from f ta_productive_final[of _ TA] have "q \<in> ta_final ?TA"
      unfolding ta_restrict_def Let_def by auto
    from ta_langI2[OF gt this q] show "t \<in> ta_lang ?TA" .
  qed
qed

(* the productive states are also productive w.r.t. the new automaton *)
lemma ta_only_prod_productive: "ta_states (ta_only_prod TA) \<subseteq> ta_productive (ta_only_prod TA)"
proof
  let ?TA = "ta_only_prod TA"
  fix q
  assume "q \<in> ta_states ?TA"
  from set_mp[OF ta_restrict_states_Q this] have "q \<in> ta_productive TA" .
  from ta_productiveE[OF this] obtain q' C where
    qq': "q' \<in> ta_res TA C\<langle>Var q\<rangle>" and q': "q' \<in> ta_final TA" by auto
  from ta_productive_final[OF q'] have q'p: "q' \<in> ta_productive TA" .
  from ta_res_only_prod[OF qq' q'p] have qq': "q' \<in> ta_res ?TA C\<langle>Var q\<rangle>" .
  have q': "q' \<in> ta_final ?TA" unfolding ta_restrict_def using q' q'p by auto
  show "q \<in> ta_productive ?TA"
    by (rule ta_productiveI[OF qq' q'])
qed

(* if previosly all states are reachable, then this also holds after removing
   all non-productive ones *)
lemma ta_only_prod_reachable: assumes all_reach: "ta_states TA \<subseteq> ta_reachable TA"
  shows "ta_states (ta_only_prod TA) \<subseteq> ta_reachable (ta_only_prod TA)"
proof
  let ?TA = "ta_only_prod TA"
  fix q
  assume q: "q \<in> ta_states ?TA"
  then have q_prod: "q \<in> ta_productive TA" using ta_restrict_states_Q[of TA] by auto
  from q have "q \<in> ta_states TA" using ta_restrict_states[of TA] by auto
  with all_reach have "q \<in> ta_reachable TA" by auto
  from ta_reachableE[OF this] obtain t where gt: "ground t" and tq: "q \<in> ta_res TA t" by auto
  from ta_res_only_prod[OF tq q_prod] gt 
  show "q \<in> ta_reachable ?TA" using gt unfolding ta_reachable_def by auto
qed

lemma ta_prod_reach_subset: "ta_subset (ta_only_prod (ta_only_reach TA)) TA"
  by (rule ta_subset_trans, (rule ta_restrict_subset)+)

lemma ta_prod_reach_states: "ta_states (ta_only_prod (ta_only_reach TA)) \<subseteq> ta_states TA"
  by (rule ta_subset_ta_states[OF ta_prod_reach_subset])

(* turn a finite automaton into a trim one, by removing
   first all unreachable and then all non-productive states *)
definition trim_ta :: "('q,'f)ta \<Rightarrow> ('q,'f)ta" where
  "trim_ta TA = ta_only_prod (ta_only_reach TA)"

lemma trim_ta_lang: "ta_lang (trim_ta TA) = ta_lang TA"
  unfolding trim_ta_def ta_only_reach_lang ta_only_prod_lang ..

lemma trim_ta_subset: "ta_subset (trim_ta TA) TA"
  unfolding trim_ta_def by (rule ta_prod_reach_subset)

theorem trim_ta: "ta_trim (trim_ta TA)"
proof -
  let ?R = "ta_only_reach TA"
  have "ta_states (trim_ta TA) \<subseteq> ta_productive (trim_ta TA)" unfolding trim_ta_def 
    by (rule ta_only_prod_productive)
  moreover
  have "ta_states ?R \<subseteq> ta_reachable ?R"
    by (rule ta_only_reach_reachable)
  from ta_only_prod_reachable[OF this]
  have "ta_states (trim_ta TA) \<subseteq> ta_reachable (trim_ta TA)" unfolding trim_ta_def .
  ultimately show ?thesis unfolding ta_trim_def by blast
qed

(* Proposition 7: every tree automaton can be turned into an  equivalent trim one *)
lemmas obtain_trimmed_ta = trim_ta trim_ta_lang ta_subset_det[OF trim_ta_subset]
thm obtain_trimmed_ta


subsection \<open>Computing reachability\<close>

definition "new_reach TA \<equiv> { q | f q. (f [] \<rightarrow> q) \<in> ta_rules TA }"

definition "reduced_TA f TA Q \<equiv> \<lparr>ta_final = {}, 
       ta_rules = { f (filter (\<lambda> q. q \<notin> Q) qs) \<rightarrow> q | f qs q. (f qs \<rightarrow> q) \<in> ta_rules TA \<and> q \<notin> Q} 
         \<union> { f [] \<rightarrow> q' | q q'. (q,q') \<in> ta_eps TA \<and> q \<in> Q \<and> q' \<notin> Q}
        , ta_eps = {(q,q') | q q'. (q,q') \<in> ta_eps TA \<and> q \<notin> Q \<and> q' \<notin> Q}\<rparr>"

lemma [code]: "new_reach TA = r_rhs ` { r \<in> ta_rules TA . r_lhs_states r = []}" (is "?A = ?B")
proof -
  note d = new_reach_def
  {
    fix q
    assume "q \<in> ?A"
    from this[unfolded d] obtain f where rule: "(f [] \<rightarrow> q) \<in> ta_rules TA" by auto
    let ?r = "f [] \<rightarrow> q"
    have "r_lhs_states ?r = []" "q = r_rhs ?r" by auto
    with rule have "q \<in> ?B" by blast
  }
  moreover
  {
    fix q 
    assume "q \<in> ?B"
    then obtain r where "r_rhs r = q" "r_lhs_states r = []" "r \<in> ta_rules TA" by auto
    then have "q \<in> ?A" unfolding d by (cases r, auto)
  }
  ultimately show ?thesis by auto
qed

lemma [code]: "reduced_TA f TA Q = \<lparr>ta_final = {}, 
       ta_rules = 
       (\<lambda> r. case r of (f qs \<rightarrow> q) \<Rightarrow> (f (filter (\<lambda> q. q \<notin> Q) qs) \<rightarrow> q)) ` {r \<in> ta_rules TA . r_rhs r \<notin> Q} \<union>
       (\<lambda> p. (f [] \<rightarrow> snd p)) ` {p \<in> ta_eps TA. fst p \<in> Q \<and> snd p \<notin> Q} 
        , ta_eps = {p \<in> ta_eps TA. fst p \<notin> Q \<and> snd p \<notin> Q}\<rparr>" 
proof -
  have cong: "\<And> f r1 r2 e r1' r2' e'. r1 = r1' \<Longrightarrow> r2 = r2' \<Longrightarrow> e = e' \<Longrightarrow> 
    \<lparr> ta_final = f, ta_rules = r1 \<union> r2, ta_eps = e \<rparr> = \<lparr> ta_final = f, ta_rules = r1' \<union> r2', ta_eps = e' \<rparr>" by auto
  show ?thesis unfolding reduced_TA_def
  proof (rule cong)
    let ?f = "(\<lambda>r. case r of (f qs \<rightarrow> q) \<Rightarrow> (f [q\<leftarrow>qs . q \<notin> Q] \<rightarrow> q))"
    show "{(f [q\<leftarrow>qs . q \<notin> Q] \<rightarrow> q) | f qs q. (f qs \<rightarrow> q) \<in> ta_rules TA \<and> q \<notin> Q} =
      ?f ` {r \<in> ta_rules TA. r_rhs r \<notin> Q}"
      (is "?A = ?B")
    proof -
      {
        fix r
        assume "r \<in> ?B"
        then obtain rr where "r = ?f rr" "rr \<in> ta_rules TA" "r_rhs rr \<notin> Q" by blast
        then have "r \<in> ?A" by (cases rr, auto)
      }
      moreover
      have "?A \<subseteq> ?B" by force
      ultimately show ?thesis by blast
    qed
  qed (force+)
qed
 

lemma new_reach_states: "new_reach TA \<subseteq> ta_states TA" 
  unfolding new_reach_def ta_states_def r_states_def by auto

lemma new_reach_reachable: assumes q: "q \<in> new_reach TA"
  shows "q \<in> ta_reachable TA" 
proof -
  from q[unfolded new_reach_def] obtain f where 
     r: "(f [] \<rightarrow> q) \<in> ta_rules TA" by auto
  let ?t = "Fun f []"
  from r have "q \<in> ta_res TA ?t" "ground ?t" by auto
  then show ?thesis unfolding ta_reachable_def by blast
qed

lemma new_reach_empty: assumes empty: "new_reach TA = {}"
  shows "ta_reachable TA = {}"
proof -
  { 
    fix q
    assume "q \<in> ta_reachable TA"
    from this[unfolded ta_reachable_def] obtain t where "ground t" "q \<in> ta_res TA t" by auto
    then have False
    proof (induct t arbitrary: q)
      case (Fun f ts q)
      from Fun(3) obtain qs q' where r: "(f qs \<rightarrow> q') \<in> ta_rules TA" and 
        rec: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" and len: "length qs = length ts" by auto
      show ?case
      proof (cases ts)
        case (Cons s ss)      
        with len obtain q1 qs' where qs: "qs = q1 # qs'" by (cases qs, auto)
        show False
          by (rule Fun(1)[of s "hd qs"], insert Fun(2) rec[of 0] len, auto simp: Cons qs)
      next
        case Nil
        with len have qs: "qs = []" by auto
        with r empty show False unfolding new_reach_def by auto
      qed
    qed auto
  }
  then show ?thesis by auto
qed

lemma reduced_TA_states: "ta_states (reduced_TA f TA Q) \<subseteq> ta_states TA - Q" (is "?l \<subseteq> ?r")
proof
  fix q
  assume q: "q \<in> ?l"
  let ?TA = "reduced_TA f TA Q"
  note d = ta_states_def
  note d' = reduced_TA_def
  note d'' = r_states_def
  from q[unfolded d] obtain r eps 
    where "(q \<in> r_states r \<and> r \<in> ta_rules ?TA \<or> q \<in> (\<lambda> (q,q'). {q,q'}) eps \<and> eps \<in> ta_eps ?TA) \<or> q \<in> ta_final ?TA"
    (is "?choice \<or> _")
    by blast
  then have ?choice unfolding d' by auto
  then show "q \<in> ?r"
  proof
    assume "q \<in> (\<lambda> (q,q'). {q,q'}) eps \<and> eps \<in> ta_eps ?TA"
    then show ?thesis unfolding d d' by auto
  next
    assume "q \<in> r_states r \<and> r \<in> ta_rules ?TA"
    then have q: "q \<in> r_states r" and r: "r \<in> ta_rules ?TA" by auto
    from r[unfolded d']
    have "(\<exists>f qs q'. r = (f [q\<leftarrow>qs . q \<notin> Q] \<rightarrow> q') \<and> (f qs \<rightarrow> q') \<in> ta_rules TA \<and> q' \<notin> Q) \<or>
      (\<exists>q1 q2. r = (f [] \<rightarrow> q2) \<and> (q1, q2) \<in> ta_eps TA \<and> q1 \<in> Q \<and> q2 \<notin> Q)" by auto
    then show ?thesis
      by (cases, insert q, (force simp: d d'')+)
  qed
qed  

lemma ta_reachable_code: "ta_reachable TA = (let Q = new_reach TA in (if Q \<subseteq> {} then {}
  else Q \<union> ta_reachable (reduced_TA f TA Q)))" 
proof -
  define Q where "Q = new_reach TA"
  let ?TA = "reduced_TA f TA Q"
  have "ta_states ?TA \<subseteq> ta_states TA" using reduced_TA_states[of f TA Q] by blast
  show ?thesis unfolding Let_def Q_def[symmetric]
  proof (cases "Q = {}")
    case True
    with True new_reach_empty[OF True[unfolded Q_def]] 
    show "ta_reachable TA = (if Q \<subseteq> {} then {} else Q \<union> ta_reachable (reduced_TA f TA Q))"
      by auto
  next
    case False
    note d = ta_reachable_def
    note d' = reduced_TA_def
    from new_reach_reachable[of _ TA] have Q: "Q \<subseteq> ta_reachable TA" by (auto simp: Q_def)
    have "Q \<union> ta_reachable (reduced_TA f TA Q) = ta_reachable TA" (is "?l = ?r")
    proof -
      {
        fix q
        assume "q \<in> ta_reachable ?TA"
        then obtain t where "ground t" "q \<in> ta_res ?TA t" unfolding d by auto
        then have "q \<in> ta_reachable TA"
        proof (induct t arbitrary: q)
          case (Fun g ts q)
          from Fun(3)
            obtain qs q' where 
             r: "(g qs \<rightarrow> q') \<in> ta_rules ?TA" and 
             rec: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res ?TA (ts ! i)" and 
             len: "length qs = length ts" and
             eps: "(q',q) \<in> (ta_eps ?TA)^*" by auto
          {
            fix i
            assume i: "i < length ts"
            then have mem: "ts ! i \<in> set ts" by auto
            with Fun(2) have "ground (ts ! i)" by auto
            from Fun(1)[OF mem this rec[OF i]] have "qs ! i \<in> ta_reachable TA" .
          } 
          from this[folded len] have IH: "set qs \<subseteq> ta_reachable TA" unfolding set_conv_nth by auto
          from r[unfolded d']
          have "(\<exists>qsa. qs = [q\<leftarrow>qsa . q \<notin> Q] \<and> (g qsa \<rightarrow> q') \<in> ta_rules TA) \<or>
                 (\<exists>q. (q, q') \<in> ta_eps TA \<and> q \<in> Q)" (is "?a \<or> ?b") by auto
          then have q': "q' \<in> ta_reachable TA"
          proof
            assume ?a
            then obtain qsa where qs: "qs = [q\<leftarrow>qsa . q \<notin> Q]" and rule: "(g qsa \<rightarrow> q') \<in> ta_rules TA" by auto
            from IH qs Q have qsa: "set qsa \<subseteq> ta_reachable TA" by auto
            show ?thesis
              by (rule ta_reachableI_rule[OF qsa rule])
          next
            assume ?b
            then obtain q1 where eps: "(q1, q') \<in> ta_eps TA" and q1: "q1 \<in> Q" by auto
            with Q have reach: "q1 \<in> ta_reachable TA" by auto
            show ?thesis
              by (rule ta_reachableI_eps[OF reach eps])
          qed
          have "ta_eps ?TA \<subseteq> ta_eps TA" unfolding d' by auto
          from rtrancl_mono[OF this] eps
          have "(q',q) \<in> (ta_eps TA)^*" by auto
          from ta_reachableI_eps'[OF q' this]
          show ?case .
        qed auto
      }
      moreover
      {
        fix q
        assume "q \<in> ta_reachable TA"
        then obtain t where "ground t" "q \<in> ta_res TA t" unfolding d by auto
        then have "q \<in> Q \<or> q \<in> ta_reachable ?TA"
        proof (induct t arbitrary: q)
          case (Fun g ts q)
          from Fun(3)
            obtain qs q' where 
             r: "(g qs \<rightarrow> q') \<in> ta_rules TA" and 
             rec: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)" and 
             len: "length qs = length ts" and
             eps: "(q',q) \<in> (ta_eps TA)^*" by auto
          {
            fix i
            assume i: "i < length ts"
            then have mem: "ts ! i \<in> set ts" by auto
            with Fun(2) have "ground (ts ! i)" by auto
            note Fun(1)[OF mem this rec[OF i]]
          }
          from this[folded len] have IH: "set qs \<subseteq> Q \<union> ta_reachable ?TA" unfolding set_conv_nth by auto
          have q': "q' \<in> Q \<or> q' \<in> ta_reachable ?TA"
          proof (cases "q' \<in> Q")
            case False
            then have r: "(g [q\<leftarrow>qs. q \<notin> Q] \<rightarrow> q') \<in> ta_rules ?TA" using r unfolding d' by auto
            have "q' \<in> ta_reachable ?TA"
              by (rule ta_reachableI_rule[OF _ r], insert IH, auto)
            then show ?thesis ..
          qed auto
          with eps show ?case
          proof (induct)
            case (step q1 q2)
            from step(3)[OF step(4)]
            have q1: "q1 \<in> Q \<or> q1 \<in> ta_reachable (reduced_TA f TA Q)" .
            show ?case
            proof (cases "q2 \<in> Q")
              case False note q2 = this
              show ?thesis
              proof (cases "q1 \<in> Q")
                case False
                with step(2) q2 have eps: "(q1,q2) \<in> ta_eps ?TA" unfolding d' by auto
                show ?thesis
                  by (rule disjI2[OF ta_reachableI_eps[OF _ eps]], insert False q1, auto)
              next
                case True
                with q2 step(2) have rule: "(f [] \<rightarrow> q2) \<in> ta_rules ?TA" unfolding d' by auto
                show ?thesis
                  by (rule disjI2[OF ta_reachableI_rule[OF _ rule]], auto)
              qed
            qed auto
          qed
        qed auto
      }
      ultimately show ?thesis using Q by blast
    qed
    then show "ta_reachable TA = (if Q \<subseteq> {} then {} else Q \<union> ta_reachable (reduced_TA f TA Q))"
      using False by auto
  qed
qed

declare ta_reachable_code[of _ default, code]

subsection \<open>Computing productivity\<close>

text \<open>First, use an alternative definition of productivity\<close>

inductive_set ta_productive_ind :: "('q,'f)ta \<Rightarrow> 'q set" for TA :: "('q,'f)ta" where
  final: "q \<in> ta_final TA \<Longrightarrow> q \<in> ta_productive_ind TA"
| eps: "(q,q') \<in> (ta_eps TA)^* \<Longrightarrow> q' \<in> ta_productive_ind TA \<Longrightarrow> q \<in> ta_productive_ind TA"
| rule: "(f qs \<rightarrow> q) \<in> ta_rules TA \<Longrightarrow> q \<in> ta_productive_ind TA \<Longrightarrow> q' \<in> set qs \<Longrightarrow> q' \<in> ta_productive_ind TA"

lemma ta_productive_ind: "ta_productive_ind TA = ta_productive TA"
proof -
  {
    fix q
    assume "q \<in> ta_productive_ind TA"
    then have "q \<in> ta_productive TA"
    proof (induct)
      case (final q)
      then show ?case by (rule ta_productive_final)
    next
      case (eps p q)
      from ta_productiveE[OF eps(3)] 
      obtain q'' C where rest: "q'' \<in> ta_res TA (C\<langle>Var q\<rangle>)" and fin: "q'' \<in> ta_final TA" .
      from eps(1) have pq': "q \<in> ta_res TA (Var p)" by auto
      show ?case
        by (rule ta_productiveI[OF ta_res_ctxt[OF pq' rest] fin])
    next
      case (rule f qs q p)
      from ta_productiveE[OF rule(3)] 
      obtain q'' C where rest: "q'' \<in> ta_res TA (C\<langle>Var q\<rangle>)" and fin: "q'' \<in> ta_final TA" .
      from rule(4) obtain i where i: "i < length qs" and p: "p = qs ! i" unfolding set_conv_nth by auto
      let ?p = "\<lambda> q t. q \<in> ta_res TA t"
      let ?qs = "map Var qs"
      let ?C = "More f (take i ?qs) Hole (drop (Suc i) ?qs)"
      let ?D = "C \<circ>\<^sub>c ?C"
      from i have [simp]: "Suc (length qs - Suc 0) = length qs" by auto
      show ?case
        apply (rule ta_productiveI[OF _ fin, of ?D], simp)
        apply (rule ta_res_ctxt[OF _ rest(1)])
        apply (insert i, simp del: ta_res.simps(1))
        apply (intro exI conjI, rule rule(1), force+)
        apply (intro allI impI)
      proof -
        fix j
        assume j: "j < length qs"
        show "qs ! j \<in> (map (ta_res TA) (take i ?qs) @ ta_res TA (Var p) # map (ta_res TA) (drop (Suc i) ?qs)) ! j"
          (is "_ \<in> ?list ! j")
        proof (cases "j = i")
          case True
          with i show ?thesis unfolding p by (simp add: nth_append)
        next
          case False 
          from i have [simp]: "min (length qs) i = i" by auto
          from False i j have id: "?list ! j = ta_res TA (Var (qs ! j))"
            by (simp add: nth_append)
          show ?thesis unfolding id using j by auto
        qed
      qed
    qed
  }
  moreover
  {
    fix q
    assume "q \<in> ta_productive TA"
    from ta_productiveE[OF this]
    obtain q'' C where q'': "q'' \<in> ta_res TA (C\<langle>Var q\<rangle>)" and f: "q'' \<in> ta_final TA" .
    from q'' ta_productive_ind.final[OF f]
    have "q \<in> ta_productive_ind TA"
    proof (induct C arbitrary: q q'')
      case (Hole q q'')
      from Hole(1) have "(q,q'') \<in> (ta_eps TA)^*" by auto
      from ta_productive_ind.eps[OF this Hole(2)] show ?case .
    next
      case (More f bef C aft p q'')
      let ?i = "length bef"
      let ?n = "Suc (?i + length aft)"
      from More(2)[simplified] obtain qs q 
        where rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
         and qq'': "(q, q'') \<in> (ta_eps TA)^*"
         and len: "length qs = ?n"
         and rec: "\<And> i. i < ?n \<Longrightarrow> qs ! i \<in> (map (ta_res TA) bef @ ta_res TA C\<langle>Var p\<rangle> # map (ta_res TA) aft) ! i" by auto
      from rec[of ?i] have reci: "qs ! ?i \<in> ta_res TA C\<langle>Var p\<rangle>" by (auto simp: nth_append)
      show ?case
      proof (rule More(1)[OF reci ta_productive_ind.rule[OF rule ta_productive_ind.eps[OF qq'' More(3)]]])
        show "qs ! ?i \<in> set qs" using len by auto
      qed
    qed
  }
  ultimately show ?thesis by auto
qed      

definition productive_relation :: "('q,'f)ta \<Rightarrow> 'q rel" where
  "productive_relation TA \<equiv> ((\<lambda> (a,b). (b,a)) ` ta_eps TA) \<union> \<Union> ((\<lambda> r. (\<lambda> q. (r_rhs r,q)) ` set (r_lhs_states r)) ` ta_rules TA)"

lemma ta_productive_code[code]: "ta_productive TA = (productive_relation TA)^* `` (ta_final TA)"
proof -
  note d = productive_relation_def
  let ?rel = "productive_relation TA"
  let ?prod = "ta_productive_ind TA"
  {
    fix q
    assume "q \<in> ?rel^* `` (ta_final TA)"
    then obtain r where qr: "(r,q) \<in> ?rel^*" and r: "r \<in> ta_final TA" by blast
    from qr have "q \<in> ?prod"
    proof (induct)
      case base show ?case by (rule ta_productive_ind.final[OF r])
    next
      case (step s t)
      note rel = step(2)[unfolded d]
      show ?case
      proof (cases "(t,s) \<in> ta_eps TA")
        case True
        then have "(t,s) \<in> (ta_eps TA)^*" by auto
        from ta_productive_ind.eps[OF this step(3)] show ?thesis .
      next
        case False
        with rel obtain rule where rule: "rule \<in> ta_rules TA"
        and st: "(s,t) \<in> Pair (r_rhs rule) ` set (r_lhs_states rule)" by auto
        obtain f qs q where r: "rule = (f qs \<rightarrow> q)" by (cases rule, auto)
        from st[unfolded r] have s: "s = q" and t: "t \<in> set qs" by auto
        from ta_productive_ind.rule[OF rule[unfolded r] step(3)[unfolded s] t] show ?thesis .
      qed
    qed
  }
  moreover
  {
    fix q
    assume q: "q \<in> ?prod"
    then have "q \<in> ?rel^* `` (ta_final TA)"
    proof (induct)
      case final 
      then show ?case by auto
    next
      case (rule f qs q q')
      from rule(1,4) have "(q,q') \<in> ?rel" unfolding d by force
      with rule(3) show ?case
        by (metis r_into_rtrancl rtrancl_Image_step)
    next
      case (eps q q')
      from eps(1) have "(q',q) \<in> ?rel^*"
      proof (induct)
        case (step r s)
        from step(2) have "(s,r) \<in> ?rel" unfolding d by auto
        with step(3) show ?case by simp
      qed auto
      with eps(3) show ?case by (rule rtrancl_Image_step)
    qed
  }
  ultimately show ?thesis unfolding ta_productive_ind by blast
qed

subsection \<open>Product-Automaton for computing intersections\<close>

lemma ta_eps_ta_states: assumes q: "q \<in> ta_states TA" and steps: "(q,q') \<in> (ta_eps TA)^*"
  shows "q' \<in> ta_states TA" 
  using steps
  by (cases, insert q, auto simp: ta_states_def)

definition prod_ta :: "('q1,'f)ta \<Rightarrow> ('q2,'f)ta \<Rightarrow> ('q1 \<times> 'q2)set \<Rightarrow> ('q1 \<times> 'q2, 'f)ta" where
  "prod_ta TA1 TA2 F \<equiv> \<lparr> ta_final = F, 
    ta_rules = { (f qs \<rightarrow> q) | f qs q. (f (map fst qs) \<rightarrow> fst q) \<in> ta_rules TA1 \<and> (f (map snd qs) \<rightarrow> snd q) \<in> ta_rules TA2}, 
    ta_eps = { (q,q') | q q'. (fst q, fst q') \<in> ta_eps TA1 \<and> snd q' = snd q \<and> snd q \<in> ta_states TA2 }
      \<union> { (q,q') | q q'. (snd q, snd q') \<in> ta_eps TA2 \<and> fst q' = fst q \<and> fst q \<in> ta_states TA1 } \<rparr>"

lemma prod_ta_code [code]:
  "prod_ta TA1 TA2 F = \<lparr> ta_final = F, 
    ta_rules =  ( \<lambda> r1r2. case r1r2 of (f qs1 \<rightarrow> q1, f' qs2 \<rightarrow> q2) \<Rightarrow> (f (zip qs1 qs2) \<rightarrow> (q1,q2))) `
       (\<Union> ((\<lambda> f. {r \<in> ta_rules TA1. r_sym r = f} \<times> {r \<in> ta_rules TA2. r_sym r = f}) ` ta_syms TA1)),
    ta_eps = (\<lambda> ((q,q'),p). ((q,p),(q',p))) ` (ta_eps TA1 \<times> ta_states TA2)
        \<union> (\<lambda> (p,(q,q')). ((p,q),(p,q'))) ` (ta_states TA1 \<times> ta_eps TA2)\<rparr>"
proof -
  have cong: "\<And> f r e1 e2 r' e1' e2'. r = r' \<Longrightarrow> e1 = e1' \<Longrightarrow> e2 = e2' \<Longrightarrow> 
    \<lparr> ta_final = f, ta_rules = r, ta_eps = e1 \<union> e2 \<rparr> = \<lparr> ta_final = f, ta_rules = r', ta_eps = e1' \<union> e2' \<rparr>" by auto
  show ?thesis unfolding prod_ta_def
  proof (rule cong)
    let ?f = "\<lambda> r1r2. case r1r2 of (f qs1 \<rightarrow> q1, f' qs2 \<rightarrow> q2) \<Rightarrow> (f (zip qs1 qs2) \<rightarrow> (q1, q2))"
    show "{(f qs \<rightarrow> q) | f qs q. (f (map fst qs) \<rightarrow> fst q) \<in> ta_rules TA1 \<and> (f (map snd qs) \<rightarrow> snd q) \<in> ta_rules TA2} =
      ?f ` (\<Union> ((\<lambda> f. {r \<in> ta_rules TA1. r_sym r = f} \<times> {r \<in> ta_rules TA2. r_sym r = f}) ` ta_syms TA1))" (is "?A = ?B")
    proof -
      define A B where "A = ?A" and "B = ?B" 
      {
        fix r
        assume "r \<in> ?B"
        then obtain r1 r2 where *: "r1 \<in> ta_rules TA1" "r2 \<in> ta_rules TA2" "r_sym r1 = r_sym r2" and r: "r = ?f (r1,r2)" by force
        obtain f qs1 q1 where r1: "r1 = (f qs1 \<rightarrow> q1)" by (cases r1, auto)
        obtain qs2 q2 where r2: "r2 = (f qs2 \<rightarrow> q2)" and len: "length qs1 = length qs2" using * r1 by (cases r2, auto)
        from r r1 r2 have r: "r = (f (zip qs1 qs2) \<rightarrow> (q1,q2))" by auto
        with *(1-2) len r1 r2 have "r \<in> ?A" by auto
      }
      moreover 
      have "\<And> r. r \<in> ?A \<Longrightarrow> r \<in> ?B" by (force simp: zip_map_fst_snd ta_syms_def)
      ultimately show ?thesis unfolding A_def[symmetric] B_def[symmetric] by blast
    qed
  qed (force+)
qed

lemma prod_ta_det: assumes "ta_det TA1" and "ta_det TA2"
  shows "ta_det (prod_ta TA1 TA2 F)"
  using assms unfolding ta_det_def prod_ta_def by auto

lemma prod_ta_eps: assumes S1: "fst q \<in> ta_states TA1" and S2: "snd q \<in> ta_states TA2"
  shows "((q,q') \<in> (ta_eps (prod_ta TA1 TA2 F))^* \<longleftrightarrow>
     (fst q, fst q') \<in> (ta_eps TA1)^* \<and> (snd q, snd q') \<in> (ta_eps TA2)^*)" (is "_ \<in> ?EP^* \<longleftrightarrow> _ \<in> ?E1^* \<and> _ \<in> ?E2^*")
proof
  assume "(q,q') \<in> ?EP^*"
  then show "(fst q, fst q') \<in> ?E1^* \<and> (snd q, snd q') \<in> ?E2^*"
  proof (induct)
    case (step p r)
    from step(2)[unfolded prod_ta_def]
    have "(fst p, fst r) \<in> ta_eps TA1 \<and> snd r = snd p \<and> snd p \<in> ta_states TA2 \<or>
      (snd p, snd r) \<in> ta_eps TA2 \<and> fst r = fst p \<and> fst p \<in> ta_states TA1" 
      (is "?l \<or> ?r") by auto
    then have "(fst p, fst r) \<in> ?E1^* \<and> (snd p, snd r) \<in> ?E2^*"
      by (cases, auto)
    with step(3) show ?case by auto
  qed auto
next
  assume "(fst q, fst q') \<in> ?E1^* \<and> (snd q, snd q') \<in> ?E2^*"
  then have 1: "(fst q, fst q') \<in> ?E1^*" and 2: "(snd q, snd q') \<in> ?E2^*" by auto
  obtain q1 q2 where q: "q = (q1, q2)" by force
  obtain q1' q2' where q': "q' = (q1',q2')" by force
  from ta_eps_ta_states[OF S1 1] S2 
  have S1: "q1' \<in> ta_states TA1"
   and S2: "q2 \<in> ta_states TA2"  unfolding q q' by auto
  note d = fst_conv snd_conv q q'
  from 1[unfolded d] have "((q1, q2),(q1',q2)) \<in> ?EP^*"
  proof (induct)
    case (step p1 r1)
    from step(2) S2 have "((p1,q2),(r1,q2)) \<in> ?EP" unfolding prod_ta_def by auto
    with step(3) show ?case by auto
  qed auto
  also have "((q1',q2),(q1',q2')) \<in> ?EP^*" using 2[unfolded d]
  proof (induct)
    case (step p2 r2)
    from step(2) S1 have "((q1',p2),(q1',r2)) \<in> ?EP^*" unfolding prod_ta_def by auto
    with step(3) show ?case by auto
  qed auto
  finally show "(q,q') \<in> ?EP^*" unfolding d .
qed

lemma prod_ta_res: assumes "ground t"
  shows "q \<in> ta_res (prod_ta TA1 TA2 F) (adapt_vars t) \<longleftrightarrow>
     fst q \<in> ta_res TA1 (adapt_vars t) \<and> snd q \<in> ta_res TA2 (adapt_vars t)"
  using assms
proof (induct t arbitrary: q)
  case (Fun f ts q)
  {
    fix i
    assume "i < length ts"
    then have mem: "ts ! i \<in> set ts" by auto
    with Fun(2) have "ground (ts ! i)" by auto
    note IH = Fun(1)[OF mem this]
  } note IH = this
  note d = prod_ta_def
  let ?P = "prod_ta TA1 TA2 F"
  show ?case (is "?l = ?r")
  proof
    assume ?l
    from this
    obtain qs q' where
      1: "(f (map fst qs) \<rightarrow> fst q') \<in> ta_rules TA1" and
      2: "(f (map snd qs) \<rightarrow> snd q') \<in> ta_rules TA2" and
      e: "(q',q) \<in> (ta_eps ?P)^*" and
      rec: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res ?P (adapt_vars (ts ! i))" and
      len: "length qs = length ts"
      by (auto simp: d)
    have 
      "fst q' \<in> r_states (f (map fst qs) \<rightarrow> fst q')" 
      "snd q' \<in> r_states (f (map snd qs) \<rightarrow> snd q')" 
      by (auto simp: r_states_def)
    with 1 2 have S: "fst q' \<in> ta_states TA1" "snd q' \<in> ta_states TA2"
      unfolding ta_states_def by blast+
    from e[unfolded prod_ta_eps[OF this]]
    have e: "(fst q', fst q) \<in> (ta_eps TA1)\<^sup>*" "(snd q', snd q) \<in> (ta_eps TA2)\<^sup>*" by auto
    {
      fix i
      assume i: "i < length ts"
      from rec[OF i, unfolded IH[OF i]]
      have "fst (qs ! i) \<in> ta_res TA1 (adapt_vars (ts ! i))"
        "snd (qs ! i) \<in> ta_res TA2 (adapt_vars (ts ! i))"
        by auto
    } note rec = this
    from rec(1) e(1) 1 len have 1: "fst q \<in> ta_res TA1 (adapt_vars (Fun f ts))" by force
    from rec(2) e(2) 2 len have 2: "snd q \<in> ta_res TA2 (adapt_vars (Fun f ts))" by force
    from 1 2 show ?r by blast
  next
    assume ?r
    then have 1: "fst q \<in> ta_res TA1 (adapt_vars (Fun f ts))"
     and  2: "snd q \<in> ta_res TA2 (adapt_vars (Fun f ts))" by auto
    from 1 obtain qs1 p1 where
      r1: "(f qs1 \<rightarrow> p1) \<in> ta_rules TA1" and 
      len1: "length qs1 = length ts" and
      rec1: "\<And> i. i < length ts \<Longrightarrow> qs1 ! i \<in> ta_res TA1 (adapt_vars (ts ! i))" and
      eps1: "(p1,fst q) \<in> (ta_eps TA1)^*" by auto
    from 2 obtain qs2 p2 where
      r2: "(f qs2 \<rightarrow> p2) \<in> ta_rules TA2" and 
      len2: "length qs2 = length ts" and
      rec2: "\<And> i. i < length ts \<Longrightarrow> qs2 ! i \<in> ta_res TA2 (adapt_vars (ts ! i))" and
      eps2: "(p2,snd q) \<in> (ta_eps TA2)^*" by auto
    let ?p = "(p1,p2)"
    have "fst ?p \<in> r_states (f qs1 \<rightarrow> p1)" "snd ?p \<in> r_states (f qs2 \<rightarrow> p2)" by (auto simp: r_states_def)
    with r1 r2 have "fst ?p \<in> ta_states TA1" "snd ?p \<in> ta_states TA2" unfolding ta_states_def by blast+
    from prod_ta_eps[OF this, of q F] eps1 eps2
    have eps: "((p1,p2),q) \<in> (ta_eps ?P)^*" by auto
    let ?qs = "zip qs1 qs2"
    let ?r = "f ?qs \<rightarrow> ?p"
    from r1 r2 len1 len2 have r: "?r \<in> ta_rules ?P" unfolding d by auto
    {
      fix i
      assume i: "i < length ts"
      have "?qs ! i \<in> ta_res ?P (adapt_vars (ts ! i))"
        unfolding IH[OF i] using rec1[OF i] rec2[OF i] i len1 len2 by auto
    } note rec = this
    from len1 len2 have len: "length ?qs = length ts" by auto
    show ?l unfolding adapt_vars_simps ta_res.simps
      by (rule, intro exI conjI, rule refl, rule r, rule eps, insert len rec, auto)
  qed
qed auto

definition intersect_ta :: "('q,'f)ta \<Rightarrow> ('p,'f)ta \<Rightarrow> ('q \<times> 'p,'f)ta" where
  "intersect_ta TA1 TA2 = prod_ta TA1 TA2 (ta_final TA1 \<times> ta_final TA2)"

lemma intersect_ta: "ta_lang (intersect_ta TA1 TA2) = ta_lang TA1 \<inter> ta_lang TA2" (is "?A = ?B \<inter> ?C")
proof -
  let ?F = "ta_final TA1 \<times> ta_final TA2"
  note d = intersect_ta_def ta_lang_def2
  {
    fix t
    assume "t \<in> ?A"
    from this[unfolded d] obtain q where g: "ground t"
      and fin: "q \<in> ?F"
      and res: "q \<in> ta_res (prod_ta TA1 TA2 ?F) (adapt_vars t)" 
      unfolding prod_ta_def by auto
    from res[unfolded prod_ta_res[OF g]] fin g
    have "t \<in> ?B \<inter> ?C" unfolding d by auto
  }
  moreover
  {
    fix t
    assume "t \<in> ?B \<inter> ?C"
    from this[unfolded d] obtain q1 q2 where g: "ground t"
      and fin: "q1 \<in> ta_final TA1" "q2 \<in> ta_final TA2"
      and res: "q1 \<in> ta_res TA1 (adapt_vars t)" "q2 \<in> ta_res TA2 (adapt_vars t)" by auto
    let ?q = "(q1,q2)"
    from prod_ta_res[OF g, of ?q TA1 TA2 ?F] res have "?q \<in> ta_res (intersect_ta TA1 TA2) (adapt_vars t)"
      unfolding d by auto
    with fin g have "t \<in> ?A" unfolding d prod_ta_def by auto
  }
  ultimately show ?thesis by blast
qed

lemma intersect_ta_det: "ta_det TA1 \<Longrightarrow> ta_det TA2 \<Longrightarrow> ta_det (intersect_ta TA1 TA2)"
  unfolding intersect_ta_def by (rule prod_ta_det)

section \<open>Deciding emptyness\<close>

definition ta_empty :: "('q,'f)ta \<Rightarrow> bool" where
  "ta_empty TA \<equiv> ta_reachable TA \<inter> ta_final TA \<subseteq> {}"

lemma ta_empty[simp]: "ta_empty TA = (ta_lang TA = {})" (is "?l = (?L = {})")
proof -
  {
    assume "\<not> ?l"
    from this[unfolded ta_empty_def] obtain q where 
      reach: "q \<in> ta_reachable TA" and fin: "q \<in> ta_final TA" by auto
    from ta_reachableE[OF reach] fin obtain t where g: "ground t" and
      res: "q \<in> ta_res TA t" by auto 
    from ta_langI[OF g fin res refl] have "?L \<noteq> {}" by auto
  }
  moreover
  {
    assume "?L \<noteq> {}"
    then obtain t where "t \<in> ?L" by auto
    from ta_langE[OF this] obtain t' q where g: "ground t'" and res: "q \<in> ta_res TA t'" and fin: "q \<in> ta_final TA" .
    from ta_res_states[OF g, of TA] res have q: "q \<in> ta_states TA" by auto
    from q res g fin have "\<not> ?l" unfolding ta_empty_def ta_reachable_def by auto
  }
  ultimately show ?thesis by blast
qed

section \<open>Computation of membership\<close>

declare ta_res.simps[code del]

lemma [code]: "ta_res TA (Var q) = (ta_eps TA)^* `` {q}" unfolding ta_res.simps by auto
lemma [code]: "ta_res TA (Fun f ts) = (let Qs = map (ta_res TA) ts; g = (f, length ts) in 
   (ta_eps TA)^* `` 
  (r_rhs ` {r \<in> ta_rules TA. r_sym r = g \<and> (\<forall> Qq \<in> set (zip Qs (r_lhs_states r)). snd Qq \<in> fst Qq) }))"
  (is "?l = ?r")
proof -
  let ?Qs = "map (ta_res TA) ts"
  let ?g = "(f, length ts)"
  let ?R = "{r \<in> ta_rules TA. r_sym r = ?g \<and> (\<forall> Qq \<in> set (zip ?Qs (r_lhs_states r)). snd Qq \<in> fst Qq) }"
  {
    fix q
    assume "q \<in> ?l"
    then  obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)"
    and eps: "(q',q) \<in> (ta_eps TA)^*"
      by auto
    from rule rec len have "(f qs \<rightarrow> q') \<in> ?R" by (auto simp: set_zip)
    then have "q' \<in> r_rhs ` ?R" by force
    with eps have "q \<in> ?r" unfolding Let_def by blast
  }
  moreover
  {
    fix q
    assume "q \<in> ?r"
    then obtain q' where "q' \<in> r_rhs ` ?R" and eps: "(q',q) \<in> (ta_eps TA)^*" unfolding Let_def by auto
    then obtain r where "r \<in> ?R" and q': "q' = r_rhs r" by auto
    then have r: "r \<in> ta_rules TA" "r_sym r = ?g" "\<And> Qq. Qq \<in> set (zip ?Qs (r_lhs_states r)) \<Longrightarrow> snd Qq \<in> fst Qq" by auto
    from r(2) q' obtain qs where rule: "r = (f qs \<rightarrow> q')"  and len: "length qs = length ts" by (cases r, auto)
    note r = r[unfolded rule, simplified]
    have "q \<in> ?l" unfolding ta_res.simps
    proof (rule, intro exI conjI, rule refl, rule r(1), rule eps, rule len, intro allI impI)
      fix i
      assume i: "i < length ts"
      with r(3)[of "(ta_res TA (ts ! i), qs ! i)"]
      show "qs ! i \<in> map (ta_res TA) ts ! i" by (force simp: set_zip len)
    qed
  }
  ultimately show ?thesis by blast
qed

definition "ta_member t TA \<equiv> ground t \<and> \<not> (ta_final TA \<inter> ta_res TA (adapt_vars t) \<subseteq> {})"

lemma [simp]: "ta_member t TA = (t \<in> ta_lang TA)" 
  unfolding ta_member_def ta_lang_def2 by auto

lemma [code_unfold]: "t \<in> ta_lang TA \<longleftrightarrow> ta_member t TA" by simp

subsection \<open>Sufficient criterion for containment\<close>
(* sufficient criterion to check whether automaton accepts at least T(g(F)) where F is a subset of
   the signature *) 

definition ta_contains_aux :: "('f \<times> nat)set \<Rightarrow> 'q set \<Rightarrow> ('q,'f)ta \<Rightarrow> 'q set \<Rightarrow> bool" where
  "ta_contains_aux F Q1 TA Q2 \<equiv> (\<forall> f qs. (f,length qs) \<in> F \<and> set qs \<subseteq> Q1 \<longrightarrow> (\<exists> q q'. (f qs \<rightarrow> q) \<in> ta_rules TA \<and> q' \<in> Q2 \<and> (q,q') \<in> (ta_eps TA)^*))"

lemma ta_contains_aux_mono: assumes R: "ta_rules TA1 \<subseteq> ta_rules TA2" and e: "ta_eps TA1 \<subseteq> ta_eps TA2"
  and q: "Q2 \<subseteq> Q2'"
  shows "ta_contains_aux F Q1 TA1 Q2 \<Longrightarrow> ta_contains_aux F Q1 TA2 Q2'" unfolding ta_contains_aux_def 
  using R rtrancl_mono[OF e] q by blast

definition ta_contains :: "('f \<times> nat)set \<Rightarrow> ('f \<times> nat)set \<Rightarrow> ('q,'f)ta \<Rightarrow> 'q set \<Rightarrow> bool"
  where "ta_contains F G TA Q \<equiv> ta_contains_aux F Q TA Q \<and> ta_contains_aux G Q TA (ta_final TA)"

lemma ta_contains_mono: assumes R: "ta_rules TA1 \<subseteq> ta_rules TA2" and e: "ta_eps TA1 \<subseteq> ta_eps TA2"
  and f: "ta_final TA1 \<subseteq> ta_final TA2"
  shows "ta_contains F G TA1 Q2 \<Longrightarrow> ta_contains F G TA2 Q2" unfolding ta_contains_def 
  using ta_contains_aux_mono[OF R e subset_refl] ta_contains_aux_mono[OF R e f] by blast

lemma ta_contains_both: 
  assumes contain: "ta_contains F G TA qs"
  shows "{t :: ('f,'v)term. \<Union> (funas_term ` set (args t)) \<subseteq> F \<and> the (root t) \<in> G \<and> ground t} \<subseteq> ta_lang TA"
proof (clarify)
  fix t :: "('f,'v)term"
  note contain = contain[unfolded ta_contains_def ta_contains_aux_def, simplified]
  assume F: "\<Union>(funas_term ` set (args t)) \<subseteq> F" and G: "the (root t) \<in> G" and g: "ground t"
  from g obtain g ss where t: "t = Fun g ss" by (cases t, auto)
  {
    fix s
    assume "s \<in> set ss"
    with F g have "funas_term s \<subseteq> F" and "ground s" unfolding t by auto
    then have "\<exists> q \<in> qs. q \<in> ta_res TA (adapt_vars s)"
    proof (induct s)
      case (Var x) then show ?case by simp
    next
      case (Fun f ts)
      {
        fix i
        assume i: "i < length ts"
        then have t: "ts ! i \<in> set ts" by auto
        from Fun(3) t have gt: "ground (ts ! i)" by auto
        from Fun(2) t have fs: "funas_term (ts ! i) \<subseteq> F" by auto
        from Fun(1)[OF t fs gt] i have "\<exists>q\<in>qs. q \<in> ta_res TA ((map adapt_vars ts) ! i)" by auto
      } then have "\<forall> i. \<exists> q. i < length ts \<longrightarrow> q \<in> qs \<and> q \<in> ta_res TA ((map adapt_vars ts) ! i)" by auto
      from choice[OF this] obtain qs' where qs'res: "\<And>i. i < length ts \<Longrightarrow> qs' i \<in> qs \<and> qs' i \<in> ta_res TA ((map adapt_vars ts) ! i)" by auto
      let ?qs = "map qs' [0 ..< length ts]"
      have qs': "\<And> i. i < length ts \<Longrightarrow>  ?qs ! i = qs' i" by auto
      with qs'res have qs'res: "\<forall> i < length ts. ?qs ! i \<in> qs \<and> ?qs ! i \<in> ta_res TA ((map adapt_vars ts) ! i)" by auto
      from contain[THEN conjunct1, THEN spec[of _ f], THEN spec[of _ ?qs]] Fun(2) qs'res 
      obtain q' q where q: "q \<in> qs" and q': "(q',q) \<in> (ta_eps TA)^*" and rule: "(f ?qs \<rightarrow> q') \<in> ta_rules TA" by force
      show ?case unfolding ta_res.simps adapt_vars_simps
        by (rule bexI[OF _ q], rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ ?qs], insert rule qs'res, simp add: q')
    qed
  } note ss = this
  {
    fix i
    assume "i < length ss"
    then have "ss ! i \<in> set ss" by auto
    note ss[OF this]
  }
  then have "\<forall> i. \<exists> q. i < length ss \<longrightarrow> (q\<in>qs \<and> q \<in> ta_res TA (adapt_vars (ss ! i)))" by auto
  from choice[OF this] obtain q where q: "\<And> i. i < length ss \<Longrightarrow> q i \<in> qs \<and> q i \<in> ta_res TA (adapt_vars (ss ! i))" by auto
  let ?qs = "map q [0 ..< length ss]"
  have qs: "set ?qs \<subseteq> qs" unfolding set_conv_nth using q by auto
  from G[unfolded t] have "(g,length ?qs) \<in> G" by auto
  from contain qs this obtain p p' where rule: "g ?qs \<rightarrow> p \<in> ta_rules TA" and p': "p' \<in> ta_final TA" 
    and eps: "(p, p') \<in> (ta_eps TA)\<^sup>*"
    by blast
  have "p' \<in> ta_res TA (adapt_vars t)" unfolding t using rule eps q by force
  from ta_langI2[OF g p' this]
  show "t \<in> ta_lang TA" .
qed  

lemma ta_contains: 
  assumes contain: "ta_contains F F TA qs"
  shows "{t :: ('f,'v)term. funas_term t \<subseteq> F \<and> ground t} \<subseteq> ta_lang TA" (is "?A \<subseteq> _")
proof 
  fix t
  assume mem: "t \<in> ?A"
  then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from mem have "t \<in> {t. \<Union>(funas_term ` set (args t)) \<subseteq> F \<and> the (root t) \<in> F}"  unfolding t
    by auto
  with ta_contains_both[OF contain] mem
  show "t \<in> ta_lang TA" by auto
qed


subsection \<open>Determinization\<close>

definition ta_power_set_rules :: "('q,'f)ta \<Rightarrow> ('q set,'f)ta_rule set" where
  "ta_power_set_rules TA \<equiv> {
    f QS \<rightarrow> Q | f QS Q. (f,length QS) \<in> ta_syms TA \<and> (\<forall> QSi \<in> set (Q # QS). QSi \<subseteq> ta_states TA) \<and> 
    Q = { q' | q' q qs. (q,q') \<in> (ta_eps TA)^* \<and> TA_rule f qs q \<in> ta_rules TA \<and> length qs = length QS \<and> (\<forall> i < length QS. qs ! i \<in> QS ! i)}}"

lemma ta_power_set_rules_E: assumes "TA_rule f QS Q \<in> ta_power_set_rules TA"
  shows "\<And> QSi. QSi \<in> set (Q # QS) \<Longrightarrow> QSi \<subseteq> ta_states TA"
  and "Q = { q' | q' q qs. (q,q') \<in> (ta_eps TA)^* \<and> TA_rule f qs q \<in> ta_rules TA \<and> length qs = length QS \<and> (\<forall> i < length QS. qs ! i \<in> QS ! i)}"
  using assms unfolding ta_power_set_rules_def by blast+

lemma ta_power_set_rules_I': assumes "\<And> QSi. QSi \<in> set (Q # QS) \<Longrightarrow> QSi \<subseteq> ta_states TA"
  and "(f,length QS) \<in> ta_syms TA"
  and "Q = { q' | q' q qs. (q,q') \<in> (ta_eps TA)^* \<and> TA_rule f qs q \<in> ta_rules TA \<and> length qs = length QS \<and> (\<forall> i < length QS. qs ! i \<in> QS ! i)}"
  shows "TA_rule f QS Q \<in> ta_power_set_rules TA" using assms unfolding ta_power_set_rules_def by blast

lemma ta_power_set_rules_I: assumes QS: "\<And> QSi. QSi \<in> set QS \<Longrightarrow> QSi \<subseteq> ta_states TA"
  and rule: "TA_rule f qs q \<in> ta_rules TA" and len: "length qs = length QS"
  and Q: "Q = { q' | q' q qs. (q,q') \<in> (ta_eps TA)^* \<and> TA_rule f qs q \<in> ta_rules TA \<and> length qs = length QS \<and> (\<forall> i < length QS. qs ! i \<in> QS ! i)}"
  shows "TA_rule f QS Q \<in> ta_power_set_rules TA" 
proof (rule ta_power_set_rules_I'[OF _ _ Q])
  fix QSi
  assume "QSi \<in> set (Q # QS)"
  then have "QSi = Q \<or> QSi \<in> set QS" by simp
  then show "QSi \<subseteq> ta_states TA"
  proof
    assume "QSi \<in> set QS"
    from QS[OF this] show ?thesis .
  next
    assume *: "QSi = Q"
    show ?thesis unfolding *
    proof
      fix q'
      assume "q' \<in> Q"
      then obtain q qs where *: "(q,q') \<in> (ta_eps TA)^*" and mem: "TA_rule f qs q \<in> ta_rules TA" unfolding Q by auto
      have "q \<in> r_states (TA_rule f qs q)" unfolding r_states_def by auto
      with mem have "q \<in> ta_states TA" unfolding ta_states_def by auto
      from ta_eps_ta_states[OF this *]
      show "q' \<in> ta_states TA" .
    qed
  qed
next
  from rule have "(f,length qs) \<in> ta_syms TA"  unfolding ta_syms_def 
    by force
  with len show "(f,length QS) \<in> ta_syms TA" by auto
qed

locale ta_powerset =
  fixes TA :: "('q,'f)ta"
  and TA' :: "('p,'f)ta"
  and set_of :: "'p \<Rightarrow> 'q set"
  and P :: "'p set"  
  assumes inj: "\<And> p p'. p \<in> P \<Longrightarrow> p' \<in> P \<Longrightarrow> set_of p = set_of p' \<Longrightarrow> p = p'"
  and sound: "TA_rule f ps p \<in> ta_rules TA' \<Longrightarrow> TA_rule f (map set_of ps) (set_of p) \<in> ta_power_set_rules TA \<and> set (p # ps) \<subseteq> P"
  and P: "set_of ` P \<subseteq> {Q. Q \<subseteq> ta_states TA}"
  and eps[simp]: "ta_eps TA' = {}"
  and complete: "TA_rule f QS Q \<in> ta_power_set_rules TA \<Longrightarrow> (\<And> Q. Q \<in> set QS \<Longrightarrow> Q \<noteq> {} \<and> Q \<in> set_of ` P) \<Longrightarrow> Q \<noteq> {} 
    \<Longrightarrow> \<exists> ps p. set (p # ps) \<subseteq> P \<and> map set_of (p # ps) = (Q # QS) \<and> (TA_rule f ps p \<in> ta_rules TA')"
  and final: "ta_final TA' = { p \<in> P. set_of p \<inter> ta_final TA \<noteq> {}}"
begin
abbreviation PSR where "PSR \<equiv> ta_power_set_rules TA"

lemmas PSR_E = ta_power_set_rules_E[where TA = TA]
lemmas PSR_I = ta_power_set_rules_I[where TA = TA]
    
lemma det: "ta_det TA'"
  unfolding ta_det_def
proof (rule conjI[OF eps], intro allI impI)
  fix f ps p p'
  assume 1: "TA_rule f ps p \<in> ta_rules TA'" and 2: "TA_rule f ps p' \<in> ta_rules TA'"
  let ?QS = "map set_of ps"
  from sound[OF 1] sound[OF 2]
  have 1: "TA_rule f ?QS (set_of p) \<in> PSR" and 2: "TA_rule f ?QS (set_of p') \<in> PSR" 
    and 3: "p \<in> P" and 4: "p' \<in> P" by auto
  from PSR_E[OF 1] PSR_E[OF 2] have "set_of p = set_of p'" by simp
  from inj[OF 3 4 this] show "p = p'" .
qed

lemma TA'_P: "ta_states TA' \<subseteq> P" 
proof -
  {
    fix f ps p 
    assume *: "TA_rule f ps p \<in> ta_rules TA'" (is "?r \<in> _")
    fix q
    assume "q \<in> r_states ?r"
    with sound[OF *] have "q \<in> P" unfolding r_states_def by auto
  }
  then show ?thesis unfolding ta_states_def eps final
    by (auto, case_tac xa, auto)
qed

definition p_of :: "'q set \<Rightarrow> 'p" where
  "p_of \<equiv> the_inv_into P set_of"

lemma p_of: assumes p: "p \<in> P" shows "p_of (set_of p) = p"
proof -
  have "inj_on set_of P" unfolding inj_on_def using inj by blast
  from the_inv_into_f_f[OF this p, folded p_of_def]
  show ?thesis .
qed 
          
lemma finite: assumes "finite (ta_states TA)"
  shows "finite (ta_states TA')"
proof (rule finite_subset)
  show "ta_states TA' \<subseteq> P" by (rule TA'_P)
  show "finite P"
  proof -
    have "P = p_of ` set_of ` P" using p_of by force  
    also have "set_of ` P \<subseteq> {Q . Q \<subseteq> ta_states TA}" by (rule P)
    finally have *: "P \<subseteq> p_of ` {Q . Q \<subseteq> ta_states TA}" by blast
    show ?thesis
      by (rule finite_subset[OF *], insert assms, auto)
  qed
qed

lemma ta_lang_sound: "ta_lang TA' \<subseteq> ta_lang TA"
proof 
  fix t
  assume "t \<in> ta_lang TA'"
  from ta_langE2[OF this] obtain p where ground: "ground t" and p: "p \<in> ta_res TA' (adapt_vars t)" and fin: "p \<in> ta_final TA'" .
  from fin[unfolded final] have "p \<in> P" "set_of p \<inter> ta_final TA \<noteq> {}" by auto
  then obtain q where fin: "q \<in> ta_final TA" and q: "q \<in> set_of p" by auto
  from ground p q have "q \<in> ta_res TA (adapt_vars t)"
  proof (induct t arbitrary: p q)
    case (Fun f ts)
    from Fun(3)
    obtain ps where rule: "(f ps \<rightarrow> p) \<in> ta_rules TA'" and len: "length ps = length ts" 
      and rec: "\<And> i. i<length ts \<Longrightarrow>  ps ! i \<in> ta_res TA' (adapt_vars (ts ! i))" by auto
    from sound[OF rule] have "TA_rule f (map set_of ps) (set_of p) \<in> PSR" ..
    from \<open>q \<in> set_of p\<close>[unfolded PSR_E(2)[OF this] length_map len] obtain q' qs where
      q: "TA_rule f qs q' \<in> ta_rules TA" and qq': "(q', q) \<in> (ta_eps TA)^*" and len2: "length qs = length ts" 
      and rec2: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> map set_of ps ! i" by force    
    {
      fix i
      assume i: "i < length ts"
      then have t: "ts ! i \<in> set ts" by auto
      with Fun(2) have gt: "ground (ts ! i)" by auto
      from rec2[OF i] i len have "qs ! i \<in> set_of (ps ! i)" by auto
      from Fun(1)[OF t gt rec[OF i] this] have "qs ! i \<in> ta_res TA (adapt_vars (ts ! i))" .
    } 
    then show ?case using q qq' len2 by auto
  qed simp
  from ta_langI2[OF ground fin this] show "t \<in> ta_lang TA" .
qed

lemma ta_lang_complete: "ta_lang TA \<subseteq> ta_lang TA'"
proof 
  fix t
  assume "t \<in> ta_lang TA"
  from ta_langE2[OF this] obtain q where ground: "ground t" and q: "q \<in> ta_res TA (adapt_vars t)" and fin: "q \<in> ta_final TA" .
  let ?P = "\<lambda> t q p. p \<in> ta_res TA' (adapt_vars t) \<and> q \<in> set_of p \<and> p \<in> P"
  from ground q have "\<exists> p. ?P t q p"
  proof (induct t arbitrary: q)
    case (Fun f ts q')
    from Fun(3)
    obtain qs q where rule: "(f qs \<rightarrow> q) \<in> ta_rules TA" and len: "length qs = length ts" 
      and qq': "(q,q') \<in> (ta_eps TA)^*"
      and rec: "\<And> i. i<length ts \<Longrightarrow>  qs ! i \<in> ta_res TA (adapt_vars (ts ! i))" by auto
    {
      fix i
      assume i: "i < length ts"
      then have t: "ts ! i \<in> set ts" by auto
      with Fun(2) have gt: "ground (ts ! i)" by auto
      from Fun(1)[OF t gt rec[OF i]] have "\<exists>p. ?P (ts ! i) (qs ! i) p" .
    } 
    then have "\<forall> i. \<exists> p. i < length ts \<longrightarrow> ?P (ts ! i) (qs ! i) p" by blast
    from choice[OF this] obtain p where rec: "\<And> i. i < length ts \<Longrightarrow> ?P (ts ! i) (qs ! i) (p i)" by auto
    define ps where "ps = map p [0 ..< length ts]"    
    {
      fix i
      assume i: "i < length ts"
      then have "ps ! i = p i" unfolding ps_def len[symmetric] by auto
      with rec[OF i] have "?P (ts ! i) (qs ! i) (ps ! i)" by auto
    } note rec = this
    from ps_def have len2: "length ps = length ts" by auto
    let ?QS = "map set_of ps"
    {
      fix Q
      assume "Q \<in> set ?QS"
      then obtain i where i: "i < length ps" and Q: "Q = ?QS ! i" unfolding set_conv_nth by auto
      then have Q: "Q = set_of (ps ! i)" by auto
      from rec[OF i[unfolded len2]] have "ps ! i \<in> P" "set_of (ps ! i) \<noteq> {}" by auto
      with Q have QP: "Q \<noteq> {} \<and> Q \<in> set_of ` P" by auto
      with P have Q_TA: "Q \<subseteq> ta_states TA" by auto
      note QP Q_TA
    } note tedious = this
    define Q where "Q = { q' | q' q qs. (q,q') \<in> (ta_eps TA)^* \<and> TA_rule f qs q \<in> ta_rules TA \<and> length qs = length ?QS \<and> (\<forall> i < length ?QS. qs ! i \<in> ?QS ! i)}"
    have q'Q: "q' \<in> Q" unfolding Q_def using qq' rule rec len len2 by auto
    then have "Q \<noteq> {}" by auto
    have "TA_rule f ?QS Q \<in> PSR" 
      by (rule PSR_I[OF tedious(2) rule], auto simp: Q_def len len2)
    from complete[OF this tedious(1) \<open>Q \<noteq> {}\<close>]
    obtain p ps' where P: "set (p # ps') \<subseteq> P" and  id: "map set_of (p # ps') = Q # ?QS" and rule: "TA_rule f ps' p \<in> ta_rules TA'" by auto
    from id have "?QS = map set_of ps'" by simp
    from arg_cong[OF id, of "map p_of"] have "map (\<lambda> p. p_of (set_of p)) ps' = map (\<lambda> p. p_of (set_of p)) ps" by (simp add: o_def)
    also have "map (\<lambda> p. p_of (set_of p)) ps' = ps'"
      by (rule map_idI[OF p_of], insert P, auto)
    also have "map (\<lambda> p. p_of (set_of p)) ps = ps"
      by (rule map_idI[OF p_of], insert rec, auto simp: set_conv_nth len2)
    finally have ps': "ps' = ps" by auto
    from id q'Q have q': "q' \<in> set_of p" by auto
    from P have p: "p \<in> P" by auto
    note rule = rule[unfolded ps']
    show ?case
      by (rule exI[of _ p], insert rule p q' rec len2, auto)
  qed simp
  then obtain p where p: "p \<in> ta_res TA' (adapt_vars t)" and "q \<in> set_of p" "p \<in> P" by auto
  with fin have fin: "p \<in> ta_final TA'" unfolding final by auto
  from ta_langI2[OF ground fin p] show "t \<in> ta_lang TA'" .
qed


lemma ta_lang: "ta_lang TA' = ta_lang TA"
  using ta_lang_sound ta_lang_complete by auto

lemmas important_results = det finite ta_lang
end

(* simple interpretation: no mapping of state sets to sets (identity) and take all subsets *) 
definition "full_power_set_ta TA = \<lparr>ta_final = {P. P \<subseteq> ta_states TA \<and> P \<inter> ta_final TA \<noteq> {}}, ta_rules = ta_power_set_rules TA, ta_eps = {} \<rparr>"
  
interpretation full_power_set: ta_powerset TA "full_power_set_ta TA" 
  id "{P. P \<subseteq> ta_states TA}" unfolding full_power_set_ta_def
  by (unfold_locales, auto simp: ta_power_set_rules_def)

lemmas full_power_set_ta = full_power_set.important_results

(* where full_power_set_ta shows that for each automaton there is an equivalent deterministic one,
  for the implementation one might want to have a smarter construction, where subsets are constructed
  only on demand. *)
thm full_power_set_ta

subsection \<open>Basic lemmas for combining tree automata with rewriting\<close>
  
(* states reachable for some t \<cdot> \<tau> by first reduction terms in \<tau> to states \<sigma>*)
lemma ta_res_subst: assumes 
  x: "\<And> x. x \<in> vars_term t \<Longrightarrow> \<sigma> x \<in> ta_res TA (\<tau> x)"
  and q: "q \<in> ta_res TA (map_vars_term \<sigma> t)"
  shows "q \<in> ta_res TA (t \<cdot> \<tau>)"
using x q
proof (induct t arbitrary: q)
  case (Var x)
  from Var(1)[of x] Var(2) ta_res_eps
  show ?case by simp
next
  case (Fun f ts)
  from Fun(3)
  obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (map_vars_term \<sigma> (ts ! i))"
    and q: "(q',q) \<in> (ta_eps TA)^*"
    by auto
  let ?ts = "map (\<lambda> t. t \<cdot> \<tau>) ts"
  {
    fix i
    assume i: "i < length ts" 
    from i have mem: "ts ! i \<in> set ts" by auto
    then have "vars_term (ts ! i) \<subseteq> vars_term (Fun f ts)" by auto 
    with Fun(1)[OF mem Fun(2) rec[OF i]] have "qs ! i \<in> ta_res TA (ts ! i \<cdot> \<tau>)"
      by auto
  } note main = this
  have id: "Fun f ts \<cdot> \<tau> = Fun f ?ts" by simp
  show ?case
    by (unfold id ta_res.simps, rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ qs], intro conjI, simp, rule rule, rule q, simp add: len, simp add: main)
qed

(* decomposing substitutions: linear case *)
lemma ta_res_subst_linear: 
  assumes l: "linear_term t"
  and q: "q \<in> ta_res TA (t \<cdot> \<tau>)"
  shows "\<exists> \<sigma>. q \<in> ta_res TA (map_vars_term \<sigma> t) \<and> (\<forall> x \<in> vars_term t. \<sigma> x \<in> ta_res TA (\<tau> x))"
using l q
proof (induct t arbitrary: q)
  case (Var x)
  from Var(2) show ?case by auto
next
  case (Fun f ts)
  from Fun(3)
  obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i \<cdot> \<tau>)"
    and q: "(q',q) \<in> (ta_eps TA)^*"
    by auto
  {
    fix i
    assume i: "i < length ts" 
    from i have mem: "ts ! i \<in> set ts" by auto
    from Fun(2) mem have "linear_term (ts ! i)" by auto
    note Fun(1)[OF mem this rec[OF i]]
  }
  then have "\<forall> i. \<exists> \<sigma>. i < length ts \<longrightarrow> qs ! i \<in> ta_res TA (map_vars_term \<sigma> (ts ! i)) \<and>
             (\<forall> x \<in> vars_term (ts ! i). \<sigma> x \<in> ta_res TA (\<tau> x))"
    by blast
  from choice[OF this] obtain \<sigma> where
    ind: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (map_vars_term (\<sigma> i) (ts ! i)) \<and> 
             (\<forall> x \<in> vars_term (ts ! i). (\<sigma> i) x \<in> ta_res TA (\<tau> x))"
    by auto
  from Fun(2) have "is_partition (map vars_term ts)" by auto
  from subst_merge[OF this, of \<sigma>] obtain \<sigma>2 where \<sigma>2: "\<And> i. i < length ts \<Longrightarrow> \<forall> x \<in> vars_term (ts ! i). \<sigma>2 x = \<sigma> i x" by auto
  show ?case
  proof (rule exI[of _ \<sigma>2], intro conjI)
    show "\<forall> x \<in> vars_term (Fun f ts). \<sigma>2 x \<in> ta_res TA (\<tau> x)"
    proof
      fix x
      assume "x \<in> vars_term (Fun f ts)"
      then obtain t where "t \<in> set ts" and "x \<in> vars_term t" by auto
      then obtain i where i: "i < length ts" and x: "x \<in> vars_term (ts ! i)" unfolding set_conv_nth by auto
      from ind[OF i] \<sigma>2[OF i] x show "\<sigma>2 x \<in> ta_res TA (\<tau> x)" by auto
    qed
  next
    { 
      fix i
      assume i: "i < length ts"
      have id: "map_vars_term \<sigma>2 (ts ! i) = map_vars_term (\<sigma> i) (ts ! i)" 
        by (rule map_vars_term_vars_term, insert \<sigma>2[OF i], auto)
      from ind[OF i, THEN conjunct1] 
      have "qs ! i \<in> ta_res TA (map_vars_term \<sigma>2 (ts ! i))" unfolding id .
    } note main = this
    have "q \<in> ta_res TA (Fun f (map (map_vars_term \<sigma>2) ts))"
      by (unfold ta_res.simps, rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ qs], intro conjI, simp, rule rule, rule q, simp add: len, simp add: main)
    then show "q \<in> ta_res TA (map_vars_term \<sigma>2 (Fun f ts))" by auto
  qed
qed

(* decomposing substitutions: deterministic case *)
lemma ta_res_subst_det: fixes \<tau> TA
  defines "\<sigma> \<equiv> (\<lambda> x. SOME q. q \<in> ta_res TA (\<tau> x))"
  assumes det: "ta_det TA"
  and q: "q \<in> ta_res TA (t \<cdot> \<tau>)"
  shows "q \<in> ta_res TA (map_vars_term \<sigma> t) \<and> (\<forall> x \<in> vars_term t. \<sigma> x \<in> ta_res TA (\<tau> x))"
using q
proof (induct t arbitrary: q)
  case (Var x)
  then have "q \<in> ta_res TA (\<tau> x)" by auto
  then have tau: "\<sigma> x \<in> ta_res TA (\<tau> x)" unfolding \<sigma>_def by (rule someI)
  from det this Var have "q = \<sigma> x" by auto
  with tau show ?case by auto
next
  case (Fun f ts)
  from Fun(2)
  obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs = length ts"
    and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i \<cdot> \<tau>)"
    and q: "(q',q) \<in> (ta_eps TA)^*"
    by auto
  {
    fix i
    assume i: "i < length ts" 
    from i have mem: "ts ! i \<in> set ts" by simp
    note Fun(1)[OF mem rec[OF i]]
  }
  then have
    ind: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (map_vars_term \<sigma> (ts ! i)) \<and> 
             (\<forall> x \<in> vars_term (ts ! i). \<sigma> x \<in> ta_res TA (\<tau> x))"
    by auto
  show ?case
  proof (intro conjI)
    show "\<forall> x \<in> vars_term (Fun f ts). \<sigma> x \<in> ta_res TA (\<tau> x)"
    proof
      fix x
      assume "x \<in> vars_term (Fun f ts)"
      then obtain t where "t \<in> set ts" and "x \<in> vars_term t" by auto
      then obtain i where i: "i < length ts" and x: "x \<in> vars_term (ts ! i)" unfolding set_conv_nth by auto
      from ind[OF i] x show "\<sigma> x \<in> ta_res TA (\<tau> x)" by auto
    qed
  next
    from ind have main: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (map_vars_term \<sigma> (ts ! i))" ..
    have "q \<in> ta_res TA (Fun f (map (map_vars_term \<sigma>) ts))"
      by (unfold ta_res.simps, rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ qs], 
        intro conjI, simp, rule rule, rule q, simp add: len, simp add: main)
    then show "q \<in> ta_res TA (map_vars_term \<sigma> (Fun f ts))" by auto
  qed
qed

lemma ta_res_subst_linear_det: 
  assumes ld: "linear_term t \<or> ta_det TA"
  and q: "q \<in> ta_res TA (t \<cdot> \<tau>)"
  shows "\<exists> \<sigma>. q \<in> ta_res TA (map_vars_term \<sigma> t) \<and> (\<forall> x \<in> vars_term t. \<sigma> x \<in> ta_res TA (\<tau> x))"
  using ld
proof 
  assume "linear_term t"
  from ta_res_subst_linear[OF this q] show ?thesis .
next
  assume "ta_det TA"
  from ta_res_subst_det[OF this q] show ?thesis by - (rule exI)
qed

(* decomposing filling of multihole contexts *)
lemma ta_res_fill_holes: assumes "q \<in> ta_res TA (fill_holes C ts)"
  and len: "num_holes C = length ts"
  shows "\<exists> qs. length qs = length ts \<and> (\<forall> i. i < length ts \<longrightarrow> qs ! i \<in> ta_res TA (ts ! i)) 
    \<and> q \<in> ta_res TA (fill_holes C (map Var qs))"
  using assms
proof (induct C arbitrary: ts q)
  case (MHole ts q)
  then show ?case by (intro exI[of _ "[q]"], cases ts, auto)
next
  case (MFun f Cs ts q)
  note conv = partition_holes_fill_holes_conv
  from MFun(2)[unfolded conv]
  obtain p ps where rule: "(f ps \<rightarrow> p) \<in> ta_rules TA"
     and eps: "(p, q) \<in> (ta_eps TA)\<^sup>*"
     and len: "length ps = length Cs" 
     and rec: "\<And> i. i<length Cs \<Longrightarrow> ps ! i \<in> ta_res TA ((fill_holes (Cs ! i) (partition_holes ts Cs ! i)))" by auto
  from MFun(3) have len2: "sum_list (map num_holes Cs) = length ts" by simp
  let ?p = "\<lambda> qs i. length qs = length (partition_holes ts Cs ! i) \<and>
       (\<forall>ia<length (partition_holes ts Cs ! i). qs ! ia \<in> ta_res TA (partition_holes ts Cs ! i ! ia)) \<and>
       ps ! i \<in> ta_res TA (fill_holes (Cs ! i) (map Var qs))"
  {
    fix i
    assume i: "i < length Cs"
    from length_partition_holes_nth [OF len2 i]
    have nh: "num_holes (Cs ! i) = length (partition_holes ts Cs ! i)" by simp
  } note nh = this
  {
    fix i
    assume i: "i < length Cs"
    from i have "Cs ! i \<in> set Cs" by auto
    from MFun(1)[OF this rec[OF i] nh[OF i]] have "\<exists> qs. ?p qs i" .
  }
  then have "\<forall> i. \<exists> qs. i < length Cs \<longrightarrow> ?p qs i" by blast
  from choice[OF this] obtain qs where IH: "\<And> i. i < length Cs \<Longrightarrow> ?p (qs i) i" by blast
  let ?qs = "map qs [0 ..< length Cs]"
  define qs' where "qs' = concat ?qs"
  have id: "partition_holes (concat ?qs) Cs = ?qs"
    by (rule partition_holes_concat_id, insert nh IH, auto)
  show ?case unfolding conv
  proof (intro exI conjI allI impI)    
    show "length qs' = length ts" unfolding len2[symmetric] qs'_def length_concat map_map
      by (rule arg_cong[where f = sum_list], rule nth_equalityI, insert IH nh, auto)
    fix j
    assume j: "j < length ts"
    have ts: "concat (partition_holes ts Cs) = ts" using len2 by simp
    with j have "j < length (concat (partition_holes ts Cs))" by auto
    note index = nth_concat_two_lists[OF this, of ?qs, unfolded ts length_partition_holes, folded qs'_def]
    have "length ?qs = length Cs" by simp
    note index = index[OF this]
    {
      fix i
      assume i: "i < length Cs"
      have "length (?qs ! i) = length (partition_holes ts Cs ! i)"
      using IH[OF i] i by simp
    }
    from index[OF this]
    obtain i k where i: "i < length Cs" and
      k: "k < length (partition_holes ts Cs ! i)" and tsj: "ts ! j = partition_holes ts Cs ! i ! k"
      and qsj: "qs' ! j = ?qs ! i ! k" by blast
    from IH[OF i] k tsj have res: "qs i ! k \<in> ta_res TA (ts ! j)" by simp
    also have "qs i ! k = qs' ! j" unfolding qsj using i by simp
    finally show "qs' ! j \<in> ta_res TA (ts ! j)" .
  next
    show "q \<in> ta_res TA (Fun f (map (\<lambda>i. fill_holes (Cs ! i) (partition_holes (map Var qs') Cs ! i)) [0..<length Cs]))"
    proof (simp, intro exI conjI, rule rule, rule eps, rule len, intro allI impI)
      fix i
      assume i: "i < length Cs"
      from IH[OF this] have "ps ! i \<in> ta_res TA (fill_holes (Cs ! i) (map Var (qs i)))" by simp
      also have "fill_holes (Cs ! i) (map Var (qs i)) = fill_holes (Cs ! i) (partition_holes (map Var qs') Cs ! i)"
        unfolding map_partition_holes_nth [OF i, symmetric] unfolding qs'_def
      proof (rule arg_cong[where f = "\<lambda> qs. fill_holes (Cs ! i) (map Var qs)"], rule sym)
        have id: "partition_holes (concat (map qs [0..<length Cs])) Cs = map qs [0..<length Cs]"
          by (rule partition_holes_concat_id, insert nh IH, auto)
        show "partition_holes (concat (map qs [0..<length Cs])) Cs ! i = qs i" unfolding id using i nh by auto
      qed
      finally show "ps ! i \<in> ta_res TA (fill_holes (Cs ! i) (partition_holes (map Var qs') Cs ! i))" .
    qed
  qed
qed simp

(* decomposing filling of contexts *)
lemma ta_res_ctxt_decompose: assumes "q \<in> ta_res TA (C \<langle> t \<rangle>)"
  shows "\<exists> p . p \<in> ta_res TA t \<and> q \<in> ta_res TA (C \<langle> Var p \<rangle>)"
proof -
  note mctxt = eqfE[OF mctxt_of_ctxt[of C]]
  from ta_res_fill_holes[OF assms[unfolded mctxt(1)] mctxt(2)]
  obtain ps where "length ps = Suc 0"
     and res: "ps ! 0 \<in> ta_res TA t"
          "q \<in> ta_res TA (fill_holes (mctxt_of_ctxt C) (map Var ps))" 
        (is "_ \<in> ta_res _ (fill_holes _ ?map)")
     by auto
  then obtain p where id: "ps ! 0 = p" "?map = [Var p]" by (cases ps, auto)
  from res[unfolded id, folded mctxt(1)]
  show ?thesis by auto
qed

(* compose filling of multihole contexts *)
lemma fill_holes_ta_res:
  assumes "length ss = num_holes C" "length qs = num_holes C"
    "\<And>i. i < num_holes C \<Longrightarrow> qs ! i \<in> ta_res \<A> (ss ! i)"
    "q \<in> ta_res \<A> (fill_holes C (map Var qs))"
  shows "q \<in> ta_res \<A> (fill_holes C ss)"
  using assms(1,2)[symmetric] assms(3,4)
proof (induct C ss qs arbitrary: q rule: fill_holes_induct2)
  case (MFun f Cs ss qs)
  { fix i q assume i: "i < length Cs"
      "q \<in> ta_res \<A> (fill_holes (Cs ! i) (partition_holes (map Var qs) Cs ! i))"
    then have "q \<in> ta_res \<A> (fill_holes (Cs ! i) (partition_holes ss Cs ! i))"
      by (smt MFun.hyps MFun.prems(1) concat_partition_by length_map length_partition_by_nth
        length_partition_holes_nth map_partition_holes_nth num_holes.simps(3) partition_by_nth_nth)
  }
  then show ?case using MFun(1,2,5) by auto meson
qed (auto intro: ta_res_eps)

subsection \<open>An algorithm for tree automata matching\<close>

(* ta_match computes (a usually small) subset of those state-substitutions
  that have to be considered for some left-hand side *)
fun ta_match :: "('q,'f)ta \<Rightarrow> 'q set \<Rightarrow> ('f,'v)term \<Rightarrow> 'q set \<Rightarrow> ('v \<times> 'q)list set"
  where "ta_match TA Qsig (Var x)  Q = { [(x,q')] | q'. q' \<in> Qsig \<and> (\<exists> q \<in> Q. (q',q) \<in> (ta_eps TA)^*)}"
   | "ta_match TA Qsig (Fun f ts) Q = { concat \<sigma>s | \<sigma>s qs q' q. 
          (f qs \<rightarrow> q') \<in> ta_rules TA \<and> 
          q \<in> Q \<and>
          (q',q) \<in> (ta_eps TA)^* \<and> 
          length qs = length ts \<and>
          length \<sigma>s = length ts \<and>
          (\<forall> i < length ts. \<sigma>s ! i \<in> ta_match TA Qsig (ts ! i) {qs ! i}) }"

lemma ta_match_vars_term: 
  "\<sigma> \<in> ta_match TA Qsig t Q \<Longrightarrow> set (map fst \<sigma>) = vars_term t \<and> set (map snd \<sigma>) \<subseteq> Qsig"
proof (induct t arbitrary: \<sigma> Q)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  from Fun(2) obtain \<sigma>s qs
    where \<sigma>: "\<sigma> = concat \<sigma>s" and len: "length \<sigma>s = length ts"
    and rec: "\<And> i. i<length ts \<Longrightarrow> \<sigma>s ! i \<in> ta_match TA Qsig (ts ! i) {qs ! i}" by auto
  {
    fix i
    assume i: "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    from Fun(1)[OF this rec[OF i]] have "set (map fst (\<sigma>s ! i)) = vars_term (ts ! i) \<and> set (map snd (\<sigma>s ! i)) \<subseteq> Qsig" by auto
  } note \<sigma>s = this
  {
    fix x
    have "(x \<in> set (map fst \<sigma>)) = (\<exists> i. i < length ts \<and> x \<in> set (map fst (\<sigma>s ! i)))"
      unfolding \<sigma> set_map set_concat unfolding set_conv_nth[of \<sigma>s] len by force
    also have "\<dots> = (\<exists> i. i < length ts \<and> x \<in> vars_term (ts ! i))" using \<sigma>s by auto
    also have "\<dots> = (x \<in> vars_term (Fun f ts))" by (auto simp: set_conv_nth)
    finally have "(x \<in> set (map fst \<sigma>)) = (x \<in> vars_term (Fun f ts))" by auto
  }
  moreover
  {
    fix x
    have "(x \<in> set (map snd \<sigma>)) = (\<exists> i. i < length ts \<and> x \<in> set (map snd (\<sigma>s ! i)))"
      unfolding \<sigma> set_map set_concat unfolding set_conv_nth[of \<sigma>s] len by force
    also have "\<dots> \<longrightarrow> (\<exists> i. i < length ts \<and> x \<in> Qsig)" using \<sigma>s by auto
    finally have "x \<in> set (map snd \<sigma>) \<longrightarrow> x \<in> Qsig" by auto
  }
  ultimately show ?case by auto
qed

(* whenever a state is reachable via some substitution \<tau>, then
   there is an equivalent one (\<sigma>) that is computed by ta_match *)
lemma ta_match: 
  assumes "q \<in> ta_res TA (map_vars_term \<tau> t) \<inter> Q" "\<tau> ` vars_term t \<subseteq> Qsig"
                shows "\<exists> \<sigma> \<in> ta_match TA Qsig t Q. (\<forall> x \<in> vars_term t. \<tau> x = fun_of \<sigma> x)"
  using assms
proof (induct t arbitrary: q Q)
  case (Var x)
  then show ?case by (force simp: fun_of_def)
next
  case (Fun f ts)
  from Fun(2)
  obtain q q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
    and Q: "q \<in> Q"
    and eps: "(q',q) \<in> (ta_eps TA)^*"
    and len: "length qs = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (map_vars_term \<tau> (ts ! i)) \<inter> {qs ! i}"
    by auto
  let ?p = "\<lambda> i \<sigma>. \<sigma> \<in> ta_match TA Qsig (ts ! i) {qs ! i} \<and> (\<forall> x \<in> vars_term (ts ! i). \<tau> x = fun_of \<sigma> x)" 
  {
    fix i
    assume i: "i < length ts"
    then have ti: "ts ! i \<in> set ts" by auto
    from Fun(3) ti have "\<tau> ` vars_term (ts ! i) \<subseteq> Qsig" by auto
    from Fun(1)[OF ti rec[OF i] this] 
    have "\<exists> \<sigma>. ?p i \<sigma>" by blast
  }
  then have "\<forall> i. \<exists> \<sigma>. i < length ts \<longrightarrow> ?p i \<sigma>" by auto
  from choice[OF this] obtain \<sigma>s where \<sigma>s: "\<And> i. i < length ts \<Longrightarrow> ?p i (\<sigma>s i)" by auto
  {
    fix i
    assume i: "i < length ts"
    from \<sigma>s[OF i] ta_match_vars_term[of _ TA Qsig "ts ! i"]
    have "set (map fst (\<sigma>s i)) = vars_term (ts ! i)" by auto
  } note \<sigma>s_vars = this
  let ?\<sigma>s = "map \<sigma>s [0 ..< length ts]"
  let ?xs = "\<lambda> i. set (map fst (\<sigma>s i))"
  define \<sigma> where "\<sigma> = concat ?\<sigma>s"
  have mem: "\<sigma> \<in> ta_match TA Qsig (Fun f ts) Q"
    unfolding ta_match.simps
    by (rule, intro exI conjI, unfold \<sigma>_def, 
    rule HOL.refl, rule rule, rule Q,
    insert len eps \<sigma>s, auto)
  show ?case
  proof (rule bexI[OF _ mem], intro conjI ballI)
    fix x 
    assume x: "x \<in> vars_term (Fun f ts)"
    then obtain t where "t \<in> set ts" and x: "x \<in> vars_term t" by auto    
    then obtain i where i: "i < length ts" and t: "t = ts ! i" 
      unfolding set_conv_nth by auto
    from \<sigma>s_vars[OF i] x[unfolded t] have x: "x \<in> ?xs i" by auto
    have "fun_of \<sigma> x = fun_of (\<sigma>s i) x" unfolding \<sigma>_def
    proof (rule fun_of_concat[OF _ i], rule x)
      fix i j
      assume i: "i < length ts" and j: "j < length ts" and xi: "x \<in> ?xs i" and xj: "x \<in> ?xs j"
      have "fun_of (\<sigma>s i) x = \<tau> x" using \<sigma>s[OF i] \<sigma>s_vars[OF i] xi i by auto 
      also have "... = fun_of (\<sigma>s j) x" using \<sigma>s[OF j] \<sigma>s_vars[OF j] xj j by auto 
      finally show "fun_of (\<sigma>s i) x = fun_of (\<sigma>s j) x" .
    qed
    also have "... = \<tau> x"
      using \<sigma>s[OF i] \<sigma>s_vars[OF i] x i by auto
    finally show "\<tau> x = fun_of \<sigma> x" by simp
  qed
qed

definition ta_match' :: "('q,'f)ta \<Rightarrow> 'q set \<Rightarrow> ('f,'v)term \<Rightarrow> ('v \<times> 'q)list set"
  where "ta_match' TA Q t = ta_match TA Q t Q"

(* whenever a state is reachable via some substitution \<tau>, then
   there is an equivalent one (\<sigma>) that is computed by ta_match *)
lemma ta_match': 
  assumes q: "q \<in> ta_res TA (map_vars_term \<tau> t)"
  and tau: "\<tau> ` vars_term t \<subseteq> ta_rhs_states TA"
  shows "\<exists> \<sigma> \<in> ta_match' TA (ta_rhs_states TA) t. (\<forall> x \<in> vars_term t. \<tau> x = fun_of \<sigma> x)"
proof -
  have "q \<in> ta_rhs_states TA" 
  proof (cases t)
    case (Fun f ts)
    then have "is_Fun (map_vars_term \<tau> t)" by (cases t, auto)
    from ta_rhs_states_res[OF this, of TA] q show ?thesis by auto
  next
    case (Var x)
    with tau q show ?thesis by (induct, auto simp: ta_rhs_states_def intro!: bexI)
  qed
  with q have "q \<in> ta_res TA (map_vars_term \<tau> t) \<inter> ta_rhs_states TA" by auto
  from ta_match[OF this tau] show ?thesis unfolding ta_match'_def by auto
qed

lemma ta_match'_vars_term: assumes "\<sigma> \<in> ta_match' TA Q t"
  shows "fun_of \<sigma> ` vars_term t \<subseteq> Q"
proof -
  from assms have "\<sigma> \<in> ta_match TA Q t Q" unfolding ta_match'_def .
  from ta_match_vars_term[OF this] have vars: "vars_term t = set (map fst \<sigma>)"
    and snd: "set (map snd \<sigma>) \<subseteq> Q" by auto
  {
    fix q
    assume "q \<in> fun_of \<sigma> ` vars_term t"
    with vars obtain x where x: "x \<in> set (map fst \<sigma>)" and q: "q = fun_of \<sigma> x" by auto
    from x obtain p where "map_of \<sigma> x = Some p" 
      by (cases "map_of \<sigma> x", insert map_of_eq_None_iff[of \<sigma>], auto)
    with q have "map_of \<sigma> x = Some q" by (simp add: fun_of_def)
    from map_of_SomeD[OF this]
    have "q \<in> snd ` set \<sigma>" by force
    with snd have "q \<in> Q" by auto
  }
  then show ?thesis by auto
qed

subsection \<open>Abstract algorithms to check compatibility for a single rule\<close>

(* state-compatibility for a rule,
   the restrictions on vars_term and \<sigma> are made to ensure that we will only
   have to test finitely many \<sigma>*)
definition rule_state_compatible :: "('q,'f)ta \<Rightarrow> 'q rel \<Rightarrow> ('f,'v)rule \<Rightarrow> bool"
where "rule_state_compatible TA rel \<equiv> \<lambda> (l,r). (\<forall> \<sigma>. (\<sigma> ` vars_term l \<subseteq> ta_rhs_states TA) \<longrightarrow> 
  ta_res TA (map_vars_term \<sigma> l) \<subseteq> rel^-1 `` ta_res TA (map_vars_term \<sigma> r))"
  
(* efficient algorithm to check compatibility *)
(* one might examine whether \<tau> in ta_match is always able to produce q,
   then one can ignore the precondition "q \<in> ta_res TA (Fun f ls \<cdot> \<tau>)" *)
fun rule_state_compatible_eff :: "('q,'f)ta \<Rightarrow> 'q set \<Rightarrow> 'q rel \<Rightarrow> ('f,'v)rule \<Rightarrow> bool"
where "rule_state_compatible_eff TA Q rel (l,r) = (\<forall> \<tau>.
  \<tau> \<in> ta_match' TA Q l \<longrightarrow>
  ta_res TA (map_vars_term (fun_of \<tau>) l) \<subseteq>
   rel^-1 `` ta_res TA (map_vars_term (fun_of \<tau>) r))"


lemma rule_state_compatible_eff: 
  assumes var: "vars_term l \<supseteq> vars_term r"
  and Q: "Q = (ta_rhs_states TA)"
  and compat: "rule_state_compatible_eff TA Q rel (l,r)"
  shows "rule_state_compatible TA rel (l,r)"
  unfolding rule_state_compatible_def split
proof (intro allI impI)
  fix \<sigma>
  assume \<sigma>: "\<sigma> ` vars_term l \<subseteq> ta_rhs_states TA"  
  show "ta_res TA (map_vars_term \<sigma> l) \<subseteq> rel^-1 `` ta_res TA (map_vars_term \<sigma> r)" (is "?rl \<subseteq> ?rr")
  proof
    fix q
    assume q: "q \<in> ta_res TA (map_vars_term \<sigma> l)"
    from ta_match'[OF this \<sigma>] obtain \<tau> where \<tau>: "\<tau> \<in> ta_match' TA Q l" and \<sigma>: "\<And> x. x \<in> vars_term l \<Longrightarrow> \<sigma> x = fun_of \<tau> x" 
      unfolding Q by auto
    have idl: "map_vars_term \<sigma> l = map_vars_term (fun_of \<tau>) l"
      by (rule map_vars_term_vars_term, insert \<sigma>, auto)
    have idr: "map_vars_term (fun_of \<tau>) r = map_vars_term \<sigma> r"
    proof (rule map_vars_term_vars_term)
        fix x
        assume "x \<in> vars_term r"
        with var have "x \<in> vars_term l" by auto
        with \<sigma> show "fun_of \<tau> x = \<sigma> x" by simp
    qed
    from compat[simplified, rule_format, OF \<tau>] q
    show "q \<in> rel\<inverse> `` ta_res TA (map_vars_term \<sigma> r)" unfolding idl idr by auto
  qed
qed

subsection \<open>Theorem 11: state-coherence and state-compatibility implies closed under rewriting\<close>

(* corresponds to Definition 8 in paper *)
definition state_coherent :: "('q,'f)ta \<Rightarrow> 'q rel \<Rightarrow> bool" where
  "state_coherent TA rel \<equiv> (rel `` ta_final TA \<subseteq> ta_final TA \<and> (\<forall> f qs q i qi. 
  (f qs \<rightarrow> q) \<in> ta_rules TA \<longrightarrow> i < length qs \<longrightarrow> (qs ! i, qi) \<in> rel \<longrightarrow> 
  (\<exists> q'. (f (qs[ i := qi]) \<rightarrow> q') \<in> ta_rules TA \<and> (q,q') \<in> rel))) \<and>
  (rel^-1 O ta_eps TA \<subseteq> (ta_eps TA)^* O rel^-1)"

lemma state_coherentE: "state_coherent TA rel \<Longrightarrow> 
  (f qs \<rightarrow> q) \<in> ta_rules TA \<Longrightarrow> i < length qs \<Longrightarrow> (qs ! i, qi) \<in> rel \<Longrightarrow>
  (\<exists> q'. (f (qs[ i := qi]) \<rightarrow> q') \<in> ta_rules TA \<and> (q,q') \<in> rel)"
  unfolding state_coherent_def by blast

lemma state_coherentE2: assumes "state_coherent TA rel"
  shows "rel `` ta_final TA \<subseteq> ta_final TA" and "(rel^-1 O ta_eps TA \<subseteq> (ta_eps TA)^* O rel^-1)"
  using assms unfolding state_coherent_def by blast+

(* corresponds to Definition 8 in paper *)
definition state_compatible :: "('q,'f)ta \<Rightarrow> 'q rel \<Rightarrow> ('f,'v)trs \<Rightarrow> bool"
where "state_compatible TA rel R \<equiv> \<forall> l r. (l,r) \<in> R \<longrightarrow> funas_term l \<subseteq> ta_syms TA 
  \<longrightarrow> rule_state_compatible TA rel (l,r)" 

lemma state_compatible_union: "state_compatible TA rel (R \<union> S) = (state_compatible TA rel R \<and> state_compatible TA rel S)"
  unfolding state_compatible_def by auto

lemma state_coherent_Id: "state_coherent TA Id" unfolding state_coherent_def by auto

lemma state_coherent_eps_trancl:
  assumes "state_coherent TA rel"
  shows "rel\<inverse> O (ta_eps TA)^* \<subseteq> (ta_eps TA)\<^sup>* O rel\<inverse>"
proof -
  {
    fix n
    have "rel^-1 O (ta_eps TA)^^n \<subseteq> (ta_eps TA)^* O rel^-1"
    proof (induct n)
      case (Suc n)
      have "rel\<inverse> O ta_eps TA ^^ Suc n = (rel\<inverse> O ta_eps TA ^^ n) O ta_eps TA" by auto
      also have "\<dots> \<subseteq> (ta_eps TA)^* O (rel^-1 O ta_eps TA)" using Suc by blast
      also have "\<dots> \<subseteq> (ta_eps TA)^* O (ta_eps TA)\<^sup>* O rel\<inverse>" using state_coherentE2[OF assms] by blast
      also have "\<dots> = (ta_eps TA)^* O rel^-1" by regexp
      finally show ?case .
    qed auto
  }
  then show ?thesis by fast
qed

lemma state_coherent_arg_rtrancl: 
  assumes coh: "state_coherent TA rel" 
  and rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
  and i: "i < length qs"
  and steps: "(qs ! i, qi) \<in> rel^*"
  shows "\<exists> q'. (f (qs[ i := qi]) \<rightarrow> q') \<in> ta_rules TA \<and> (q,q') \<in> rel^*"
proof -
  define p where "p = qs ! i"
  from i have "qs[ i := p] = qs" unfolding p_def by simp
  with rule have rule: "(f (qs [ i := p]) \<rightarrow> q) \<in> ta_rules TA" by simp
  from steps p_def have steps: "(p, qi) \<in> rel^*" by simp
  from steps show ?thesis
  proof (induct)
    case base
    show ?case using rule by auto
  next
    case (step r s)
    from step(3) obtain t where rule: "(f qs[i := r] \<rightarrow> t) \<in> ta_rules TA" and qt: "(q, t) \<in> rel\<^sup>*" by auto
    from state_coherentE[OF coh rule] step(2) i obtain u where 
      "(f (qs[i := r])[i := s] \<rightarrow> u) \<in> ta_rules TA" and rel: "(t, u) \<in> rel" by force+
    with qt show ?case by auto
  qed
qed    

lemma state_coherent_rtrancl: assumes cohe: "state_coherent TA rel"
  shows "state_coherent TA (rel^*)"
proof -
  let ?rel = "rel^*"
  note d = state_coherent_def
  note coh = cohe[unfolded d]
  from coh have "rel `` ta_final TA \<subseteq> ta_final TA" by auto
  then have final: "?rel `` ta_final TA \<subseteq> ta_final TA"
    by (metis Image_closed_trancl order_refl)
  from state_coherent_eps_trancl[OF cohe] have eps: "rel\<inverse> O (ta_eps TA)^* \<subseteq> (ta_eps TA)\<^sup>* O rel\<inverse>" by auto
  have eps: "?rel\<inverse> O ta_eps TA \<subseteq> (ta_eps TA)\<^sup>* O ?rel\<inverse>"
  proof
    fix q q'
    assume "(q,q') \<in> ?rel\<inverse> O ta_eps TA"
    then obtain q'' where "(q'',q) \<in> ?rel" and "(q'',q') \<in> ta_eps TA"  by auto
    then show "(q,q') \<in> (ta_eps TA)\<^sup>* O ?rel\<inverse>"
    proof (induct arbitrary: q' rule: rtrancl_induct)
      case (step q1 q2 q3)
      from step(3)[OF step(4)] obtain q5 where 15: "(q1, q5) \<in> (ta_eps TA)\<^sup>*"
        and 35: "(q3, q5) \<in> rel\<^sup>*" by auto
      from step(2) 15 have "(q2,q5) \<in> rel^-1 O (ta_eps TA)^*" by auto
      with eps obtain q6 where 26: "(q2,q6) \<in> (ta_eps TA)^*" and 56: "(q5,q6) \<in> rel" by auto 
      then show ?case using 35 by auto
    qed auto
  qed
  show ?thesis unfolding d
    by (rule conjI[OF conjI[OF final] eps], intro allI impI, rule state_coherent_arg_rtrancl[OF cohe], auto)
qed

lemma state_coherent_args: 
  assumes coh: "state_coherent TA rel"
  and rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
  and len: "length qs' = length qs"
  and rel: "\<And> i. i < length qs \<Longrightarrow> (qs ! i, qs' ! i) \<in> rel^*"
  shows "\<exists> q'. (f qs' \<rightarrow> q') \<in> ta_rules TA \<and> (q,q') \<in> rel^*"
proof -
  let ?p = "\<lambda> qs. \<exists> q'. (f qs \<rightarrow> q') \<in> ta_rules TA \<and> (q,q') \<in> rel^*"
  let ?r = "\<lambda> a b. (a,b) \<in> rel^*"
  have init: "?p qs" using rule by auto
  show ?thesis
  proof (rule parallel_list_update[where p = ?p and r = ?r, OF _ refl init len rel]) 
    fix qs' i y
    assume len: "length qs' = length qs"
    and i: "i < length qs"
    and rel: "(qs' ! i, y) \<in> rel\<^sup>*"
    and "\<exists>q'. (f qs' \<rightarrow> q') \<in> ta_rules TA \<and> (q, q') \<in> rel\<^sup>*"
    then obtain q' where rule: "(f qs' \<rightarrow> q') \<in> ta_rules TA" and qq': "(q, q') \<in> rel\<^sup>*" by auto
    from state_coherentE[OF state_coherent_rtrancl[OF coh], OF rule i[folded len] rel] qq'
    show "\<exists>q'. (f qs'[i := y] \<rightarrow> q') \<in> ta_rules TA \<and> (q, q') \<in> rel\<^sup>*" by auto
  qed
qed

lemma state_coherent_ctxt: assumes coh: "state_coherent TA rel" and rel: "(p,q) \<in> rel"
  shows "q' \<in> ta_res TA D\<langle>Var p\<rangle> \<Longrightarrow> \<exists> q''. (q', q'') \<in> rel \<and> q'' \<in> ta_res TA D\<langle>Var q\<rangle>"
proof (induct D arbitrary: q')
  case Hole
  then show ?case using rel state_coherent_eps_trancl[OF coh] by auto
next
  case (More f bef C aft q')
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  from More(2)[simplified] obtain q0 qs where
  rule: "(f qs \<rightarrow> q0) \<in> ta_rules TA" and
  eps: "(q0,q') \<in> (ta_eps TA)^*" and
  len: "length qs = ?n" and
  res: "\<And> i. i< ?n \<Longrightarrow>
           qs ! i \<in> (map (ta_res TA) bef @ ta_res TA C\<langle>Var p\<rangle> # map (ta_res TA) aft) ! i" by auto
  have i: "?i < ?n" by auto
  from res[of ?i] have "qs ! ?i \<in> ta_res TA C\<langle>Var p \<rangle>" by (simp add: nth_append) 
  from More(1)[OF this] obtain q'' where rel: "(qs ! ?i, q'') \<in> rel" and q'': "q'' \<in> ta_res TA C\<langle>Var q\<rangle>" by auto
  from state_coherentE[OF coh rule, unfolded len, OF i rel] obtain q3 where 
    rule: "(f qs[?i := q''] \<rightarrow> q3) \<in> ta_rules TA" and rel: "(q0, q3) \<in> rel" by auto
  from state_coherent_eps_trancl[OF coh] rel eps 
    obtain q1 where eps: "(q3,q1) \<in> (ta_eps TA)^*" and rel: "(q',q1) \<in> rel" by auto
  show ?case
  proof (intro exI conjI, rule rel, simp, intro exI conjI allI impI, rule rule, rule eps)
    fix i
    assume i: "i < ?n"
    show "qs[length bef := q''] ! i \<in> (map (ta_res TA) bef @ ta_res TA C\<langle>Var q\<rangle> # map (ta_res TA) aft) ! i"
      using res[OF i] q'' len by (cases "i = ?i", auto simp: nth_append)
  qed (auto simp: len)
qed
  
lemma state_coherent_fill_holes_rel: assumes coh: "state_coherent TA rel"
  and "q \<in> ta_res TA (fill_holes C (map Var qs))"
  and rels: "\<And> i. i < length qs \<Longrightarrow> (qs ! i, qs' ! i) \<in> rel^*"
  and nh: "num_holes C = length qs"
  and len: "length qs' = length qs"
  shows "\<exists> q'. (q,q') \<in> rel^* \<and> q' \<in> ta_res TA (fill_holes C (map Var qs'))"
proof -
  {
    fix i
    assume "i \<le> length qs"
    then have "\<exists> q'. (q,q') \<in> rel^* \<and> q' \<in> ta_res TA (fill_holes C (map Var (take i qs' @ drop i qs)))"
    proof (induct i)
      case 0
      show ?case using assms by auto 
    next
      case (Suc i)
      then have i: "i < length qs" and i': "i \<le> length qs" by auto
      let ?bef = "take i qs'"
      let ?aft = "drop (Suc i) qs"
      from Suc(1)[OF i'] obtain q' where rel: "(q, q') \<in> rel\<^sup>*"
        and q': "q' \<in> ta_res TA (fill_holes C (map Var (?bef @ drop i qs)))" by auto
      from i have one: "?bef @ drop i qs = ?bef @ qs ! i # ?aft" by (metis Cons_nth_drop_Suc)
      from i len have two: "take (Suc i) qs' @ ?aft = (take i qs' @ [qs' ! i]) @ ?aft" 
        by (metis take_Suc_conv_app_nth)      
      then have two: "take (Suc i) qs' @ ?aft = ?bef @ qs' ! i # ?aft" by simp
      have nh: "num_holes C = Suc (length ?bef + length ?aft)" unfolding nh using len i by simp
      from fill_holes_ctxt_main[of C "map Var ?bef" "map Var ?aft", unfolded nh]
      obtain D where id: "\<And> s. fill_holes C (map Var (?bef @ s # ?aft)) = D \<langle>Var s\<rangle>" by auto
      from q'[unfolded one id] have "q' \<in> ta_res TA D\<langle>Var (qs ! i)\<rangle>" by simp
      from state_coherent_ctxt[OF state_coherent_rtrancl[OF coh] rels[OF i] this] obtain q'' where
        rel2: "(q', q'') \<in> rel\<^sup>*" and res: "q'' \<in> ta_res TA D\<langle>Var (qs' ! i)\<rangle>" by auto
      from rel rel2 have rel: "(q,q'') \<in> rel^*" by auto
      from rel res show ?case unfolding id two by auto
    qed
  }
  from this[of "length qs"] show ?thesis using len by simp
qed


context
  fixes TA :: "('q,'f)ta"
  and rel :: "'q rel"
  and R :: "('f,'v)trs"
  assumes comp: "state_compatible TA rel R"
  and coh: "state_coherent TA rel"
  and ll_or_det: "left_linear_trs R \<or> ta_det TA"
  and wf_trs: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin
(* major lemma, corresponds to proof of Theorem 11 *)
lemma state_compatible_res: 
  assumes step: "(s, t) \<in> rstep R"
  and ground: "ground s"
  and "p \<in> ta_res TA (adapt_vars s)"
  shows "\<exists> p'. p' \<in> ta_res TA (adapt_vars t) \<and> (p,p') \<in> rel"
  using assms
proof (induct)
  case (IH C \<tau> l r)
  note av = adapt_vars_def
  let ?C = "adapt_vars_ctxt C :: ('f,'q)ctxt"
  let ?\<tau> = "\<lambda> x. adapt_vars (\<tau> x)"
  from ta_res_ctxt_decompose[OF IH(3)[unfolded av map_vars_term_ctxt_commute, folded av]]
  obtain q where q: "q \<in> ta_res TA (l \<cdot> ?\<tau>)" and p: "p \<in> ta_res TA ?C\<langle>Var q\<rangle>" by (auto simp add: adapt_vars_ctxt_def)
  from ll_or_det IH have ground: "ground (l \<cdot> \<tau>)" and lin: "linear_term l \<or> ta_det TA"
    unfolding left_linear_trs_def by auto
  from ta_res_subst_linear_det[OF lin q] obtain \<sigma> where
    q: "q \<in> ta_res TA (map_vars_term \<sigma> l)" and 
    vars: "\<forall> x \<in> vars_term l. \<sigma> x \<in> ta_res TA (?\<tau> x)" by auto
  from ta_syms_res[OF q]
  have "funas_term l \<subseteq> ta_syms TA" by auto
  with comp[unfolded state_compatible_def] IH(1) have
    comp: "rule_state_compatible TA rel (l,r)" by auto
  have "\<sigma> ` vars_term l \<subseteq> ta_rhs_states TA" 
  proof 
    fix q
    assume "q \<in> \<sigma> ` vars_term l"
    then obtain x where x: "x \<in> vars_term l" and q: "q = \<sigma> x" by auto
    with vars have q: "q \<in> ta_res TA (?\<tau> x)" by auto
    from ground x have "ground (?\<tau> x)" by auto
    then have "is_Fun (?\<tau> x)"
      by (metis ground.simps(1) is_VarE)
    from ta_rhs_states_res[OF this, of TA] q show "q \<in> ta_rhs_states TA" by auto
  qed
  with comp[unfolded rule_state_compatible_def] q
  have q: "q \<in> rel^-1 `` ta_res TA (map_vars_term \<sigma> r)" by auto
  then obtain q' where qq': "(q,q') \<in> rel" and q': "q' \<in> ta_res TA (map_vars_term \<sigma> r)" by auto
  from ta_res_subst[OF _ q'] wf_trs[OF IH(1)] vars have q': "q' \<in> ta_res TA (adapt_vars (r \<cdot> \<tau>))" by force
  from state_coherent_ctxt[OF coh qq' p] obtain p' where 
    rel: "(p, p') \<in> rel" and p': "p' \<in> ta_res TA ?C\<langle>Var q'\<rangle>" by auto
  from ta_res_ctxt[OF q' p'] rel show ?case unfolding av map_vars_term_ctxt_commute by (auto simp add: adapt_vars_ctxt_def)
qed

(* Theorem 11 in paper: soundness *)
lemma state_compatible_lang: "rstep R `` ta_lang TA \<subseteq> ta_lang TA"
proof 
  fix t
  assume "t \<in> rstep R `` ta_lang TA"
  then obtain s where s: "s \<in> ta_lang TA" and step: "(s,t) \<in> rstep R" by auto
  from ta_langE2[OF s] obtain q where
    g: "ground s" and fin: "q \<in> ta_final TA" and res: "q \<in> ta_res TA (adapt_vars s)" .
  from rstep_ground[OF wf_trs g step] have gt: "ground t" .
  from state_compatible_res[OF step g] res obtain q' 
    where qq': "(q,q') \<in> rel" and res: "q' \<in> ta_res TA (adapt_vars t)" by auto
  from state_coherentE2[OF coh] fin qq' have fin: "q' \<in> ta_final TA" by auto
  from ta_langI2[OF gt fin res]
  show "t \<in> ta_lang TA" .
qed

(* Theorem 11 applied to have reachability *)
lemma state_compatible: assumes L: "L \<subseteq> ta_lang TA"
  shows "{t | s. s \<in> L \<and> (s,t) \<in> (rstep R)^*} \<subseteq> ta_lang TA"
  by (rule closed_imp_rtrancl_closed[OF L state_compatible_lang])
end

subsection \<open>Theorem 13: Completeness of state-compatibility and state-coherence\<close>

lemma ta_trimE: assumes trim: "ta_trim TA"
  and rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
  and q': "q' \<in> set (q # qs)"
  shows "q' \<in> ta_reachable TA \<and> q' \<in> ta_productive TA"
proof -
  from q' rule have "q' \<in> ta_states TA" unfolding ta_states_def by (force simp: r_states_def)
  with trim show ?thesis unfolding ta_trim_def by auto
qed

(* we assume that there is some det. trim automaton TA and arbitrary TRS R such that 
   TA is closed under R *)         
locale ta_trim_det_closed = 
  fixes TA :: "('q,'f)ta"
  and R :: "('f,'v)trs"
  assumes det: "ta_det TA"
  and trim: "ta_trim TA"  
  and closedImp: "rstep R `` ta_lang TA \<subseteq> ta_lang TA"
begin

lemma closed: "s \<in> ta_lang TA \<Longrightarrow> (s,t) \<in> rstep R \<Longrightarrow> t \<in> ta_lang TA" using closedImp by auto
lemma [simp]: "ta_eps TA = {}" using det[unfolded ta_det_def] by auto

lemma ta_productiveE: assumes "q \<in> ta_productive TA"
  obtains q' C where "q' \<in> ta_res TA (C\<langle>Var q\<rangle>)" "q' \<in> ta_final TA" "ground_ctxt C"
proof -
  from assms[unfolded ta_productive_def] obtain q' C where 
    q': "q' \<in> ta_res TA (C\<langle>Var q\<rangle>)" and fin: "q' \<in> ta_final TA" by auto
  from q' have "\<exists> C. ground_ctxt C \<and> q' \<in> ta_res TA (C\<langle>Var q\<rangle>)"
  proof (induct C arbitrary: q')
    case Hole
    then show ?case by (intro exI[of _ Hole], auto)
  next
    case (More f bef D aft)
    let ?i = "length bef"
    let ?n = "Suc (?i + length aft)"
    from More(2)
    obtain qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA"
      and len: "length qs = ?n"
      and rec: "\<And> i. i < ?n \<Longrightarrow> qs ! i \<in> (map (ta_res TA) bef @ ta_res TA D\<langle>Var q\<rangle> # map (ta_res TA) aft) ! i" by auto
    from rec[of ?i] have "qs ! ?i \<in> ta_res TA D\<langle>Var q\<rangle>" by (auto simp: nth_append)
    from More(1)[OF this] obtain D where gD: "ground_ctxt D" and mem: "qs ! ?i \<in> ta_res TA D\<langle>Var q\<rangle>" by auto
    let ?p = "\<lambda> q t. q \<in> ta_res TA t \<and> ground t"
    define ts where "ts \<equiv> \<lambda> q. SOME t. ?p q t"
    {
      fix p
      assume "p \<in> set qs"
      then have "p \<in> r_states (f qs \<rightarrow> q')" unfolding r_states_def by auto
      with rule have "p \<in> ta_states TA" unfolding ta_states_def by auto
      with trim have "p \<in> ta_reachable TA" unfolding ta_trim_def by auto
      from ta_reachableE[OF this] obtain t where "?p p t" by blast
      then have "?p p (ts p)" unfolding ts_def by (rule someI)
    } note ts = this
    let ?ts = "map ts qs"
    let ?C = "More f (take ?i ?ts) D (drop (Suc ?i) ?ts)"
    have gC: "ground_ctxt ?C" using gD ts 
      set_take_subset[of ?i qs] set_drop_subset[of "Suc ?i" qs]
      by (auto simp: take_map drop_map)
    have [simp]: "min (length qs) ?i = ?i" using len by auto
    have [simp]: "Suc (?i + (length qs - Suc ?i)) = length qs" unfolding len by simp
    show ?case
    proof (intro exI conjI, rule gC, simp, intro exI conjI, rule rule, simp add: len, intro allI impI)
      fix j
      assume j: "j < length qs"
      show "qs ! j \<in> (map (ta_res TA) (take ?i ?ts) @ ta_res TA D\<langle>Var q\<rangle> # map (ta_res TA) (drop (Suc ?i) ?ts)) ! j"
         (is "_ \<in> ?list ! j")
      proof (cases "j = ?i")
        case True
        then show ?thesis using mem by (simp add: nth_append)
      next
        case False
        from False j have id: "?list ! j = ta_res TA (ts (qs ! j))"
          by (simp add: nth_append)
        from ts[of "qs ! j"] j show ?thesis unfolding id by auto
      qed
    qed
  qed
  then obtain C where gC: "ground_ctxt C" and q': "q' \<in> ta_res TA C \<langle>Var q\<rangle>" by blast
  assume *: "\<And>q' C. q' \<in> ta_res TA C\<langle>Var q\<rangle> \<Longrightarrow> q' \<in> ta_final TA \<Longrightarrow> ground_ctxt C \<Longrightarrow> thesis"
  show thesis
    by (rule *[OF q' fin gC])
qed

definition rel where "rel \<equiv> { (q,q'). \<exists> t t'. ground t \<and> ground t' \<and> q \<in> ta_res TA t \<and> (adapt_vars t,adapt_vars t') \<in> rstep R \<and> q' \<in> ta_res TA t'}"

lemma relE: assumes "(q,q') \<in> rel"
  obtains t t' where "ground t" "ground t'" "q \<in> ta_res TA t" "q' \<in> ta_res TA t'" "(adapt_vars t,adapt_vars t') \<in> rstep R"
  using assms[unfolded rel_def] by blast

lemma relI: "ground t \<Longrightarrow> ground t' \<Longrightarrow> q \<in> ta_res TA t \<Longrightarrow> q' \<in> ta_res TA t' \<Longrightarrow> (adapt_vars t,adapt_vars t') \<in> rstep R \<Longrightarrow> (q,q') \<in> rel"
  unfolding rel_def by blast

lemma compatible: "state_compatible TA rel R"
  unfolding state_compatible_def
proof (clarify)
  fix l r
  assume lr: "(l,r) \<in> R"
  show "rule_state_compatible TA rel (l,r)"
    unfolding rule_state_compatible_def
  proof (clarify)
    fix \<sigma> q 
    assume sigma: "\<sigma> ` vars_term l \<subseteq> ta_rhs_states TA"
      and ql: "q \<in> ta_res TA (map_vars_term \<sigma> l)"
    define \<tau> where "\<tau> \<equiv> \<lambda> x. (if x \<in> vars_term l then (SOME t. ground t \<and> \<sigma> x \<in> ta_res TA t) else Var q)"
    {
      fix x
      assume x: "x \<in> vars_term l"
      with sigma have "\<sigma> x \<in> ta_rhs_states TA" by auto
      with ta_rhs_states_subset_states[of TA] have mem: "\<sigma> x \<in> ta_states TA" by auto
      from trim[unfolded ta_trim_def, rule_format, OF mem]
      have "\<sigma> x \<in> ta_reachable TA" ..
      from ta_reachableE[OF this] have "\<exists> t. ground t \<and> \<sigma> x \<in> ta_res TA t" by blast
      from someI_ex[OF this] have "ground (\<tau> x) \<and> \<sigma> x \<in> ta_res TA (\<tau> x)" unfolding \<tau>_def using x by auto
    } note tau = this
    have "q \<in> ta_rhs_states TA"
    proof (cases l)
      case (Fun f ls)
      then have "is_Fun (map_vars_term \<sigma> l)" by simp
      from ta_rhs_states_res[OF this, of TA] ql show ?thesis by auto
    qed (insert ql sigma, auto)
    with ta_rhs_states_subset_states[of TA] have q: "q \<in> ta_states TA" by blast
    from trim[unfolded ta_trim_def, rule_format, OF this] have "q \<in> ta_productive TA" ..
    from ta_productiveE[OF this] obtain C p where 
      fin: "p \<in> ta_final TA" and pq: "p \<in> ta_res TA (C \<langle>Var q\<rangle>)" and C: "ground_ctxt C" .
    let ?t = "C \<langle> l \<cdot> \<tau> \<rangle>"
    let ?t' = "C \<langle> r \<cdot> \<tau> \<rangle>"
    let ?a = "adapt_vars :: ('f,'q)term \<Rightarrow> ('f,'v)term"
    let ?at = "?a ?t"
    let ?at' = "?a ?t'"
    have step: "(?at, ?at') \<in> rstep R" using lr by auto
    have gt: "ground ?t" using C tau by auto
    have gl: "ground (l \<cdot> \<tau>)" using tau by auto
    have qlt: "q \<in> ta_res TA (l \<cdot> \<tau>)"
      by (rule ta_res_subst[OF _ ql], insert tau, auto)
    have "p \<in> ta_res TA ?t"
      by (rule ta_res_ctxt[OF qlt pq])
    then have tA: "?at \<in> ta_lang TA" unfolding ta_lang_def using fin gt by blast
    from closed[OF tA step] have t'A: "?at' \<in> ta_lang TA" .
    from ta_langE3[OF this] obtain p' where gr: "ground (r \<cdot> \<tau>)" and p': "p' \<in> ta_res TA ?t'" by auto
    from ta_res_ctxt_decompose[OF p'] obtain q' where q': "q' \<in> ta_res TA (r \<cdot> \<tau>)" by auto
    have lr: "(?a (l \<cdot> \<tau>), ?a (r \<cdot> \<tau>)) \<in> rstep R" using lr by auto
    have qq': "(q,q') \<in> rel" 
      by (rule relI[OF gl gr qlt q' lr])
    from ta_res_subst_det[OF det q']
      obtain \<sigma>' where q': "q' \<in> ta_res TA (map_vars_term \<sigma>' r)" and 
      sigma': "\<And> x. x\<in>vars_term r \<Longrightarrow> \<sigma>' x \<in> ta_res TA (\<tau> x)" by blast
    have "map_vars_term \<sigma>' r = map_vars_term \<sigma> r" 
    proof (rule map_vars_term_vars_term)
      fix x
      assume xr: "x \<in> vars_term r"
      have xl: "x \<in> vars_term l"
      proof (rule ccontr)
        assume "x \<notin> vars_term l"
        then have "\<tau> x = Var q" unfolding \<tau>_def by auto
        with xr gr show False by auto
      qed      
      from sigma'[OF xr] have 1: "\<sigma>' x \<in> ta_res TA (\<tau> x)" by auto
      from tau[OF xl] have 2: "\<sigma> x \<in> ta_res TA (\<tau> x)" by auto
      from ta_detE[OF det 1 2] show "\<sigma>' x = \<sigma> x" .
    qed
    then have q': "q' \<in> ta_res TA (map_vars_term \<sigma> r)" using q' by simp    
    then show "q \<in> rel\<inverse> `` ta_res TA (map_vars_term \<sigma> r)" using qq' by auto
  qed
qed

lemma coherent: "state_coherent TA rel"
  unfolding state_coherent_def
proof (intro conjI allI impI, rule)
  fix q'
  assume "q' \<in> rel `` ta_final TA"
  then obtain q where qq': "(q,q') \<in> rel" and qf: "q \<in> ta_final TA" by auto
  let ?a = "adapt_vars :: ('f,'q)term \<Rightarrow> ('f,'v)term"
  from relE[OF qq'] obtain t t' where 
    gt: "ground t" and gt': "ground t'" 
    and q: "q \<in> ta_res TA t" and q': "q' \<in> ta_res TA t'" 
    and step: "(?a t, ?a t') \<in> rstep R" by auto
  from q gt qf have "?a t \<in> ta_lang TA" unfolding ta_lang_def by auto
  from closed[OF this step] have "?a t' \<in> ta_lang TA" .
  from ta_langE2[OF this] obtain q'' where q'': "q'' \<in> ta_res TA t'" and qf'': "q'' \<in> ta_final TA" by auto
  from ta_detE[OF det q'' q'] qf''
  show "q' \<in> ta_final TA" by simp
next
  fix f qs q i qi'
  assume rule: "(f qs \<rightarrow> q) \<in> ta_rules TA" and
    i: "i < length qs" and
    rel: "(qs ! i, qi') \<in> rel"
  let ?a = "adapt_vars :: ('f,'q)term \<Rightarrow> ('f,'v)term"
  let ?aC = "adapt_vars_ctxt :: ('f,'q)ctxt \<Rightarrow> ('f,'v)ctxt"
  let ?n = "length qs"
  let ?qi = "qs ! i"
  note trim = ta_trimE[OF trim rule]
  from relE[OF rel] obtain ti ti' where
    gti: "ground ti" and gti': "ground ti'" 
    and qi: "?qi \<in> ta_res TA ti" 
    and qi': "qi' \<in> ta_res TA ti'" 
    and step: "(?a ti, ?a ti') \<in> rstep R" by auto
  {
    fix j
    assume "j < ?n"
    then have "qs ! j \<in> set (q # qs)" by auto
    from trim[OF this] have "qs ! j \<in> ta_reachable TA" ..
    from ta_reachableE[OF this] have "\<exists> t. ground t \<and> qs ! j \<in> ta_res TA t" by blast
  }
  then have "\<forall> j. \<exists> t. j < ?n \<longrightarrow> ground t \<and> qs ! j \<in> ta_res TA t" by blast
  from choice[OF this] obtain tjs where tjs: "\<And> j. j < ?n \<Longrightarrow> ground (tjs j) \<and> qs ! j \<in> ta_res TA (tjs j)" by blast
  let ?t_gen = "\<lambda> t. Fun f (map (\<lambda> j. if i = j then t else tjs j) [0 ..< ?n])"
  let ?t = "?t_gen ti"
  let ?t' = "?t_gen ti'"
  from trim[of q] have "q \<in> ta_productive TA" by auto
  from ta_productiveE[OF this]
    obtain p C where qp: "p \<in> ta_res TA (C\<langle>Var q\<rangle>)" 
    and p: "p \<in> ta_final TA" and gC: "ground_ctxt C" .
  {
    fix t :: "('f,'q)term"
    assume "ground t"
    then have "ground (?t_gen t)" 
      using tjs by auto
  } note g = this
  from g[OF gti] have gCt: "ground (C\<langle>?t\<rangle>)" using gC by auto
  from g[OF gti'] have gCt': "ground (C\<langle>?t'\<rangle>)" using gC by auto
  have qt: "q \<in> ta_res TA ?t"
    by (simp, intro exI conjI, rule rule, insert qi tjs, auto)
  have pCt: "p \<in> ta_res TA (C \<langle> ?t \<rangle>)"
    by (rule ta_res_ctxt[OF qt qp])
  from ta_langI[OF gCt p pCt refl] have tA: "((?aC C) \<langle> ?a ?t \<rangle>) \<in> ta_lang TA" by simp
  let ?C = "?aC (ctxt_of_pos_term ([i]) ?t)"
  from rstep_ctxt[OF step, of ?C] have "(?C \<langle> ?a ti \<rangle>, ?C \<langle> ?a ti' \<rangle>) \<in> rstep R" .
  also have "?C \<langle> ?a ti \<rangle> = ?a ?t" unfolding map_upt_split[OF i] by simp
  also have "?C \<langle> ?a ti' \<rangle> = ?a ?t'" unfolding map_upt_split[OF i] by simp
  finally have step: "(?a ?t,?a ?t') \<in> rstep R" .
  from closed[OF tA rstep_ctxt[OF step, of "?aC C"]] have "(?aC C)\<langle>?a ?t'\<rangle> \<in> ta_lang TA" .
  then have "?a (C \<langle>?t'\<rangle>) \<in> ta_lang TA" by simp
  from ta_langE3[OF this]
  obtain p' where pt': "p' \<in> ta_res TA (C\<langle>?t'\<rangle>)" and p': "p' \<in> ta_final TA" .
  from ta_res_ctxt_decompose[OF pt'] obtain q' where qt': "q' \<in> ta_res TA ?t'" and pq': "p' \<in> ta_res TA (C \<langle>Var q'\<rangle>)" by auto
  let ?tj_gen = "\<lambda> t j. if i = j then t else tjs j"
  let ?ti = "?tj_gen ti"
  let ?ti' = "?tj_gen ti'"
  from qt'
  obtain qs' where rule: "(f qs' \<rightarrow> q') \<in> ta_rules TA"
    and len: "length qs' = length qs"
    and qj: "\<And> j. j<length qs \<Longrightarrow> qs' ! j \<in> ta_res TA (?ti' j)" by auto
  have "qs' = qs[i := qi']"
  proof (rule nth_equalityI, simp add: len)
    fix j
    assume j': "j < length qs'"
    then have j: "j < length qs" by (simp add: len)
    from qj[OF this] have qj: "qs' ! j \<in> ta_res TA (?ti' j)" .
    show "qs' ! j = qs[i := qi'] ! j"
    proof (cases "j = i")
      case True
      with qj have "qs' ! j \<in> ta_res TA ti'" by simp
      from ta_detE[OF det this qi'] True show ?thesis using j by auto
    next
      case False
      with qj have "qs' ! j \<in> ta_res TA (tjs j)" by auto
      from ta_detE[OF det this] tjs[OF j] False show ?thesis using j by auto
    qed
  qed
  with rule have "(f qs[i := qi'] \<rightarrow> q') \<in> ta_rules TA" by auto
  moreover
  from relI[OF g[OF gti] g[OF gti'] qt qt' step]
  have "(q,q') \<in> rel" .
  ultimately show "\<exists>q'. (f qs[i := qi'] \<rightarrow> q') \<in> ta_rules TA \<and> (q, q') \<in> rel" by blast
qed auto
end

(* Theorem 13 in paper *)
theorem ta_trim_det_closed:
  fixes TA :: "('q,'f)ta"
  and R :: "('f,'v)trs"
  assumes det: "ta_det TA"
  and trim: "ta_trim TA"  
  and closed: "rstep R `` ta_lang TA \<subseteq> ta_lang TA"
  shows "\<exists> rel. state_compatible TA rel R \<and> state_coherent TA rel"
proof -
  interpret ta_trim_det_closed TA R
    by (unfold_locales, rule det, rule trim, rule closed)
  show ?thesis
    by (intro exI conjI, rule compatible, rule coherent)
qed

(* First part of Corollary 14 in paper *)
corollary closed_iff_compatible_and_coherent:
  fixes TA :: "('q,'f)ta" and R :: "('f,'v)trs" and determ :: "('q,'f)ta \<Rightarrow> ('p,'f)ta"
  assumes determinizer: "(ta_lang (determ TA) :: ('f,'v)terms) = ta_lang TA \<and> ta_det (determ TA)"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "(rstep R `` ta_lang TA \<subseteq> ta_lang TA) \<longleftrightarrow>
    (\<exists> rel. state_compatible (trim_ta (determ TA)) rel R \<and> state_coherent (trim_ta (determ TA)) rel)" 
    (is "?closed = ?compat_coherent")
proof -
  let ?ta_langp = "ta_lang :: ('p,'f)ta \<Rightarrow> ('f,'v)terms"
  let ?ta_langq = "ta_lang :: ('q,'f)ta \<Rightarrow> ('f,'v)terms"
  define TA' where "TA' = trim_ta (determ TA)"
  from determinizer have d: "?ta_langp (determ TA) = ?ta_langq TA" and det: "ta_det (determ TA)" by auto
  have lang: "?ta_langp TA' = ta_lang TA" unfolding TA'_def by (simp add: d trim_ta_lang)
  from ta_subset_det[OF trim_ta_subset det] have det: "ta_det TA'" unfolding TA'_def .
  show ?thesis
  proof
    assume ?compat_coherent
    then obtain rel where compat: "state_compatible TA' rel R" "state_coherent TA' rel" 
      unfolding TA'_def by blast
    from det have eps: "ta_eps TA' = {}" unfolding ta_det_def by auto
    from state_compatible[OF compat disjI2[OF det] wf subset_refl]
    show ?closed unfolding lang by blast
  next
    assume ?closed
    from trim_ta have trim: "ta_trim TA'" unfolding TA'_def .
    from ta_trim_det_closed[OF det trim, of R] \<open>?closed\<close>
    show ?compat_coherent unfolding lang[symmetric] TA'_def[symmetric] by blast
  qed
qed

subsection \<open>Computing smallest relations such that
  automaton is state-coherent and state-compatible (algorithm of Section 3.3)\<close>

locale fixed_automaton = fixes 
  TA :: "('q,'f)ta" and
  R  :: "('f,'v)trs" 
begin

text \<open>We directly here integrate the restriction to ta_match, so that initial_rel can later
  on be implementated via a code-equation. (Without this restriction one would have to deal
  with the never occurring case, that we encounter rules violating the variable condition. And
  this restriction is coming from the outside, so cannot be handled via code equations)\<close>

definition "initial_rel \<equiv> { (q,ta_res TA (map_vars_term (fun_of \<tau>) r)) | q l r \<tau>. q \<in> ta_res TA (map_vars_term (fun_of \<tau>) l)
    \<and> \<tau> \<in> ta_match' TA (ta_rhs_states TA) l \<and> (l,r) \<in> R}"

definition initial_relation :: "('q \<times> 'q)set option" where
  "initial_relation \<equiv> let q_qs = initial_rel in 
    (if {} \<in> snd ` q_qs then None
     else Some (\<Union> ((\<lambda> (q,qs). Pair q ` qs) ` q_qs)))"

lemma initial_relation: assumes det: "ta_det TA"
  and comp: "state_compatible TA rel' R"
  shows "\<exists> rel. initial_relation = Some rel \<and> rel \<subseteq> rel'"
proof -
  let ?q_qs = "{ (q,ta_res TA (map_vars_term (fun_of \<tau>) r)) | q l r \<tau>. q \<in> ta_res TA (map_vars_term (fun_of \<tau>) l)
    \<and> \<tau> \<in> ta_match' TA (ta_rhs_states TA) l \<and> (l,r) \<in> R}"
  from det have eps: "ta_eps TA = {}" unfolding ta_det_def by auto
  {
    fix q qs
    assume "(q,qs) \<in> ?q_qs"
    then obtain l r \<tau> where lr: "(l,r) \<in> R" and \<tau>: "\<tau> \<in> ta_match' TA (ta_rhs_states TA) l" 
    and q: "q \<in> ta_res TA (map_vars_term (fun_of \<tau>) l)" and qs: "qs = ta_res TA (map_vars_term (fun_of \<tau>) r)" by auto
    from q have "funas_term l \<subseteq> ta_syms TA"
      by (metis funas_term_map_vars_term ta_syms_res)      
    from comp[unfolded state_compatible_def, rule_format, OF lr this]
    have "rule_state_compatible TA rel' (l, r)" .
    from this[unfolded rule_state_compatible_def split, rule_format, OF ta_match'_vars_term[OF \<tau>]] q
    have mem: "q \<in> rel'\<inverse> `` qs" unfolding qs by auto
    then obtain q' where q': "q' \<in> qs" by blast
    {
      fix q''
      assume "q'' \<in> qs"
      from ta_detE[OF det this[unfolded qs] q'[unfolded qs]] have "q'' = q'" .
    }
    with q' have qsq': "qs = {q'}" by blast
    with mem have rel: "(q,q') \<in> rel'" by blast
    with qsq' have "\<exists> q'. qs = {q'} \<and> (q,q') \<in> rel'" by blast
  } note q_qs = this
  {
    assume "{} \<in> snd ` ?q_qs"
    then obtain q where "(q,{}) \<in> ?q_qs" by force
    from q_qs[OF this] have False by auto
  }
  then have nmem: "{} \<notin> snd ` ?q_qs" by blast
  let ?rel = "(\<Union> ((\<lambda> (q,qs). Pair q ` qs) ` ?q_qs))"
  {
    fix q q'
    assume "(q,q') \<in> ?rel"
    then obtain qs where qqs: "(q,qs) \<in> ?q_qs" and q': "q' \<in> qs" by auto
    from q_qs[OF qqs] q' have "(q,q') \<in> rel'" by auto
  }
  then have subset: "?rel \<subseteq> rel'" by force
  show ?thesis 
    unfolding initial_relation_def initial_rel_def using nmem subset by auto
qed

inductive require_relation :: "('q \<times> 'q)set \<Rightarrow> 'q \<Rightarrow> 'q option \<Rightarrow> bool" for rel :: "('q \<times> 'q)set" where
 coherence: "(f qs \<rightarrow> q) \<in> ta_rules TA \<Longrightarrow> i < length qs \<Longrightarrow> (qs ! i, qi') \<in> rel 
    \<Longrightarrow> (f (qs[i := qi']) \<rightarrow> q') \<in> ta_rules TA \<Longrightarrow> 
    require_relation rel q (Some q')" 
| no_coherence: "(f qs \<rightarrow> q) \<in> ta_rules TA \<Longrightarrow> i < length qs \<Longrightarrow> (qs ! i, qi') \<in> rel 
    \<Longrightarrow> \<not> (\<exists> q'. (f (qs[i := qi']) \<rightarrow> q') \<in> ta_rules TA) \<Longrightarrow> 
    require_relation rel q None" 

lemma require_relation_ta_states:
  assumes "require_relation rel q (Some q')"
  shows "{q,q'} \<subseteq> ta_states TA"
proof -
  define sq' where "sq' = Some q'"
  from assms have "require_relation rel q sq'" and "sq' = Some q'" unfolding sq'_def by auto    
  then have "{q,the sq'} \<subseteq> ta_states TA"
  proof (induct)
    case (coherence f qs q i qi' q')
    have "q \<in> r_states (f qs \<rightarrow> q)" unfolding r_states_def by auto
    moreover have "q' \<in> r_states (f qs[i := qi'] \<rightarrow> q')" unfolding r_states_def by auto
    ultimately show ?case using coherence(1,4)
      by (auto simp: ta_states_def)
  qed auto
  then show ?thesis unfolding sq'_def by auto
qed

lemma require_relation: assumes   det: "ta_det TA"  
  and sub: "rel \<subseteq> rel'" 
  shows "require_relation rel q sq' \<Longrightarrow> state_coherent TA rel' \<Longrightarrow> state_compatible TA rel' R \<Longrightarrow> 
   \<exists> q'. sq' = Some q' \<and> (q,q') \<in> rel'"
proof (induct rule: require_relation.induct)
  case (no_coherence f qs q i qi')
  with sub have mem: "(qs ! i, qi') \<in> rel'" by auto
  from no_coherence(5) have "state_coherent TA rel'" by auto
  from state_coherentE[OF this no_coherence(1-2) mem]
    no_coherence(4) show ?case by blast
next
  case (coherence f qs q i qi' q')
  with sub have mem: "(qs ! i, qi') \<in> rel'" by auto
  from coherence(5) have "state_coherent TA rel'" by auto
  from state_coherentE[OF this coherence(1-2) mem]
  obtain q'' where "(f qs[i := qi'] \<rightarrow> q'') \<in> ta_rules TA" "(q,q'') \<in> rel'" by auto
  with det[unfolded ta_det_def] coherence(4) show ?case by blast
qed

inductive_set generate_rel :: "(('q \<times> 'q)set option \<times> ('q \<times> 'q)set option)set" where
  fail: "require_relation rel q None \<Longrightarrow> (Some rel, None) \<in> generate_rel"
| iterate: "require_relation rel q (Some q') \<Longrightarrow> (q,q') \<notin> rel \<Longrightarrow>
  (Some rel, Some (insert (q,q') rel)) \<in> generate_rel"

lemma None_NF_generate_rel[simp]: "None \<in> NF generate_rel"
  by (rule, rule, cases rule: generate_rel.cases, auto)

lemma generate_rel_subset: assumes   det: "ta_det TA"  
 shows "(rel,srel') \<in> generate_rel \<Longrightarrow> the rel \<subseteq> rel'' 
  \<Longrightarrow> state_coherent TA rel'' \<Longrightarrow> state_compatible TA rel'' R 
  \<Longrightarrow> \<exists> rel'. srel' = Some rel' \<and> rel' \<subseteq> rel''"
proof (induct rule: generate_rel.induct)
  case (fail rel q)
  note fail = fail[unfolded option.sel]
  from require_relation[OF det fail(2) fail(1,3,4)]
  show ?case by blast
next
  case (iterate rel q q')
  note iterate = iterate[unfolded option.sel]
  from require_relation[OF det iterate(3,1,4,5)] iterate(3)
  show ?case by auto
qed

lemma generate_rel_complete: assumes   det: "ta_det TA"  
  and steps: "(initial_relation,srel) \<in> generate_rel^*"
  and coh: "state_coherent TA rel'"
  and comp: "state_compatible TA rel' R"
  shows "\<exists> rel. srel = Some rel \<and> rel \<subseteq> rel'"
proof -
  from initial_relation[OF det comp] obtain rel where init: "initial_relation = Some rel" and rel: "rel \<subseteq> rel'" by auto
  {
    fix sr
    have "(sr, srel) \<in> generate_rel^* \<Longrightarrow> sr \<noteq> None \<Longrightarrow> the sr \<subseteq> rel' \<Longrightarrow> \<exists> rel. srel = Some rel \<and> rel \<subseteq> rel'"
    proof (induct rule: rtrancl_induct)
      case base
      then show ?case by (cases sr, auto)
    next
      case (step sr' sr'')
      from step(3)[OF step(4-5)] obtain r' where sr': "sr' = Some r'" and sub: "r' \<subseteq> rel'" by auto
      from generate_rel_subset[OF det step(2), unfolded sr' option.sel, OF sub coh comp]
      show ?case .
    qed
  }
  from this[OF steps, unfolded init] show ?thesis using rel by auto
qed

lemma generate_rel_mono: assumes "(Some r, Some r') \<in> generate_rel^*"
  shows "r \<subseteq> r'"
proof -
  {
    fix sr sr'
    have "(sr,sr') \<in> generate_rel^* \<Longrightarrow> sr \<noteq> None \<Longrightarrow> sr' \<noteq> None \<Longrightarrow> the sr \<subseteq> the sr'"
    proof (induct rule: rtrancl_induct)
      case (step sr' sr'')
      from step(5) obtain r'' where sr'': "sr'' = Some r''" by auto
      from step(2) obtain r' where sr': "sr' = Some r'" by (cases, auto)
      from step(4) obtain r where sr: "sr = Some r" by auto
      from step(3) sr sr' have "r \<subseteq> r'" by auto
      moreover from step(2)[unfolded sr' sr''] have "r' \<subseteq> r''" by (cases, auto)
      ultimately show ?case unfolding sr sr'' by auto
    qed auto
  }
  from this[OF assms] show ?thesis by auto
qed
  
lemma generate_rel_sound: assumes eps: "ta_eps TA = {}" and 
  nf: "(initial_relation, Some rel) \<in> generate_rel^!"
  and rel_fin: "rel `` ta_final TA \<subseteq> ta_final TA"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "state_coherent TA rel \<and> state_compatible TA rel R"
proof (rule ccontr)
  from nf have NF: "Some rel \<in> NF (generate_rel)" by auto
  from rel_fin have fin_imp: "\<And> q q'. (q,q') \<in> rel \<Longrightarrow> q \<in> ta_final TA \<longrightarrow> q' \<in> ta_final TA" by blast
  assume "\<not> ?thesis"
  then have "\<not> state_coherent TA rel \<or> \<not> state_compatible TA rel R" by blast
  then show False
  proof
    assume "\<not> state_compatible TA rel R"
    from this[unfolded state_compatible_def]
    obtain l r where 
      lr: "(l, r) \<in> R" and fl: "funas_term l \<subseteq> ta_syms TA" 
      and not: "\<not> rule_state_compatible TA rel (l, r)" by blast
    from not[unfolded rule_state_compatible_def split] obtain \<tau> where
      vars: "\<tau> ` vars_term l \<subseteq> ta_rhs_states TA" 
      and not: "\<not> ta_res TA (map_vars_term \<tau> l) \<subseteq> rel\<inverse> `` ta_res TA (map_vars_term \<tau> r)" by blast
    from not obtain q where q: "q \<in> ta_res TA (map_vars_term \<tau> l)" 
      and not: "\<not> (\<exists> q'. q' \<in> ta_res TA (map_vars_term \<tau> r) \<and> (q,q') \<in> rel)" by blast
    from ta_match'[OF q vars] obtain \<tau>' where \<tau>': "\<tau>' \<in> ta_match' TA (ta_rhs_states TA) l" 
      and varsl: "\<forall>x\<in>vars_term l. \<tau> x = fun_of \<tau>' x" by auto
    have idl: "map_vars_term \<tau> l = map_vars_term (fun_of \<tau>') l"
      by (rule map_vars_term_vars_term, insert varsl, auto)
    have idr: "map_vars_term \<tau> r = map_vars_term (fun_of \<tau>') r"
      by (rule map_vars_term_vars_term, insert wf[OF lr] varsl, auto)
    from q lr \<tau>' have init: "(q,ta_res TA (map_vars_term \<tau> r)) \<in> initial_rel" unfolding initial_rel_def idl idr by auto
    {
      assume "initial_relation = None"
      with nf have "(None, Some rel) \<in> generate_rel^!" by auto
      then have "(None, Some rel) \<in> generate_rel^*" by auto
      then have "(None, Some rel) \<in> generate_rel^+" by (cases, auto)
      then have "\<exists> s. (None,s) \<in> generate_rel" by (induct, auto)
      then obtain s where "(None,s) \<in> generate_rel" by auto
      from generate_rel.cases[OF this] have False by auto
    }
    then obtain irel where initial: "initial_relation = Some irel" by auto
    show False 
    proof (cases "\<exists> q'. q' \<in> ta_res TA (map_vars_term \<tau> r)")
      case True
      then obtain q' where q': "q' \<in> ta_res TA (map_vars_term \<tau> r)" by auto
      with not have qq': "(q,q') \<notin> rel" by blast
      from init q' have qq'2: "(q,q') \<in> irel" using initial
        unfolding initial_relation_def Let_def by (auto split: if_splits)
      from nf[unfolded initial] have "(Some irel, Some rel) \<in> generate_rel^*" by auto
      from generate_rel_mono[OF this] qq' qq'2 show False by auto
    next
      case False
      then have "ta_res TA (map_vars_term \<tau> r) = {}" by blast
      from init[unfolded this]
      have "initial_relation = None" unfolding initial_relation_def Let_def
        by force
      with initial show False by auto
    qed 
  next
    assume "\<not> state_coherent TA rel"
    from this[unfolded state_coherent_def eps] rel_fin
    obtain f qs q i qi
    where rule: "(f qs \<rightarrow> q) \<in> ta_rules TA"
          and i: "i < length qs" and rel: "(qs ! i, qi) \<in> rel" 
          and not: "\<not> (\<exists> q'. (f qs[i := qi] \<rightarrow> q') \<in> ta_rules TA \<and> (q, q') \<in> rel)"
      by blast
    show False
    proof (cases "\<exists> q'. (f qs[i := qi] \<rightarrow> q') \<in> ta_rules TA")
      case True
      then obtain q' where rule': "(f qs[i := qi] \<rightarrow> q') \<in> ta_rules TA" by blast
      with not have qq': "(q,q') \<notin> rel" by auto
      from require_relation.coherence[OF rule i rel rule'] have "require_relation rel q (Some q')" .
      from generate_rel.iterate[OF this qq'] NF show False by blast
    next
      case False
      from generate_rel.fail[OF require_relation.no_coherence[OF rule i rel False]] NF
      show False by blast
    qed
  qed
qed

(* decision procedure for coherence and compatibility: just compute arbitrary normal form
  w.r.t. generate_rel, and then check whether produced relation satisfies final state condition *)
definition "decide_coherent_compatible_main normalizer \<equiv> case normalizer initial_relation of
  None \<Rightarrow> False
| Some rel \<Rightarrow> rel `` ta_final TA \<subseteq> ta_final TA"

lemma decide_coherent_compatible_main: assumes det: "ta_det TA"  
  and normalizer: "(initial_relation, normalizer initial_relation) \<in> generate_rel^!"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "decide_coherent_compatible_main normalizer = 
  (\<exists> rel. state_compatible TA rel R \<and> state_coherent TA rel)"
proof -
  from det have eps: "ta_eps TA = {}" unfolding ta_det_def by auto
  let ?nf_rel = "normalizer initial_relation"
  from normalizer have steps: "(initial_relation, ?nf_rel) \<in> generate_rel^*" by auto
  note d = decide_coherent_compatible_main_def 
  show ?thesis
  proof
    assume "decide_coherent_compatible_main normalizer"
    from this[unfolded d] obtain rel where srel: "?nf_rel = Some rel" and fin: "rel `` ta_final TA \<subseteq> ta_final TA" by (cases ?nf_rel, auto)
    from generate_rel_sound[OF eps normalizer[unfolded srel] fin wf] show "(\<exists> rel. state_compatible TA rel R \<and> state_coherent TA rel)" by blast
  next
    assume "(\<exists> rel. state_compatible TA rel R \<and> state_coherent TA rel)"
    then obtain rel where compat: "state_compatible TA rel R" and coh: "state_coherent TA rel" by blast
    from generate_rel_complete[OF det steps coh compat] 
    obtain rel' where *: "?nf_rel = Some rel' \<and> rel' \<subseteq> rel" by auto
    with state_coherentE2[OF coh] have "rel' `` ta_final TA \<subseteq> ta_final TA" by auto
    then show "decide_coherent_compatible_main normalizer" using *
      unfolding d by auto
  qed
qed

text \<open>We also provide a normalizer which implements a standard working list algorithm\<close>

definition "new_states rel \<equiv> { (q,qo) | q qo. require_relation rel q qo}"

lemma new_states_empty[simp]: "new_states {} = {}" unfolding new_states_def
  by (auto, cases rule: require_relation.cases, auto)

lemma new_states_union[simp]: "new_states (rel \<union> rel') = new_states rel \<union> new_states rel'"
  (is "?l = ?r1 \<union> ?r2")
proof -
  note d = new_states_def
  {
    fix q qo
    assume "(q,qo) \<in> ?l"
    then have "require_relation (rel \<union> rel') q qo" unfolding d by auto
    then have "require_relation rel q qo \<or> require_relation rel' q qo"
      by (cases, auto intro: require_relation.intros)
    then have "(q,qo) \<in> ?r1 \<union> ?r2" unfolding d by auto
  }
  moreover
  {
    fix q qo rel''
    assume qqo: "(q,qo) \<in> new_states rel''" and subset: "rel'' \<subseteq> rel \<union> rel'"
    from qqo have "require_relation rel'' q qo" unfolding d by auto
    then have "require_relation (rel \<union> rel') q qo"
      by (cases, insert subset, auto intro: require_relation.intros)
    then have "(q,qo) \<in> ?l" unfolding d by auto
  } note other = this
  from other[of _ _ rel] other[of _ _ rel'] have "?r1 \<union> ?r2 \<subseteq> ?l" by auto
  ultimately show ?thesis by auto
qed


lemma new_states_ta_states: "new_states rel \<subseteq> ta_states TA \<times> ({None} \<union> Some ` ta_states TA)"
  (is "_ \<subseteq> ?large")
proof
  fix q po
  note d = new_states_def
  assume mem: "(q,po) \<in> new_states rel"    
  show "(q,po) \<in> ?large"
  proof (cases po)
    case (Some p)
    with mem have "require_relation rel q (Some p)" unfolding d by auto
    from require_relation_ta_states[OF this] show ?thesis unfolding Some by auto
  next
    case None
    with mem have "require_relation rel q None" unfolding d by auto
    then have "q \<in> ta_states TA"
    proof (cases rule: require_relation.cases)
      case (no_coherence f qs)
      have "q \<in> r_states (f qs \<rightarrow> q)" unfolding r_states_def by auto
      with no_coherence(1) show ?thesis unfolding ta_states_def by auto
    qed
    then show ?thesis unfolding None by auto
  qed
qed

text \<open>The following method is terminating if TA is finite. However, since
  we want to execute this code later on, we did not use the assumption "finite TA" 
  in the locale, so that the simplification rules are unconditional. 
  Since partial-function does not offer an induction scheme, to prove the main
  property of normalize-main, we directly use induction with the well-founded relation
  that also shows termination.\<close>
partial_function (tailrec) normalize_main where 
  "normalize_main rel accu = (let new = new_states rel
    in (if None \<in> snd ` new then None else
    let new_rel = (\<lambda> (x,y). (x,the y)) ` new;
        new_accu = accu \<union> rel;
        todo = new_rel - new_accu
    in (if todo \<subseteq> {} then Some new_accu
    else normalize_main todo new_accu)))"    

lemma finite_new_states: "finite (ta_states TA) \<Longrightarrow> finite (new_states rel)"
  by (rule finite_subset[OF new_states_ta_states], auto)

lemma normalize_main: assumes fin: "finite (ta_states TA)"
  shows "(Some rel, normalize_main rel {}) \<in> generate_rel^!"
proof -
  let ?G = generate_rel
  let ?the = "(\<lambda>(x, y). (x, the y))"
  {
    fix accu
    let ?m = "\<lambda> (accu,rel). card (ta_states TA \<times> ta_states TA - (rel \<union> accu))"
    let ?P = "\<lambda> (accu,rel). None \<notin> snd ` new_states accu \<longrightarrow> ?the ` new_states accu \<subseteq> accu \<union> rel \<longrightarrow>
      (Some (accu \<union> rel), normalize_main rel accu) \<in> generate_rel^!"
    assume ass: "None \<notin> snd ` new_states accu" "?the ` new_states accu \<subseteq> accu \<union> rel"
    have "(Some (accu \<union> rel), normalize_main rel accu) \<in> generate_rel^!"
    proof (induct rule: wf_induct[OF wf_measure[of ?m], of ?P "(accu,rel)", unfolded split, rule_format, OF _ ass])
      case (1 accu_rel)
      obtain rel accu where accu_rel: "accu_rel = (accu,rel)" by force
      show ?case unfolding accu_rel split
      proof (intro impI)
        assume premNone: "None \<notin> snd ` new_states accu"
        assume premAccu: "?the ` new_states accu \<subseteq> accu \<union> rel"
        let ?new = "new_states rel"
        note simps = normalize_main.simps[of rel] Let_def new_states_def
        show "(Some (accu \<union> rel), normalize_main rel accu) \<in> ?G^!"
        proof (cases "None \<in> snd ` ?new")
          case True
          then have id: "normalize_main rel accu = None" unfolding simps by simp
          from True have "None \<in> snd ` new_states (accu \<union> rel)" by auto
          then obtain q where "require_relation (accu \<union> rel) q None" unfolding simps by auto
          from generate_rel.fail[OF this]
          show ?thesis unfolding id by auto
        next
          case False note oFalse = this      
          let ?the = "(\<lambda>(x, y). (x, the y))"
          let ?new_rel = "?the ` ?new"
          let ?new_accu = "accu \<union> rel"
          let ?todo = "?new_rel - ?new_accu"
          have None: "None \<notin> snd ` new_states ?new_accu" using oFalse premNone by auto
          show ?thesis
          proof (cases "?todo \<subseteq> {}")
            case True
            with False have id: "normalize_main rel accu = Some ?new_accu" by (auto simp: simps)
            have NF: "Some ?new_accu \<in> NF ?G"
            proof (rule, rule)
              fix srel
              assume "(Some ?new_accu, srel) \<in> ?G"
              then show False
              proof (cases)
                case (fail q)
                then have "(q,None) \<in> new_states ?new_accu" unfolding new_states_def by auto
                with None show False by force
              next
                case (iterate q q')
                from iterate(2) have "(q,Some q') \<in> new_states ?new_accu" unfolding new_states_def by auto
                with True premAccu have "(q,q') \<in> ?new_accu" by auto
                with iterate(3) show False ..
              qed
            qed
            then show ?thesis unfolding id by auto
          next
            case False
            with oFalse have id: "normalize_main rel accu = normalize_main ?todo ?new_accu" unfolding simps by simp
            note IH = 1[of "(?new_accu,?todo)", unfolded split accu_rel, rule_format]
            show ?thesis unfolding id
            proof (rule normalizability_I'[OF _ IH])
              show "?the ` new_states ?new_accu \<subseteq> ?new_accu \<union> ?todo" using premAccu by auto
              show "None \<notin> snd ` new_states ?new_accu" by (rule None)
              define A where "A = ?todo"
              have "finite A" unfolding A_def using finite_new_states[of rel, OF fin] by auto
              moreover have "A \<subseteq> ?the ` ?new" unfolding A_def by auto
              ultimately have "(Some ?new_accu, Some (?new_accu \<union> A)) \<in> ?G^*"
              proof (induct A)
                case (insert x A)
                from insert(4) have sub: "A \<subseteq> ?new_rel" by auto
                note IH = insert(3)[OF sub]
                show ?case
                proof (cases "x \<in> ?new_accu")
                  case True
                  then have "?new_accu \<union> insert x A = ?new_accu \<union> A" by auto
                  with IH show ?thesis by auto
                next
                  case False
                  obtain q p where x: "x = (q,p)" by force
                  with insert(4) have "(q,p) \<in> ?new_rel" by auto
                  then obtain po where mem: "(q,po) \<in> ?new" and "(q,p) = ?the (q,po)" by auto
                  with oFalse have "po = Some p" by (cases po, force+)
                  with mem have "(q,Some p) \<in> new_states (?new_accu \<union> A)" by auto
                  then have "require_relation (?new_accu \<union> A) q (Some p)" unfolding new_states_def by auto
                  from generate_rel.iterate[OF this, folded x] False insert(2) IH
                  show ?thesis by auto
                qed
              qed simp
              then show "(Some ?new_accu, Some (?new_accu \<union> ?todo)) \<in> ?G^*" unfolding A_def .
              show "((?new_accu,?todo), (accu,rel)) \<in> measure ?m"
              proof (simp, rule psubset_card_mono)
                show "finite (ta_states TA \<times> ta_states TA - (rel \<union> accu))" using fin by auto
                show "ta_states TA \<times> ta_states TA - (?new_rel \<union> ?new_accu) \<subset> ta_states TA \<times> ta_states TA - (rel \<union> accu)" (is "?l \<subset> ?r")
                proof 
                  show "?l \<subseteq> ?r" by auto
                  from False obtain qq' where mem: "qq' \<in> ?new_rel - ?new_accu" by blast
                  obtain q q' where qq': "qq' = (q,q')" by force
                  from mem[unfolded qq'] obtain qo where q': "q' = the qo" and qqo: "(q,qo) \<in> ?new" by auto
                  with oFalse have qo: "qo = Some q'" by (cases qo, force+)
                  from qqo[unfolded qo] have "(q, Some q') \<in> new_states rel" by auto
                  with new_states_ta_states have "qq' \<in> ta_states TA \<times> ta_states TA" 
                  unfolding qq' by auto
                  with mem show "?l \<noteq> ?r" by auto
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  } note main = this
  show ?thesis using main[of "{}"] by auto
qed

fun normalize where 
  "normalize None = None"
| "normalize (Some rel) = normalize_main rel {}"

lemma normalize: assumes fin: "finite (ta_states TA)"
  shows "(rel, normalize rel) \<in> generate_rel^!"
proof (cases rel)
  case (Some rel)
  show ?thesis unfolding Some normalize.simps
    by (rule normalize_main[OF fin])
qed auto

definition "decide_coherent_compatible \<equiv> decide_coherent_compatible_main normalize"

lemma decide_coherent_compatible: assumes det: "ta_det TA"
  and fin: "finite (ta_states TA)"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "decide_coherent_compatible = 
  (\<exists> rel. state_compatible TA rel R \<and> state_coherent TA rel)"
  unfolding decide_coherent_compatible_def
  by (rule decide_coherent_compatible_main[OF det], rule normalize[OF fin], insert wf, auto)
end

text \<open>We can now define a decision procedure for deterministic TA, whether
  they are closed under rewriting\<close>

definition closed_under_rewriting :: "('q,'f)ta \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "closed_under_rewriting TA R \<equiv> fixed_automaton.decide_coherent_compatible (trim_ta TA) R"

lemma closed_under_rewriting: assumes det: "ta_det TA" 
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and fin: "finite (ta_states TA)"
  shows "closed_under_rewriting TA R = (rstep R `` ta_lang TA \<subseteq> ta_lang TA)"
  (is "?l = ?r")
proof -
  have r: "?r = (\<exists>rel. state_compatible (trim_ta TA) rel R \<and> state_coherent (trim_ta TA) rel)"
    by (rule closed_iff_compatible_and_coherent[of "\<lambda> x. x"], insert det wf fin, auto)
  from ta_subset_ta_states[OF trim_ta_subset[of TA]] fin have fin: "finite (ta_states (trim_ta TA))" 
    by (rule finite_subset)
  from det have det: "ta_det (trim_ta TA)" by (rule obtain_trimmed_ta)
  interpret fixed_automaton "trim_ta TA" R .
  show ?thesis unfolding r
    using decide_coherent_compatible[OF det fin wf]
    unfolding closed_under_rewriting_def by auto
qed

lemmas decision_procedure_code = 
  fixed_automaton.decide_coherent_compatible_def
  fixed_automaton.decide_coherent_compatible_main_def
  fixed_automaton.normalize.simps
  fixed_automaton.normalize_main.simps
  fixed_automaton.initial_relation_def

declare decision_procedure_code[code]

text \<open>We also can couple the decision procedure with our determizer @{term full_power_set_ta} 
  to get rid of the @{term ta_det} precondition.\<close>

definition closed_under_rewriting_non_det :: "('q,'f)ta \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "closed_under_rewriting_non_det TA R \<equiv> closed_under_rewriting (full_power_set_ta TA) R"

lemma closed_under_rewriting_non_det: 
  assumes wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and fin: "finite (ta_states TA)"
  shows "closed_under_rewriting_non_det TA R = (rstep R `` ta_lang TA \<subseteq> ta_lang TA)"
proof -
  note power = full_power_set_ta[of TA]
  show ?thesis
    unfolding closed_under_rewriting_non_det_def power(3)[symmetric]
    by (rule closed_under_rewriting[OF power(1) wf power(2)[OF fin]])
qed


subsection \<open>Implementation of @{term fixed_automaton.new_states} 
  and @{term fixed_automaton.initial_rel}\<close>

fun coherent_rule :: "'q rel \<Rightarrow> ('q,'f)ta_rule set \<Rightarrow> ('q,'f)ta_rule \<Rightarrow> ('q \<times> 'q option)set" where
  "coherent_rule rel rules (TA_rule f qs q) = (\<Union> (set (map (\<lambda> i. 
     let qi = qs ! i;
         qi's = snd ` {qq' \<in> rel. fst qq' = qi};
         rhss = \<Union> ((\<lambda> qi'. let qs' = qs[i := qi'];
            rls = {rule \<in> rules. case rule of TA_rule g qs'' q' \<Rightarrow> g = f \<and> qs'' = qs'}
            in 
            if rls \<subseteq> {} then {None} else (Some o r_rhs) ` rls
         ) ` qi's)
     in (\<lambda> qo. (q,qo)) ` rhss
     ) 
    [0 ..< length qs])))"

definition new_states :: "('q,'f)ta \<Rightarrow> 'q rel \<Rightarrow> ('q \<times> 'q option)set" where
  "new_states TA rel = (let rules = ta_rules TA in
    \<Union> (coherent_rule rel rules ` rules))"

lemma new_states[code_unfold]: "fixed_automaton.new_states = new_states" (is "?l = ?r")
proof (intro ext)
  fix TA rel
  note d = new_states_def
  show "?l TA rel = ?r TA rel"
  proof -
    interpret fixed_automaton TA .
    note d' = new_states_def
    {
      fix q po
      assume "(q,po) \<in> ?l TA rel"
      from this[unfolded d']
      have "require_relation rel q po" by auto
      then have "(q,po) \<in> ?r TA rel"
      proof (cases)
        case (coherence f qs i qi' p)
        let ?set = "{rule \<in> ta_rules TA. case rule of TA_rule g qs'' q' \<Rightarrow> g = f \<and> qs'' = qs[i := qi']}"
        have mem: "(f qs[i := qi'] \<rightarrow> p) \<in> ?set"
          using coherence by auto
        then have non_empty: "?set \<subseteq> {} = False" by auto
        have i: "i \<in> set [0 ..< length qs]" using coherence(3) by auto
        have qi': "qi' \<in> snd ` {qq' \<in> rel. fst qq' = qs ! i}" using coherence mem by force
        have "(q,po) \<in> coherent_rule rel (ta_rules TA) (f qs \<rightarrow> q)"  
          unfolding coherent_rule.simps coherence(1) Let_def set_map
          by (rule, rule, rule i, force, rule, rule refl, rule, 
            rule qi', unfold non_empty if_False, insert coherence mem, force)
        with coherence(2) show ?thesis unfolding d Let_def by blast
      next
        case (no_coherence f qs i qi')
        let ?set = "{rule \<in> ta_rules TA. case rule of TA_rule g qs'' q' \<Rightarrow> g = f \<and> qs'' = qs[i := qi']}"
        have set: "?set \<subseteq> {}"
        proof
          fix rule
          assume "rule \<in> ?set"
          then have False using no_coherence by (cases rule, auto)
          then show "rule \<in> {}" by auto
        qed
        then have set: "?set = {}" by auto
        have i: "i \<in> set [0 ..< length qs]" using no_coherence(3) by auto
        have qi': " qi' \<in> snd ` {qq' \<in> rel. fst qq' = qs ! i}" using no_coherence by force
        have "(q,None) \<in> coherent_rule rel (ta_rules TA) (f qs \<rightarrow> q)"
          unfolding coherent_rule.simps Let_def set_map
          by (rule, rule, rule refl, rule i, rule, rule refl, rule, rule imageI[OF qi'], unfold set, auto)
        with no_coherence(2) show ?thesis unfolding d Let_def no_coherence(1) by blast
      qed
    }
    moreover
    {
      fix q po
      assume "(q,po) \<in> ?r TA rel"
      from this[unfolded d Let_def]
      obtain rule where mem1: "rule \<in> ta_rules TA" and
        mem: "(q, po) \<in> coherent_rule rel (ta_rules TA) rule" by auto
      obtain f qs q' where rule: "rule = TA_rule f qs q'" by (cases rule, auto)
      note mem = mem[unfolded rule coherent_rule.simps set_map]
      let ?inn = "\<lambda> i qi'. let qs' = qs[i := qi']; 
        rls = {rule \<in> ta_rules TA. case rule of TA_rule g qs'' q' \<Rightarrow> g = f \<and> qs'' = qs'}
        in if rls \<subseteq> {} then {None} else (Some \<circ> r_rhs) ` rls"
      define inn where "inn \<equiv> \<lambda> qi's i. (\<Union>((?inn i) ` qi's))"
      let ?out = "\<lambda> i. let qi = qs ! i; qi's = snd ` {qq' \<in> rel. fst qq' = qi}
            in (Pair q') ` (inn qi's i)"
      from mem have "(q, po) \<in> \<Union> (?out ` set [0..<length qs])" unfolding inn_def Let_def by auto
      then obtain i where i: "i < length qs" and mem: "(q,po) \<in> ?out i" by auto
      from mem have q': "q' = q" by auto
      from mem[unfolded Let_def] have mem: "po \<in> inn (snd ` {qq' \<in> rel. fst qq' = qs ! i}) i" by auto
      then obtain qi' where rel: "(qs ! i, qi') \<in> rel" and mem: "po \<in> ?inn i qi'" unfolding inn_def by force
      note intro = require_relation.intros[OF mem1[unfolded rule q'] i rel]
      let ?set = "{rule \<in> ta_rules TA. case rule of TA_rule g qs'' q' \<Rightarrow> g = f \<and> qs'' = qs[i := qi']}"
      note mem = mem[unfolded Let_def]
      have "require_relation rel q po"
      proof (cases "?set = {}")
        case True
        with mem have po: "po = None" by auto
        show ?thesis unfolding po
          by (rule intro(2), insert True, auto)
      next
        case False
        then have "?set \<subseteq> {} = False" by auto
        note mem = mem[unfolded this if_False]
        from mem obtain rule where po: "po = (Some o r_rhs) rule" and rule: "rule \<in> ?set" by auto
        from rule obtain p where rule: "rule = f (qs[i := qi']) \<rightarrow> p" and mem: "rule \<in> ta_rules TA" by (cases rule, auto)
        show ?thesis using po intro(1)[OF mem[unfolded rule]] unfolding rule by auto
      qed    
      then have "(q,po) \<in> ?l TA rel" unfolding d' by auto
    }
    ultimately show ?thesis by auto
  qed
qed  

definition "initial_rel TA R \<equiv> let 
    rhs = ta_rhs_states TA;
    match = ta_match' TA rhs;
    analyze_rule = (\<lambda> (l,r). let vl = vars_term l in \<Union> ((\<lambda> \<sigma>. let qr = ta_res TA (map_vars_term (fun_of \<sigma>) r)
      in ((\<lambda> q. (q,qr)) ` ta_res TA (map_vars_term (fun_of \<sigma>) l))) ` match l))
    in \<Union> (analyze_rule ` R)"

lemma ta_rhs_states_code[code]: "ta_rhs_states TA = (ta_eps TA)^* `` (r_rhs ` ta_rules TA)"
  unfolding ta_rhs_states_def by auto

lemma initial_rel[code_unfold]: "fixed_automaton.initial_rel = initial_rel" (is "?l = ?r")
proof (intro ext)
  fix TA R
  note d = initial_rel_def Let_def
  show "?l TA R = ?r TA R"
  proof -
    interpret fixed_automaton TA R .
    note d' = initial_rel_def
    {
      fix q qr
      assume "(q,qr) \<in> ?r TA R"
      from this[unfolded d] obtain l r \<sigma> where
        lr: "(l,r) \<in> R" and 
        \<sigma>: "\<sigma> \<in> ta_match' TA (ta_rhs_states TA) l" and
        mem: "(q,qr) \<in> (\<lambda>q. (q, ta_res TA (map_vars_term (fun_of \<sigma>) r))) ` ta_res TA (map_vars_term (fun_of \<sigma>) l)" 
        by auto
      from mem have q: "q \<in> ta_res TA (map_vars_term (fun_of \<sigma>) l)" and qr: "qr = ta_res TA (map_vars_term (fun_of \<sigma>) r)" by auto
      have "(q,qr) \<in> ?l TA R" unfolding d' qr
        by (rule, intro exI conjI, rule refl, insert lr q \<sigma>, auto)
    }
    moreover
    {
      fix q qr
      assume "(q,qr) \<in> ?l TA R"
      from this[unfolded d'] obtain l r \<sigma> where
        lr: "(l,r) \<in> R" and
        qr: "qr = ta_res TA (map_vars_term (fun_of \<sigma>) r)" and
        \<sigma>: "\<sigma> \<in> ta_match' TA (ta_rhs_states TA) l" and
        q: "q \<in> ta_res TA (map_vars_term (fun_of \<sigma>) l)" by auto
      have "(q,qr) \<in> ?r TA R" unfolding d qr
        by (rule, rule imageI[OF lr], unfold split, rule, rule imageI, rule, rule \<sigma>, insert q, auto)
    }
    ultimately show ?thesis by force
  qed
qed

definition fmap_states_ta ::  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'f) ta \<Rightarrow> ('b, 'f) ta" where
 "fmap_states_ta f TA \<equiv>
    let rep_rule = \<lambda>r. case r of g qs \<rightarrow> q \<Rightarrow> g (map f qs) \<rightarrow> f q in
    \<lparr> ta_final = f ` (ta_final TA), 
      ta_rules = rep_rule ` (ta_rules TA),
      ta_eps = (\<lambda>(q, q'). (f q, f q')) ` (ta_eps TA) \<rparr>"

lemma ta_res_fmap_states_inv:
  assumes "inj_on f (ta_states TA)" "ground t" "q \<in> ta_res (fmap_states_ta f TA) (adapt_vars t)"
  shows "\<exists>p. p \<in> ta_res TA (adapt_vars t) \<and> q = f p"
  using assms(2,3)
proof (induction t arbitrary: q)
  let ?fta = "fmap_states_ta f TA"
  {
    fix f qs q and TA :: "('x, 'y) ta" assume *: "f qs \<rightarrow> q \<in> ta_rules TA"
    then have "q \<in> ta_states TA" "p \<in> set qs \<Longrightarrow> p \<in> ta_states TA" for p
      by (simp_all add: r_rhs_def ta_states_def r_states_def split: ta_rule.splits) blast+
  } note rq_states = this

  case (Fun g ts)
  from this obtain qs q' where
    rule: "g qs \<rightarrow> q' \<in> ta_rules ?fta" and
    res: "\<forall>i < length qs. qs ! i \<in> ta_res ?fta (adapt_vars (ts ! i)) \<and> ground (ts ! i)" and
    eps: "(q', q) \<in> (ta_eps ?fta)\<^sup>*" and
    ground: "\<forall>i < length qs. ground (ts ! i)" and
    len: "length qs = length ts"
  by auto
  with Fun.IH have
    "\<forall>i. \<exists>p. i < length qs \<longrightarrow> p \<in> ta_res TA (adapt_vars (ts ! i)) \<and> qs ! i = f p"
  by (auto)
  from choice[OF this] obtain ps' where
    ps': "\<forall>i < length qs. (ps' i) \<in> ta_res TA (adapt_vars (ts ! i)) \<and> qs ! i = f (ps' i)"
  by auto
  define ps where "ps = map ps' [0 ..< length qs]"
  have len_ps: "length ps = length qs" by (simp add: ps_def)
  from ps' have
    res: "\<forall>i < length qs. ps ! i \<in> ta_res TA (adapt_vars (ts ! i))" and
    ps: "qs = map f ps"
  by (auto simp: ps_def intro: nth_equalityI)
  from res ground have p_in_states: "p \<in> set ps \<Longrightarrow>  p \<in> ta_states TA" for p
    by (auto simp: len_ps in_set_conv_nth)
       (meson ground_adapt_vars rev_subsetD ta_res_states)
  from rule[unfolded ps] obtain p' where rule: "g ps \<rightarrow> p' \<in> ta_rules TA" "q' = f p'"
    by (auto simp: fmap_states_ta_def image_iff, case_tac x)
       (auto dest!: map_inj_on intro!: subset_inj_on[OF assms(1)] intro: p_in_states rq_states(2))
  then have p'_in_states: "p' \<in> ta_states TA" by (auto intro: rq_states)
  from eps rule(2) have "\<exists>p. (p', p) \<in> (ta_eps TA)\<^sup>* \<and> q = f p"
  proof (induction rule: rtrancl.induct)
    case (rtrancl_refl x)
      then show ?case by (auto intro!: exI[of _ x]) next
    case prems: (rtrancl_into_rtrancl x y z)
      from prems obtain fy where fy: "(p', fy) \<in> (ta_eps TA)\<^sup>*" and y: "y = f fy" by blast
      from ta_eps_ta_states[OF p'_in_states this(1)] have fy_in_states: "fy \<in> ta_states TA" .
      from prems(2) obtain fz where "(fy, fz) \<in> ta_eps TA" "z = f fz"
        by (auto simp: fmap_states_ta_def y fy_in_states dest!: inj_onD[OF assms(1)])
           (auto simp: ta_states_def)
      with fy show ?case by (auto intro: exI[of _ fz])
  qed
  from this obtain p where "(p', p) \<in> (ta_eps TA)\<^sup>*" "q = f p" by blast
  with rule res show ?case by (simp) 
    (rule exI[of _ p], simp, rule exI[of _ p'], rule exI[of _ ps], auto simp: len len_ps)
qed simp

lemma fmap_ta:
  assumes "inj_on f (ta_states TA)"
    shows "ta_det (fmap_states_ta f TA) = ta_det TA" (is "ta_det ?fta = ta_det TA")
      and "ta_lang (fmap_states_ta f TA) = ta_lang TA"
proof -
  let ?rep_rule = "\<lambda>r. case r of f qs \<rightarrow> q \<Rightarrow> f (map f qs) \<rightarrow> f q"
  have qfin_states: "q \<in> ta_final TA \<Longrightarrow> q \<in> ta_states TA" for q and TA :: "('x, 'y) ta"
    unfolding ta_states_def by blast

  {
    fix f qs q and TA :: "('x, 'y) ta" assume *: "f qs \<rightarrow> q \<in> ta_rules TA"
    then have "q \<in> ta_states TA" "p \<in> set qs \<Longrightarrow> p \<in> ta_states TA" for p
      by (simp_all add: r_rhs_def ta_states_def r_states_def split: ta_rule.splits) blast+
  } note rq_states = this

  {
    fix g qs q assume "g qs \<rightarrow> q \<in> ta_rules ?fta"
    then have "\<exists>ps p. g ps \<rightarrow> p \<in> ta_rules TA \<and> qs = map f ps \<and> q = f p"
      by (force simp: fmap_states_ta_def Let_def split: ta_rule.splits)
  } note ps_rule = this

  have eps_states: 
    "(x, y) \<in> (ta_eps TA)\<^sup>+ \<Longrightarrow> x \<in> ta_states TA"
    "(x, y) \<in> (ta_eps TA)\<^sup>+ \<Longrightarrow> y \<in> ta_states TA"
  for x y and TA :: "('x, 'y) ta" by (induction rule: trancl_induct) (auto simp: ta_states_def)

  show "ta_det ?fta = ta_det TA" proof -
  {
    assume det: "ta_det ?fta"
    then have "ta_det TA" unfolding ta_det_def[of TA]
    proof (intro conjI impI allI, simp add: ta_det_def fmap_states_ta_def)
      fix g qs q q' assume rule: "g qs \<rightarrow> q \<in> ta_rules TA" "g qs \<rightarrow> q' \<in> ta_rules TA"
      then have "g (map f qs) \<rightarrow> f q \<in> ta_rules ?fta" "g (map f qs) \<rightarrow> f q' \<in> ta_rules ?fta"
        by (auto simp: fmap_states_ta_def image_iff split: ta_rule.split)
      with det have "f q = f q'" by (auto simp: ta_det_def)
      moreover from rule have "q \<in> ta_states TA" "q' \<in> ta_states TA" by (auto intro: rq_states)
      ultimately show "q = q'" using assms by (auto dest: inj_onD)
    qed
  } moreover {
    assume det: "ta_det TA"
    then have "ta_det ?fta" unfolding ta_det_def[of ?fta]
    proof (intro conjI impI allI, simp add: ta_det_def fmap_states_ta_def)
      fix g qs q q' assume rule: "g qs \<rightarrow> q \<in> ta_rules ?fta" "g qs \<rightarrow> q' \<in> ta_rules ?fta"
      from this[THEN ps_rule] obtain ps ps' p p' where
        rules: "g ps \<rightarrow> p \<in> ta_rules TA" "g ps' \<rightarrow> p' \<in> ta_rules TA" and 
        sorted: "qs = map f ps" "qs = map f ps'" "q = f p" "q' = f p'"
      by blast
      from sorted assms have "ps' = ps"
      by (auto dest!: rules[THEN rq_states(2)] inj_onD intro!: list.inj_map_strong[of ps' ps f f])
      with rules det have "p = p'" by (simp add: ta_det_def)
      then show "q = q'" by (simp add: sorted)
    qed
  }
  ultimately show ?thesis by blast
  qed
  show "ta_lang ?fta = ta_lang TA" (is "?L = ?R") proof standard
    show "?R \<subseteq> ?L"  proof standard
      fix t assume "t \<in> ?R"
      from this obtain p where
        res: "p \<in> ta_res TA (adapt_vars t)" and
        final: "p \<in> ta_final TA" and
        ground: "ground t"
      by (auto simp: ta_lang_def)
      from res ground have "f p \<in> ta_res ?fta (adapt_vars t)" proof (induction t arbitrary: p)
        case (Fun g ts)
          from this obtain ps p' where
            rule: "g ps \<rightarrow> p' \<in> ta_rules TA" and
            res: "\<forall>i < length ps. ps ! i \<in> ta_res TA (adapt_vars (ts ! i)) \<and> ground (ts ! i)" and 
            len: "length ps = length ts" and
            eps: "(p', p) \<in> (ta_eps TA)\<^sup>*"
          by auto
          with Fun.IH have "\<forall>i < length ps. f (ps ! i) \<in> ta_res ?fta (adapt_vars (ts ! i))" by auto
          moreover from rule have "g (map f ps) \<rightarrow> f p' \<in> ta_rules ?fta"
            by (auto simp: fmap_states_ta_def image_iff split: ta_rule.splits)
          moreover from eps have "(f p', f p)  \<in> (ta_eps ?fta)\<^sup>*"
          proof (induction rule: rtrancl_induct)
            case (step x y)
              then have "(f x, f y) \<in> ta_eps ?fta" by (auto simp: fmap_states_ta_def)
              with step show ?case by (auto intro: rtrancl_into_rtrancl)
          qed simp
          ultimately show ?case by (auto intro!: exI[of _ "map f ps"] simp: len)
      qed simp
      moreover from final have "f p \<in> ta_final ?fta" by (auto simp: fmap_states_ta_def)
      ultimately show "t \<in> ?L" using ground by (auto intro: ta_langI2)
    qed
    show "?L \<subseteq> ?R" proof standard
      fix t assume "t \<in> ?L"
      from this obtain q where
        res: "q \<in> ta_res ?fta (adapt_vars t)" and
        final: "q \<in> ta_final ?fta" and
        ground: "ground t"
        by (auto simp: ta_lang_def)
      from ta_res_fmap_states_inv[OF assms ground res] this
      obtain p where p: "p \<in> ta_res TA (adapt_vars t)" "q = f p" by blast
      with ground have "p \<in> ta_states TA" by (meson ground_adapt_vars rev_subsetD ta_res_states)
      with p final have "p \<in> ta_final TA"
        by (auto simp:  fmap_states_ta_def dest!: inj_onD[OF assms] intro!: qfin_states)
      with p ground show "t \<in> ?R" by (auto intro: ta_langI2)
    qed
  qed
qed

end
