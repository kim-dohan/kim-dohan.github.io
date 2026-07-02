theory Tree_Automata_Det
imports         
  Tree_Automata
begin

section \<open>Powerset Construction for Tree Automata\<close>

text \<open>
The idea to treat states and transitions separately is from arXiv:1511.03595. Some parts of
the implementation are also based on that paper. (The Algorithm corresponds roughly to the one
in "Step 5")
\<close>

subsection \<open>Abstract Definitions and Correctness Proof\<close>

notation TA_rule ("_ _ \<rightarrow> _" [51, 51, 51] 52)

definition "ps_state eps rules f ps \<equiv> 
  {q' | qs q q'. f qs \<rightarrow> q \<in> rules \<and> list_all2 (\<in>) qs ps \<and> (q,q') \<in> eps\<^sup>*}"

text \<open>
A set of "powerset states" is complete if it is sufficient to capture all (non)deterministic
derivations.
\<close>

definition "ps_states_complete_it eps rules Q Qnext \<equiv>
  \<forall>f ps. set ps \<subseteq> Q \<and> ps_state eps rules f ps \<noteq> {} \<longrightarrow> ps_state eps rules f ps \<in> Qnext"

abbreviation "ps_states_complete eps rules Q \<equiv> ps_states_complete_it eps rules Q Q"

text \<open>The least complete set of states\<close>
inductive_set ps_states for eps rules where
  "\<lbrakk>\<forall>p \<in> set ps. p \<in> ps_states eps rules; ps_state eps rules f ps \<noteq> {}\<rbrakk>
    \<Longrightarrow> ps_state eps rules f ps \<in> ps_states eps rules"

lemma ps_states_complete:
  "ps_states_complete eps rules (ps_states eps rules)"
unfolding ps_states_complete_it_def by (auto intro: ps_states.intros)

lemma ps_states_least_complete:
  assumes "ps_states_complete_it eps rules Q Qnext" "Qnext \<subseteq> Q"
    shows "ps_states eps rules \<subseteq> Q"
proof standard
  fix q assume "q \<in> ps_states eps rules"
  then show "q \<in> Q" proof (induction rule: ps_states.induct)
    case prems : (1 ps f)
      from prems(1) have "set ps \<subseteq> Q" by auto
      with prems(2) have "ps_state eps rules f ps \<in> Qnext"
        by (auto intro: assms[unfolded ps_states_complete_it_def, rule_format])
      with assms show ?case by blast
  qed
qed

definition "ps_rules eps rules Q \<equiv>
  {f ps \<rightarrow> p | f ps p. set ps \<subseteq> Q \<and> p = ps_state eps rules f ps \<and> p \<noteq> {}}"

lemma ps_rules_sound:
  fixes eps rules Q final final'
  defines "ta \<equiv> \<lparr>ta_final = final, ta_rules = rules, ta_eps = eps\<rparr>"
  defines "pta \<equiv> \<lparr>ta_final = final', ta_rules = ps_rules eps rules Q, ta_eps = {}\<rparr>"
  assumes ground: "ground t"
      and res: "p \<in> ta_res pta (adapt_vars t)"
    shows "p \<subseteq> ta_res ta (adapt_vars t)"
using ground res proof (induction t arbitrary: p)
  case (Fun f ts p)
    have "ta_eps pta = {}" by (simp add: pta_def)
    with Fun.prems obtain ps where
      rule: "f ps \<rightarrow> p \<in> ta_rules pta" and
      len: "length ps = length ts" and
      eps: "\<forall>i < length ts. ps!i \<in> ta_res pta (adapt_vars (ts!i)) \<and> ground (ts!i)" by auto
    from this Fun.IH have IH: "\<forall>i < length ts. ps!i \<subseteq> ta_res ta (adapt_vars (ts!i))" by auto
    show ?case proof standard
      fix q assume "q \<in> p"
      with rule obtain qs q' where "f qs \<rightarrow> q' \<in> rules" "(q',q) \<in> eps\<^sup>*" "list_all2 (\<in>) qs ps"
        unfolding pta_def ps_rules_def ps_state_def by auto
      with IH len show "q \<in> ta_res ta (adapt_vars (Fun f ts))"
        by (auto intro!: exI[of _ q'] exI[of _ qs] simp: ta_def list_all2_conv_all_nth) blast
    qed
qed simp

lemma ps_rules_complete:
  fixes eps rules final final'
  defines "Q \<equiv> ps_states eps rules"
  defines "ta \<equiv> \<lparr>ta_final = final, ta_rules = rules, ta_eps = eps\<rparr>"
  defines "pta \<equiv> \<lparr>ta_final = final', ta_rules = ps_rules eps rules Q, ta_eps = {}\<rparr>"
  assumes ground: "ground t"
      and res: "q \<in> ta_res ta (adapt_vars t)"
    shows "\<exists>p. q \<in> p \<and> p \<in> ta_res pta (adapt_vars t) \<and> p \<in> Q"
using ground res proof (induction t arbitrary: q)
  let ?P = "\<lambda>t q p. q \<in> p \<and> p \<in> ta_res pta (adapt_vars t) \<and> p \<in> Q"
  case (Fun f ts)
    from Fun.prems obtain qs q' where
      rule: "f qs \<rightarrow> q' \<in> rules" and
      eps: "(q',q) \<in> eps\<^sup>*" and
      len: "length qs = length ts" and
      "\<forall>i < length ts. qs!i \<in> ta_res ta (adapt_vars (ts!i)) \<and> ground (ts!i)" by (auto simp: ta_def)
    with Fun.IH have "\<forall>i. \<exists>p. i < length ts \<longrightarrow> ?P (ts!i) (qs!i) p" by auto
    with choice[OF this] obtain psf where ps: "\<forall>i < length ts. ?P (ts!i) (qs!i) (psf i)" by auto
    define ps where "ps = map psf [0 ..< length ts]"
    let ?p = "ps_state eps rules f ps"
    from ps have in_Q: "set ps \<subseteq> Q" by (auto simp: ps_def)
    from ps len have "list_all2 (\<in>) qs ps" by (auto simp: list_all2_conv_all_nth ps_def)
    with rule eps have in_p: "q \<in> ?p" unfolding ps_state_def by auto
    with in_Q have rule: "f ps \<rightarrow> ?p \<in> ps_rules eps rules Q" unfolding ps_rules_def by blast
    from in_Q in_p have "?p \<in> Q" by (auto simp: Q_def intro!: ps_states_complete[unfolded ps_states_complete_it_def, rule_format])
    with in_p ps rule show ?case by (auto intro!: exI[of _ ?p] exI[of _ ps] simp: pta_def ps_def)
qed simp

definition ps_ta :: "('q, 'f) ta \<Rightarrow> ('q set, 'f) ta" where
  "ps_ta TA \<equiv>
    let eps = ta_eps TA;
        rules = ta_rules TA;
        Q = ps_states eps rules;
        final = {q \<in> Q. q \<inter> ta_final TA \<noteq> {}} in
        \<lparr>ta_final = final, ta_rules = ps_rules eps rules Q, ta_eps = {}\<rparr>"

lemma ps_ta_eps[simp]: "ta_eps (ps_ta TA) = {}" by (auto simp: Let_def ps_ta_def)

lemma ps_ta_det[iff]: "ta_det (ps_ta TA)" by (auto simp: Let_def ps_ta_def ta_det_def ps_rules_def)

lemma ps_ta_lang:
  "(ta_lang TA :: ('f,'x) term set) = ta_lang (ps_ta TA)" (is "?L = ?R")
proof standard
  obtain rules eps final where
    TA: "TA = \<lparr>ta_final = final, ta_rules = rules, ta_eps = eps\<rparr>" by (cases TA)
  show "?L \<subseteq> ?R" proof standard
    fix t :: "('f,'x) term" assume "t \<in> ?L"
    from this obtain q where
      q_res: "q \<in> ta_res TA (adapt_vars t)" and q_final: "q \<in> ta_final TA" and
      t: "ground t"
    by (auto simp: ta_lang_def)
    from ps_rules_complete[OF t q_res[unfolded TA]] obtain p where
      "p \<in> ps_states eps rules" "q \<in> p" "p \<in> ta_res (ps_ta TA) (adapt_vars t)"
    by (auto simp: ps_ta_def Let_def TA)
    moreover with q_final have "p \<in> ta_final (ps_ta TA)" by (auto simp: ps_ta_def Let_def TA)
    ultimately show "t \<in> ?R" using t by (auto intro!: ta_langI2)
  qed
  show "?R \<subseteq> ?L" proof standard
    fix t :: "('f,'x) term" assume "t \<in> ?R"
    from this obtain p where
      p_res: "p \<in> ta_res (ps_ta TA) (adapt_vars t)" and p_final: "p \<in> ta_final (ps_ta TA)" and
      t: "ground t"
    by (auto simp: ta_lang_def)
    from ps_rules_sound[OF t p_res[unfolded ps_ta_def Let_def]] have
      "p \<subseteq> ta_res TA (adapt_vars t)" by (auto simp: TA)
    moreover from p_final obtain q where "q \<in> p" "q \<in> ta_final TA" by (auto simp: ps_ta_def Let_def)
    ultimately show "t \<in> ?L" using t by (auto intro!: ta_langI2)
  qed
qed

lemma ps_ta_states:
  "ta_states (ps_ta TA) \<subseteq> Pow (r_rhs ` (ta_rules TA) \<union> snd ` (ta_eps TA))" (is "?L \<subseteq> ?R")
proof -
  let ?rules = "ta_rules TA" and ?eps = "ta_eps TA"
  have state: "ps_state ?eps ?rules f ps \<in> ?R" for f ps
  by (auto simp: ps_state_def image_iff dest!: rtranclD)
     (auto dest!: tranclD2 simp: r_rhs_def split: ta_rule.splits)
  moreover then have "ps_states ?eps ?rules \<subseteq> ?R" by (auto elim!: ps_states.cases)
  ultimately show "?L \<subseteq> ?R"
    by (auto simp: ta_states_def r_states_def ps_ta_def Let_def r_lhs_states_def ps_rules_def)+
qed

lemma ps_ta_finite:
  assumes "finite (ta_rules TA)" "finite (ta_eps TA)"
    shows "finite (ta_rules (ps_ta TA))"
proof -
  let ?Q = "ta_states (ps_ta TA)"
  let ?sym = "r_sym ` ta_rules TA"
  define args where "args \<equiv> \<Union>(f,n) \<in> ?sym. {qs. set qs \<subseteq> ?Q \<and> length qs = n}"
  define bound where "bound \<equiv> \<Union>(f,_) \<in> ?sym. \<Union>q \<in> ?Q. \<Union>qs \<in> args. {f qs \<rightarrow> q}"
  from assms ps_ta_states have finite: "finite ?Q" "finite ?sym" by (auto intro: finite_subset)
  then have "finite args" by (auto intro!: finite_lists_length_eq[OF \<open>finite ?Q\<close>] simp only: args_def)
  with finite have "finite bound" unfolding bound_def by (auto simp only: finite_UN)
  moreover have "ta_rules (ps_ta TA) \<subseteq> bound" proof standard
    fix r assume *: "r \<in> ta_rules (ps_ta TA)"
    obtain f ps p where r[simp]: "r = f ps \<rightarrow> p" by (cases r)
    from * obtain qs q where "f qs \<rightarrow> q \<in> ta_rules TA" and len: "length ps = length qs"
      by (auto simp: ps_ta_def Let_def ps_rules_def ps_state_def dest: list_all2_lengthD)
    from this have sym: "(f, length qs) \<in> ?sym" by force
    moreover from * have "set ps \<subseteq> ?Q"
      by (auto simp only: r ta_states_def r_states_def intro!: exI[of _ "f ps \<rightarrow> p"] )
         (auto intro: bexI[of _ "f ps \<rightarrow> p"])
    ultimately have ps: "ps \<in> args" by (auto simp only: args_def UN_iff intro!: bexI[of _ "(f, length qs)"] len)  
    from * have "p \<in> ?Q"
      by (auto simp only: r ta_states_def r_states_def intro!: exI[of _ "f ps \<rightarrow> p"] )
         (auto intro: bexI[of _ "f ps \<rightarrow> p"])
    with ps sym show "r \<in> bound"
      by (auto simp only: r bound_def UN_iff intro!: bexI[of _ "(f, length qs)"] bexI[of _ "p"] bexI[of _ "ps"])
  qed
  ultimately show ?thesis by (blast intro: finite_subset)
qed

subsection \<open>Abstract Implementation\<close>

definition "ps_states_new eps rules Q \<equiv>
  {q | q ps f. set ps \<subseteq> Q \<and> q = ps_state eps rules f ps \<and> q \<noteq> {}}"

lemma ps_states_new_complete:
  "ps_states_complete_it eps rules Q (ps_states_new eps rules Q)"
unfolding ps_states_complete_it_def ps_states_new_def by auto

lemma ps_states_new_increase:
  assumes "Q \<subseteq> ps_states_new eps rules Q"
  shows "ps_states_new eps rules Q \<subseteq> ps_states_new eps rules (ps_states_new eps rules Q)" (is "?L \<subseteq> ?R")
proof standard
  fix p assume *: "p \<in> ?L"
  from this obtain ps f where "set ps \<subseteq> Q" and p: "p = ps_state eps rules f ps" by (auto simp: ps_states_new_def)
  with assms have ps: "set ps \<subseteq> ps_states_new eps rules Q" by blast
  from * have "p \<noteq> {}" unfolding ps_states_new_def by blast
  with ps p show "p \<in> ?R" unfolding ps_states_new_def[where Q = "ps_states_new eps rules Q"] by blast
qed

lemma ps_states_new_bound:
  "ps_states_new eps rules Q \<subseteq> Pow (r_rhs ` rules \<union> snd ` eps)"
unfolding ps_states_new_def ps_state_def by (auto, erule rtranclE) force+

definition ps_states_impl where
  "ps_states_impl eps rules \<equiv>
    let Qinit = ps_states_new eps rules {} in
    while (\<lambda>(Qold, Qnew). \<not>(Qnew \<subseteq> Qold))
      (\<lambda>(Qold, Qnew). (Qnew, ps_states_new eps rules Qnew))
    ({}, Qinit)"

lemma ps_states_impl_correct:
  assumes "finite eps" "finite rules"
  defines "P \<equiv> \<lambda>(Q,Qnext). ps_states_complete_it eps rules Q Qnext \<and> Qnext \<subseteq> Q \<and>
                            Q \<subseteq> ps_states eps rules"
  shows "P (ps_states_impl eps rules)"
proof -
  let ?inv = "\<lambda>(old, new).
    ps_states_complete_it eps rules old new \<and>
    old \<subseteq> new \<and>
    new = ps_states_new eps rules old \<and>
    old \<subseteq> ps_states eps rules"
  let ?ub = "Pow (r_rhs ` rules \<union> snd ` eps)"
  let ?r = "{(A,B). fst B \<subset> fst A \<and> fst A \<subseteq> ?ub}"
  show ?thesis unfolding ps_states_impl_def Let_def P_def
  proof (rule while_rule[where P = "?inv" and r = "?r"], goal_cases)
  case prems : (2 old_new)
    obtain old new where [simp]: "old_new = (old, new)" by (cases old_new)
    have "ps_states_complete_it eps rules new (ps_states_new eps rules new)" by (simp add: ps_states_new_complete)
    moreover from prems have "new \<subseteq> ps_states_new eps rules new" by (auto intro!: ps_states_new_increase)
    moreover have "new \<subseteq> ps_states eps rules" proof standard
      fix q assume "q \<in> new"
      with prems have "q \<in> ps_states_new eps rules old" by auto
      from this obtain f ps where "set ps \<subseteq> old" and q: "q = ps_state eps rules f ps" "q \<noteq> {}"
        unfolding ps_states_new_def by auto
      with prems have "set ps \<subseteq> ps_states eps rules" by auto
      with q show "q \<in> ps_states eps rules" by (auto intro!: ps_states.intros)
    qed
    ultimately show ?case by auto
  next
  case (4)     
    then show ?case using assms by (intro wf_bounded_set[where f = fst and ub = "const ?ub"]) auto
  next
  case prems : (5 old_new)
    obtain old new where [simp]: "old_new = (old, new)" by (cases old_new)
    from prems have "old \<subset> ps_states_new eps rules old" by auto
    with prems show ?case by (auto intro!: ps_states_new_bound)
  qed (auto intro: ps_states_new_complete)
qed

lemma ps_states_impl:
  assumes "finite eps" "finite rules"
    shows "ps_states eps rules = fst (ps_states_impl eps rules)" (is "?L = ?R")
proof standard
  let ?impl = "ps_states_impl eps rules"
  from ps_states_impl_correct[OF assms] have 
    "ps_states_complete_it eps rules (fst ?impl) (snd ?impl)"
    "(snd ?impl) \<subseteq> (fst ?impl)"
  by auto
  from ps_states_least_complete[OF this] show "?L \<subseteq> ?R" . 
  from ps_states_impl_correct[OF assms] show "?R \<subseteq> ?L" by auto
qed

end
