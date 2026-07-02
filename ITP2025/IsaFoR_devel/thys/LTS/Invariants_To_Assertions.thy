theory Invariants_To_Assertions
  imports 
    Cooperation_Program
begin

context lts
begin

definition change_assertion where
  "change_assertion P A = \<lparr> lts.initial = lts.initial P, transition_rules = transition_rules P, assertion = A \<rparr>"

lemma invariants_to_assertion_reachable_states:
  assumes inv: "invariants P \<Phi>"
  and A: "\<And> l. assertion P l \<and>\<^sub>f \<Phi> l \<Longrightarrow>\<^sub>f A l" "\<And> l. formula (A l)"
  shows "reachable_states P \<subseteq> reachable_states (change_assertion P A)" (is "?l \<subseteq> ?r")
proof(intro subsetI)
  note inv = invariantD[OF invariantsD[OF inv]]
  fix s assume "s \<in> ?l"
  then obtain n where "s \<in> ((transition P)^^n) `` initial_states P" by fast
  then show "s \<in> ?r"
  proof (induct n arbitrary: s)
    case 0
    then have reach: "s \<in> reachable_states P" by auto
    obtain l \<alpha> where s[simp]: "s = State \<alpha> l" by (cases s, auto)
    with 0 have "l \<in> lts.initial P" "\<alpha> \<Turnstile> assertion P l" and \<alpha>: "assignment \<alpha>" by (auto simp: initial_states_def)
    with impliesD[OF A(1) \<alpha>, of l] inv[OF reach[unfolded s]] A(2)
    have "s \<in> initial_states (change_assertion P A)" by (auto simp: change_assertion_def initial_states_def)
    then show ?case by (auto simp: change_assertion_def initial_states_def)
  next
    case (Suc n)
    then obtain t where tPn: "t \<in> ((transition P)^^n) `` initial_states P" and tsP: "(t,s) \<in> transition P" by auto
    obtain l \<alpha> where t: "t = State \<alpha> l" by (cases t, auto)
    obtain r \<beta> where s: "s = State \<beta> r" by (cases s, auto)
    from tPn have tP: "t \<in> ?l" by (auto simp: rtrancl_is_UN_relpow)
    from reachable_state[OF tP] t have Pl: "\<alpha> \<Turnstile> assertion P l" and \<alpha>: "assignment \<alpha>" by auto
    from inv[OF tP[unfolded t]] impliesD[OF A(1) \<alpha>, of l] tP Pl have Al: "\<alpha> \<Turnstile> A l" by auto
    from rtrancl_image_advance[OF tP tsP] have sP: "s \<in> ?l".
    from reachable_state[OF sP] s have Pr: "\<beta> \<Turnstile> assertion P r" and \<beta>: "assignment \<beta>" by auto
    from inv[OF sP[unfolded s]] impliesD[OF A(1) \<beta>, of r] sP Pr have Ar: "\<beta> \<Turnstile> A r" by auto
    from tsP obtain \<tau> where "\<tau> \<in> transition_rules P" "(t,s) \<in> transition_step_lts P \<tau>" by (auto simp: transition_def)
    with \<alpha> \<beta> Al Ar have "(t,s) \<in> transition (change_assertion P A)" by (auto simp: change_assertion_def s t)
    with rtrancl_image_advance[OF Suc(1)[OF tPn]]
    show ?case by auto
  qed
qed

lemma invariants_to_assertion: assumes inv: "invariants P \<Phi>"
  and SN: "cooperation_SN Q"
  and J: "\<And> l. assertion P l \<and>\<^sub>f \<Phi> l \<Longrightarrow>\<^sub>f \<Psi> l" "\<And> l. formula (\<Psi> l)" 
  and Q: "Q = \<lparr> lts.initial = lts.initial P, transition_rules = transition_rules P, assertion = \<Psi> \<rparr>" (is "_ = ?Q")
shows "cooperation_SN P"
proof -
  have "flat_transitions_of P \<union> sharp_transitions_of P = transition_rules P" 
    by auto
  then have id: "(\<Union> (transition_step_lts P ` (flat_transitions_of P \<union> sharp_transitions_of P)))\<^sup>* `` initial_states P
    = reachable_states P" 
    unfolding transition_def by simp
  {
    fix s
    assume reach: "s \<in> reachable_states P"
    obtain l \<alpha> where s: "s = State \<alpha> l" by (cases s, auto)
    from reachable_state[OF reach]
    have al: "\<alpha> \<Turnstile> assertion P l" and aP: "valuation s \<Turnstile> assertion P (location s)" 
      and v: "assignment (valuation s)" 
      by (auto simp: s)
    from inv reach[unfolded s] s
    have "valuation s \<Turnstile> \<Phi> (location s)" by auto
    from impliesD[OF J(1) v] this aP J(2)[of "location s"]
    have "valuation s \<Turnstile> \<Psi> (location s)" "formula (\<Psi> (location s))" by auto
  } note J = this
  {
    fix g
    let ?PS = "{ \<tau> \<in> transition_rules P. g \<tau> }" 
    let ?QS = "{ \<tau> \<in> transition_rules ?Q. g \<tau> }" 
    fix a b1 b2
    assume a: "a \<in> ?PS" and step: "(b1, b2) \<in> transition_step_lts P a" 
      and reach: "b1 \<in> reachable_states P" "b2 \<in> reachable_states P"
    note J = J[OF reach(1)] J[OF reach(2)]
    from J step 
    have "(b1, b2) \<in> transition_step (\<lambda>s. state s \<and> valuation s \<Turnstile> \<Psi> (location s)) a" by (cases b1; cases b2, cases a, auto)
    with a have "a \<in> ?QS \<and> (b1, b2) \<in> transition_step_lts ?Q a" by auto
  } note main = this
  {
    fix s
    assume s: "s \<in> initial_states P" 
    then have "s \<in> reachable_states P" by auto
    from J[OF this] s have "s \<in> initial_states ?Q" unfolding initial_states_def by auto
  }
  then have init:  "(\<lambda>x. x) ` initial_states P \<subseteq> initial_states ?Q" by auto
  show "cooperation_SN P" 
    by (rule cooperation_SN_on_simulation[OF _ _ _ SN[unfolded Q], of "\<lambda> x. x" _ _ _ _ "\<lambda> x. x"], 
    unfold id, rule init, (rule main, auto)[1], (rule main, auto)[1])
qed

lemma invariants_to_assertion_lts: assumes inv: "invariants P \<Phi>"
  and SN: "lts_termination Q"
  and J: "\<And> l. assertion P l \<and>\<^sub>f \<Phi> l \<Longrightarrow>\<^sub>f J l" "\<And> l. formula (J l)" 
  and Q: "Q = \<lparr> lts.initial = lts.initial P, transition_rules = transition_rules P, assertion = J \<rparr>" (is "_ = ?Q")
shows "lts_termination P"
proof 
  {
    fix s
    assume reach: "s \<in> reachable_states P"
    obtain l \<alpha> where s: "s = State \<alpha> l" by (cases s, auto)
    from reachable_state[OF reach]
    have al: "\<alpha> \<Turnstile> assertion P l" and aP: "valuation s \<Turnstile> assertion P (location s)" 
      and v: "assignment (valuation s)" 
      by (auto simp: s)
    from inv reach[unfolded s] s
    have "valuation s \<Turnstile> \<Phi> (location s)" by auto
    from impliesD[OF J(1) v] this aP J(2)[of "location s"]
    have "valuation s \<Turnstile> J (location s)" "formula (J (location s))" by auto
  } note J = this
  {
    fix s
    assume s: "s \<in> initial_states P" 
    then have "s \<in> reachable_states P" by auto
    from J[OF this] s have "s \<in> initial_states ?Q" unfolding initial_states_def by auto
  } note init = this
  fix f
  assume nSN: "f 0 \<in> initial_states P" "\<forall> i. (f i, f (Suc i)) \<in> transition P" 
  from init[OF nSN(1)] have init: "f 0 \<in> initial_states Q" unfolding Q .
  have *: "(f 0, f i) \<in> (transition P)^*" for i 
  proof (induct i)
    case (Suc i)
    from Suc nSN(2)[rule_format, of i] show ?case by auto
  qed auto
  from nSN(1) have reach: "f i \<in> reachable_states P" for i using *[of i] by auto
  {
    fix i
    from nSN(2)[rule_format, of i, unfolded transition_def]
    obtain r where r: "r \<in> transition_rules P" and step: "(f i, f (Suc i)) \<in> transition_step_lts P r" by auto
    from r have r: "r \<in> transition_rules Q" unfolding Q by auto
    from step have step: "(f i, f (Suc i)) \<in> transition_step_lts Q r" using J[OF reach[of i]] J[OF reach[of "Suc i"]]
      unfolding Q by auto
    with r have "(f i, f (Suc i)) \<in> transition Q" unfolding transition_def by auto
  }
  with init SN show False by auto
qed

definition fix_invariants :: "('f,'v,'t,'l :: showl,'tr :: showl) lts_impl \<Rightarrow> ('l \<Rightarrow> ('f,'v,'t) exp formula)
  \<Rightarrow> showsl + ('f,'v,'t,'l,'tr) lts_impl" where 
  "fix_invariants P \<Phi> = do {
      let ls = nodes_lts_impl P;
      let old = assertion_of P;
      return 
       (Lts_Impl 
         (initial P) 
         (transitions_impl P) 
         (map (\<lambda> l. (l, \<Phi> l)) ls))
    } <+? (\<lambda> s. showsl_lit (STR ''problem when fixing invariants as assertions\<newline>'') o s)"

lemma fix_invariants:
  assumes res: "fix_invariants P A = return Q"
  defines "A' \<equiv> (\<lambda>l. if l \<in> set (nodes_lts_impl P) then A l else True\<^sub>f)"
  shows "lts_of Q = change_assertion (lts_of P) A'"
proof-
  note res = res[unfolded fix_invariants_def Let_def, simplified]
  define f where "f = (\<lambda>l. (l, A l))"
  define fm where "fm = map f (nodes_lts_impl P)"
  note res = res[folded f_def fm_def]
  from res have Q: "Q = Lts_Impl (lts_impl.initial P) (transitions_impl P) fm" by auto
  have PQ: "lts_of Q = \<lparr>lts.initial = lts.initial (lts_of P), transition_rules = transition_rules (lts_of P),
       assertion = map_of_default form_True fm\<rparr>" unfolding Q by (simp add: assertion_of_def)
  also have "map_of_default form_True fm = A'"
    by (rule ext, rule map_of_defaultI2, auto simp: A'_def fm_def f_def)
  finally show ?thesis by (auto simp: change_assertion_def)
qed

lemma fix_invariants_cooperation_SN:
  assumes res: "fix_invariants P \<Phi> = return Q"
      and inv: "invariants (lts_of P) \<Phi>"
      and SN: "cooperation_SN_impl Q"
  shows "cooperation_SN_impl P"
proof
  assume lts: "lts_impl P"
  from lts_impl[OF lts, unfolded lts_def] have lc: "formula (assertion_of P l)" for l by auto
  note res = res[unfolded fix_invariants_def Let_def, simplified]
  define f where "f = (\<lambda>l. (l, \<Phi> l))"
  from inv have "formula (\<Phi> l)" for l by auto
  then have form: "formula (snd (f l))" for l unfolding f_def
    using lc[of l] lts_impl[OF lts]
    by (auto simp: lts_def)
  have form': "(a,g) = f l \<Longrightarrow> formula g" for a g l using form[of l] by (cases "f l", auto)
  define fm where "fm = map f (nodes_lts_impl P)"
  note res = res[folded f_def fm_def]
  from res have Q: "Q = Lts_Impl (lts_impl.initial P) (transitions_impl P) fm" by auto
  have PQ: "lts_of Q = \<lparr>lts.initial = lts.initial (lts_of P), transition_rules = transition_rules (lts_of P),
       assertion = map_of_default form_True fm\<rparr>" unfolding Q by (simp add: assertion_of_def)
  from lts form' have lts: "lts_impl Q" by (auto simp: Q fm_def f_def elim: lts_implE)
  show "indexed_rewriting.cooperation_SN_on (transition_step_lts (lts_of P)) (flat_transitions_of (lts_of P)) (sharp_transitions_of (lts_of P)) (initial_states (lts_of P))"      
  proof (rule invariants_to_assertion[OF inv _ _ _ PQ])
    show "cooperation_SN (lts_of Q)" using SN lts by auto
    fix l
    let ?f = "map_of_default True\<^sub>f fm l" 
    let ?P = "\<lambda> f. f = True\<^sub>f \<or> (l \<in> set (nodes_lts_impl P) \<and> f = \<Phi> l)"
    note d = map_of_default_def lookup_default_def lookup_of_alist
    have choice: "?P ?f" 
    proof (cases "map_of fm l")
      case (Some f)
      with map_of_SomeD[OF this]
      show ?thesis unfolding d by (auto simp: fm_def f_def)
    qed (auto simp: d)
    from inv have Il: "formula (\<Phi> l)" by auto
    from choice show "formula (map_of_default True\<^sub>f fm l)"
      by (auto simp: lc Il)
    show "assertion (lts_of P) l \<and>\<^sub>f \<Phi> l \<Longrightarrow>\<^sub>f map_of_default True\<^sub>f fm l" 
      using choice by auto
  qed
qed 

lemma fix_invariants_lts:
  assumes res: "fix_invariants P \<Phi> = return Q"
      and inv: "invariants (lts_of P) \<Phi>"
      and SN: "lts_impl Q \<Longrightarrow> lts_termination (lts_of Q)"
  shows "lts_impl P \<Longrightarrow> lts_termination (lts_of P)"
proof -
  assume lts: "lts_impl P"
  from lts_impl[OF lts, unfolded lts_def] have lc: "formula (assertion_of P l)" for l by auto
  note res = res[unfolded fix_invariants_def Let_def, simplified]
  define f where "f = (\<lambda>l. (l, \<Phi> l))"
  from inv have "formula (\<Phi> l)" for l by auto
  then have form: "formula (snd (f l))" for l unfolding f_def
    using lc[of l] lts_impl[OF lts]
    by (auto simp: lts_def)
  have form': "(a,g) = f l \<Longrightarrow> formula g" for a g l using form[of l] by (cases "f l", auto)
  define fm where "fm = map f (nodes_lts_impl P)"
  note res = res[folded f_def fm_def]
  from res have Q: "Q = Lts_Impl (lts_impl.initial P) (transitions_impl P) fm" by auto
  have PQ: "lts_of Q = \<lparr>lts.initial = lts.initial (lts_of P), transition_rules = transition_rules (lts_of P),
       assertion = map_of_default form_True fm\<rparr>" unfolding Q by (simp add: assertion_of_def)
  from lts form' have lts: "lts_impl Q" by (auto simp: Q fm_def f_def elim: lts_implE)
  show "lts_termination (lts_of P)" 
  proof (rule invariants_to_assertion_lts[OF inv _ _ _ PQ])
    show "lts_termination (lts_of Q)" using SN lts by auto
    fix l
    let ?f = "map_of_default True\<^sub>f fm l" 
    let ?P = "\<lambda> f. f = True\<^sub>f \<or> (l \<in> set (nodes_lts_impl P) \<and> f = \<Phi> l)"
    note d = map_of_default_def lookup_default_def lookup_of_alist
    have choice: "?P ?f" 
    proof (cases "map_of fm l")
      case (Some f)
      with map_of_SomeD[OF this]
      show ?thesis unfolding d by (auto simp: fm_def f_def)
    qed (auto simp: d)
    from inv have Il: "formula (\<Phi> l)" by auto
    from choice show "formula (map_of_default True\<^sub>f fm l)"
      by (auto simp: lc Il)
    show "assertion (lts_of P) l \<and>\<^sub>f \<Phi> l \<Longrightarrow>\<^sub>f map_of_default True\<^sub>f fm l" 
      using choice by auto
  qed
qed

lemma fix_invariants_safety:
  assumes res: "fix_invariants P \<Phi> = return Q"
      and inv: "invariants (lts_of P) \<Phi>"
      and safe: "lts_impl Q \<Longrightarrow> lts_safe (lts_of Q) errs"
  shows "lts_impl P \<Longrightarrow> lts_safe (lts_of P) errs"
proof(unfold lts_safe_def, intro allI impI)
  assume lts: "lts_impl P"
  from lts_impl[OF lts, unfolded lts_def] have lc: "formula (assertion_of P l)" for l by auto
  note res2 = res[unfolded fix_invariants_def Let_def, simplified]
  define f where "f = (\<lambda>l. (l, \<Phi> l))"
  from inv have "formula (\<Phi> l)" for l by auto
  then have form: "formula (snd (f l))" for l unfolding f_def
    using lc[of l] lts_impl[OF lts]
    by (auto simp: lts_def)
  have form': "(a,g) = f l \<Longrightarrow> formula g" for a g l using form[of l] by (cases "f l", auto)
  define fm where "fm = map f (nodes_lts_impl P)"
  note res2 = res2[folded f_def fm_def]
  from res2 have Q: "Q = Lts_Impl (lts_impl.initial P) (transitions_impl P) fm" by auto
  have PQ: "lts_of Q = \<lparr>lts.initial = lts.initial (lts_of P), transition_rules = transition_rules (lts_of P),
       assertion = map_of_default form_True fm\<rparr>" unfolding Q by (simp add: assertion_of_def)
  from lts form' have "lts_impl Q" by (auto simp: Q fm_def f_def elim: lts_implE)
  note safe = safe[OF this]

  fix l \<alpha> assume "l \<in> errs"
  with safe[unfolded lts_safe_def] have "State \<alpha> l \<notin> reachable_states (lts_of Q)" by auto
  moreover have "reachable_states (lts_of P) \<subseteq> reachable_states (lts_of Q)"
    unfolding fix_invariants[OF res]
    apply (rule invariants_to_assertion_reachable_states[OF inv])
    using inv lts by (auto intro: lts_impl_formula_assertion_of)
  ultimately show "State \<alpha> l \<notin> reachable_states (lts_of P)" by auto
qed

end


declare lts.fix_invariants_def[code]

  
end
