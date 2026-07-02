theory Transition_Removal
  imports 
    Cooperation_Program
    Ord.Lexicographic_Orders
    Ord.Non_Inf_Orders
begin

hide_const (open) FuncSet.Pi

datatype ('e,'t,'l,'tr,'s) transition_removal_info = Transition_removal_info
  (rank: "'l sharp \<Rightarrow> 'e")
  (removed: "'tr list")
  (dom_type: "'t")
  (bound_exp: "'e")
  (hinter: "'tr \<Rightarrow> 's")


lemma(in Order_Pair.order_pair) chain_imp_le:
  assumes chain: "chain NS seq" and ij: "i \<le> j" shows "(seq i, seq j) \<in> NS"
proof-
  have "(seq i, seq (i+k)) \<in> NS" for k
  proof(induct k)
    case 0 show ?case by (auto intro: refl_NS_point)
  next
    case (Suc k)
    have "(seq (i+k), seq (i + Suc k)) \<in> NS" using chain by auto
    from trans_NS_point[OF Suc this] show ?case by auto
  qed
  from this[of "j-i"] ij show ?thesis by auto
qed

lemma(in SN_order_pair) chain_imp_chain_not_less:
  assumes chain: "chain NS f" shows "\<exists>j. chain (NS-S) (shift f j)"
proof-
  from chain non_strict_ending[of f NS S] NS_O_S SN obtain j where 
    steps: "\<And> i. i \<ge> j \<Longrightarrow> (f i, f (Suc i)) \<in> NS - S" by (auto simp: SN_def)
  show ?thesis
    by (rule exI[of _ j], insert steps, auto)
qed

lemma(in SN_order_pair) no_chain_less[simp]: "chain S f \<longleftrightarrow> False" using SN by auto

lemma(in SN_order_pair) wf_order_set: "class.wf_order (\<lambda>x y. (y,x) \<in> NS \<union> S) (\<lambda>x y. (y,x) \<in> S)"
  apply (unfold_locales)
  apply (auto dest: trans_NS_point trans_S_point compat_NS_S_point compat_S_NS_point intro: refl_NS_point SN_induct[OF SN])
  done

context lts begin

context
  fixes less_eq less :: "'m \<Rightarrow> 'm \<Rightarrow> bool"
  assumes wf_order: "class.wf_order less_eq less"
begin

interpretation wf_order less_eq less by (fact wf_order)
interpretation ord_syntax less_eq less.

lemma transition_removal_via_rank:
  fixes rank :: "('v,'t,'d,'l sharp) state \<Rightarrow> 'm"
    and P :: "('f,'v,'t,'l sharp) lts"
  assumes TD: "\<forall>\<tau> \<in> TD. is_sharp_transition \<tau>"
      and NS: "\<And> s t \<tau>. \<tau> \<notin> TD \<Longrightarrow> \<tau> \<in> sharp_transitions_of P \<Longrightarrow> s \<in> reachable_states P \<Longrightarrow> t \<in> reachable_states P
                \<Longrightarrow> (s,t) \<in> transition_step_lts P \<tau> \<Longrightarrow> rank s \<sqsupseteq> rank t"
      and S: "\<And> s t \<tau>. \<tau> \<in> TD \<Longrightarrow> s \<in> reachable_states P \<Longrightarrow> t \<in> reachable_states P
                \<Longrightarrow> (s,t) \<in> transition_step_lts P \<tau> \<Longrightarrow> rank s \<sqsupset> rank t"
      and cSN: "cooperation_SN (delete_transitions P TD)"
  shows "cooperation_SN P"
  unfolding indexed_rewriting.cooperation_SN_on_as_SN_on_traverse
proof(intro allI impI SN_onI)
  interpret indexed_rewriting "transition_step_lts P" .
  let ?P = "delete_transitions P TD"
  fix \<tau>s seq
  assume \<tau>s: "\<tau>s \<subseteq> sharp_transitions_of P"
     and \<tau>s0: "\<tau>s \<noteq> {}"
     and init: "seq 0 \<in> transitions_steps_lts P (flat_transitions_of P) `` initial_states P"
     and chain: "chain (traverse \<tau>s) seq"
  have trans: "transitions_step_lts P \<tau>s \<subseteq> transition P" by (insert \<tau>s, auto)
  { fix i
    from chain[rule_format, of i]
    obtain subseq l
    where first: "subseq 0 = seq i" and last: "subseq l = seq (Suc i)" and trav: "traversed \<tau>s subseq l"
      by (rule mem_traverseE)
    have reach: "seq i \<in> reachable_states P"
    proof (induct i)
      case 0 show ?case by(rule subsetD[OF _ init], rule Image_subsetI, rule rtrancl_mono, auto)
    next
      case (Suc i)
      from chain have "step seq i \<in> traverse \<tau>s" by auto
      with traverse_subset_Induces[of "\<tau>s"]
      have "step seq i \<in> (transitions_step_lts P \<tau>s)\<^sup>*" by auto
      also have "... \<subseteq> (transition P)\<^sup>*" by (fact rtrancl_mono[OF trans])
      finally have "step seq i \<in> ...".
      with Suc have "seq (Suc i) \<in> (transition P)\<^sup>* `` reachable_states P" by fast
      then show ?case by auto
    qed
    { fix j \<tau>s' assume jl: "j \<le> l"
      have "traversed \<tau>s' subseq j \<Longrightarrow> \<tau>s' \<subseteq> \<tau>s \<Longrightarrow>
        subseq j \<in> reachable_states P \<and>
        (\<tau>s' \<inter> TD = {} \<longrightarrow> rank (seq i) \<sqsupseteq> rank (subseq j)) \<and>
        (\<tau>s' \<inter> TD \<noteq> {} \<longrightarrow> rank (seq i) \<sqsupset> rank (subseq j))"
      proof(insert first jl, induct rule: traversed.induct)
        case (base subseq) with reach show ?case by auto
      next
        case IH: (step \<tau>s' subseq j \<tau>')
        then have weak: "\<tau>s' \<inter> TD = {} \<Longrightarrow> rank (seq i) \<sqsupseteq> rank (subseq j)"
              and strict: "\<tau>s' \<inter> TD \<noteq> {} \<Longrightarrow> rank (seq i) \<sqsupset> rank (subseq j)"
              and step: "(subseq j, subseq (Suc j)) \<in> transition_step_lts P \<tau>'"
              and jl: "j < l"
              and \<tau>': "\<tau>' \<in> \<tau>s"
              and \<tau>s': "\<tau>s' \<subseteq> \<tau>s"
              and reach: "subseq j \<in> reachable_states P" by auto
        from IH traversed_imp_chain[OF trav] have "step subseq j \<in> transitions_step_lts P \<tau>s" by auto
        also have "... \<subseteq> transition P" by (rule trans)
        finally have "step subseq j \<in> ...".
        with reach have "subseq (Suc j) \<in> transition P `` reachable_states P" by auto
        also have "... \<subseteq> reachable_states P" by (rule rtrancl_image_unfold_right)
        finally have *: "subseq (Suc j) \<in> ...".
        have weak_step: "insert \<tau>' \<tau>s' \<inter> TD = {} \<Longrightarrow> rank (subseq j) \<sqsupseteq> rank (subseq (Suc j))"
          apply(intro NS[OF _ _ reach * step]) using \<tau>' \<tau>s \<tau>s' by auto
        also note weak
        finally have **: "insert \<tau>' \<tau>s' \<inter> TD = {} \<Longrightarrow> rank (seq i) \<sqsupseteq> rank (subseq (Suc j))" by auto
        {
          assume "insert \<tau>' \<tau>s' \<inter> TD \<noteq> {}"
          then obtain \<tau> where \<tau>: "\<tau> \<in> insert \<tau>' \<tau>s' \<inter> TD" by auto
          then consider "\<tau> = \<tau>' \<and> \<tau> \<in> TD" | "\<tau> \<in> \<tau>s' \<inter> TD" by auto
          then have "rank (seq i) \<sqsupset> rank (subseq (Suc j))"
          proof(cases)
            case 1 with reach step *
            have now: "rank (subseq j) \<sqsupset> rank (subseq (Suc j))" by(intro S[of \<tau>], auto)
            show ?thesis
            proof (cases "\<tau>s' \<inter> TD = {}")
              case True
              note now also note weak[OF True] finally show ?thesis.
            next
              case False
              note now also note strict[OF False] finally show ?thesis.
            qed
          next
            case 2
            with strict have prev: "rank (seq i) \<sqsupset> rank (subseq j)" by auto
            show ?thesis
            proof (cases "\<tau>' \<in> TD")
              case True note S[OF True reach * step] also note prev finally show ?thesis.
            next
              case False from NS[OF False _ reach * step] \<tau>' \<tau>s
              have "rank (subseq (Suc j)) \<sqsubseteq> rank (subseq j)" by auto
              also note prev finally show ?thesis.
            qed
          qed
        }
        with * ** show ?case by auto
      qed
    }
    note this[OF le_refl trav subset_refl, unfolded first last, THEN conjunct2, THEN conjunct2]
  }
  then have "\<tau> \<in> \<tau>s \<inter> TD \<Longrightarrow> chain (rel_of (\<sqsupset>)) (rank \<circ> seq)" for \<tau> by auto
  then have disj: "\<tau>s \<inter> TD = {}" using SN by blast
  with \<tau>s
  have \<tau>s2: "\<tau>s \<subseteq> sharp_transitions_of ?P" by auto
  note init
  also have "transitions_steps_lts P (flat_transitions_of P) `` initial_states P \<subseteq>
    transitions_steps_lts P (flat_transitions_of ?P) `` initial_states ?P"
    by (intro Image_mono rtrancl_mono, insert TD, auto)
  finally have init2: "seq 0 \<in> ...".
  have "\<not> SN_on (traverse \<tau>s) (Induces (flat_transitions_of ?P) `` initial_states ?P)"
    by (fact not_SN_onI[OF init2 chain])
  with \<tau>s0 \<tau>s2 have "\<not> cooperation_SN ?P" by (unfold indexed_rewriting.cooperation_SN_on_as_SN_on_traverse, auto)
  with cSN show False by auto
qed

end
end

subsection \<open>General implementation\<close>

locale pre_transition_removal = lts where type_fixer = "TYPE('f\<times>'t\<times>'d)"
  for type_fixer :: "('f \<times> 'v \<times> 't \<times> 'd \<times> 'l \<times> 'tr :: showl) itself"
  and check_weak check_strict :: "'tr \<times> ('f,'v,'t,'l sharp) transition_rule \<Rightarrow> showsl check"
  and TD :: "'tr list"
  and Pi :: "('f,'v,'t,'l sharp,'tr) lts_impl"
begin

definition "processor \<equiv>
  do {check_allm (\<lambda>(tr,\<tau>).
    (if tr \<in> set TD then
      check (is_sharp_transition \<tau>)
        (showsl_lit (STR ''non-sharp transition '') \<circ> showsl tr \<circ> showsl_lit (STR '' cannot be removed'')) \<then>
      check_strict (tr,\<tau>) <+? (\<lambda>s. showsl_lit (STR ''Failed to strictly orient transition '') \<circ> showsl tr \<circ> showsl_nl \<circ> s)
     else if is_sharp_transition \<tau> then
      check_weak (tr,\<tau>) <+? (\<lambda>s. showsl_lit (STR ''Failed to weakly orient transition '') \<circ> showsl tr \<circ> showsl_nl \<circ> s)
    else succeed)) (transitions_impl Pi)
  ;return (del_transitions_impl Pi TD)
  } <+? (\<lambda> s. showsl_lit (STR ''Failed to eliminate transitions '') \<circ> showsl_list TD \<circ> showsl_lit (STR '':\<newline>'') \<circ> s)"

lemma processorD:
  assumes "processor = return Pi'"
  shows "Pi' = del_transitions_impl Pi TD"
    and "(tr,\<tau>) \<in> set (transitions_impl Pi) \<Longrightarrow> is_sharp_transition \<tau> \<Longrightarrow>
         tr \<notin> set TD \<Longrightarrow> isOK(check_weak (tr,\<tau>))"
    and "(tr,\<tau>) \<in> set (transitions_impl Pi) \<Longrightarrow> tr \<in> set TD \<Longrightarrow> is_sharp_transition \<tau>"
    and "(tr,\<tau>) \<in> set (transitions_impl Pi) \<Longrightarrow> tr \<in> set TD \<Longrightarrow> isOK(check_strict (tr,\<tau>))"
    and "sub_lts_impl Pi' Pi" 
  using assms[unfolded processor_def]
  by (induct Pi, auto simp: del_transitions_impl_def diff_by_label_def mset_filter)

end

declare pre_transition_removal.processor_def[code]

subsection \<open>Abstract transition removal using well-founded ranking functions\<close>

locale transition_removal =
  logic where type_fixer = "TYPE('f\<times>'t\<times>'d)" +
  pre_transition_removal where type_fixer = type_fixer +
  wf_order less_eq less
  for type_fixer :: "('f \<times> 'v \<times> 't \<times> 'd \<times> 'l \<times> 'tr :: showl) itself"
  and less_eq less :: "'m \<Rightarrow> 'm \<Rightarrow> bool"
  and rank :: "('v,'t,'d,'l sharp) state \<Rightarrow> 'm" +
  assumes check_weak:
    "\<And>tr \<tau> s t.
       isOK (check_weak (tr, \<tau>)) \<Longrightarrow>
       lts_impl Pi \<Longrightarrow>
       (tr,\<tau>) \<in> set (transitions_impl Pi) \<Longrightarrow>
       s \<in> reachable_states (lts_of Pi) \<Longrightarrow>
       t \<in> reachable_states (lts_of Pi) \<Longrightarrow>
       (s, t) \<in> transition_step_lts (lts_of Pi) \<tau> \<Longrightarrow>
       less_eq (rank t) (rank s)"
  assumes check_strict: 
    "\<And>tr \<tau> s t.
       isOK (check_strict (tr, \<tau>)) \<Longrightarrow>
       lts_impl Pi \<Longrightarrow>
       (tr,\<tau>) \<in> set (transitions_impl Pi) \<Longrightarrow>
       s \<in> reachable_states (lts_of Pi) \<Longrightarrow>
       t \<in> reachable_states (lts_of Pi) \<Longrightarrow>
       (s, t) \<in> transition_step_lts (lts_of Pi) \<tau> \<Longrightarrow>
       less (rank t) (rank s)"
begin

interpretation ord_syntax less_eq less.

lemma sound:
  assumes ret: "processor = return Pi'"
      and SN: "cooperation_SN_impl Pi'"
  shows "cooperation_SN_impl Pi"
proof(intro cooperation_SN_implI transition_removal_via_rank[OF wf_order_axioms, of _ "lts_of Pi"] conjI)
  assume Pi: "lts_impl Pi"
  let ?TD = "{\<tau> | \<tau> tr. (tr,\<tau>) \<in> set (transitions_impl Pi) \<and> tr \<in> set TD}"
  note * = processorD[OF ret]
  from *(3)
  show "\<forall>\<tau> \<in> ?TD. is_sharp_transition \<tau>" by auto
  show "cooperation_SN (delete_transitions (lts_of Pi) ?TD)"
  proof(rule cooperation_SN_sub_lts)
    note del = del_transitions_impl[of Pi TD]
    show sub: "sub_lts (delete_transitions (lts_of Pi) ?TD) (lts_of (del_transitions_impl Pi TD))"
      using del by auto
    from sub_lts_impl[OF del(1) Pi] SN *
    show "cooperation_SN (lts_of (del_transitions_impl Pi TD))" by auto
  qed
  fix s t \<tau>
  assume s: "s \<in> reachable_states (lts_of Pi)" "t \<in> reachable_states (lts_of Pi)" and st: "(s, t) \<in> transition_step_lts (lts_of Pi) \<tau>"
  { assume \<tau>: "\<tau> \<notin> ?TD" "\<tau> \<in> {\<tau> \<in> transition_rules (lts_of Pi). is_sharp_transition \<tau>}"
    from \<tau> obtain tr where tr: "(tr,\<tau>) \<in> set (transitions_impl Pi)" by auto
    from \<tau>(1) tr have "tr \<notin> set TD" by auto
    with *(2)[OF tr] \<tau> have weak: "isOK (check_weak (tr, \<tau>))" by auto
    from lts_impl[OF Pi] tr show "rank s \<sqsupseteq> rank t" by (elim ltsE, auto intro!: check_weak[OF weak Pi _ s st])
  }
  { assume \<tau>: "\<tau> \<in> ?TD"
    from \<tau> obtain tr where tr: "(tr,\<tau>) \<in> set (transitions_impl Pi)" "tr \<in> set TD" by auto
    from s st lts_impl[OF Pi] tr
    show "rank s \<sqsupset> rank t" by (elim ltsE, auto intro!: check_strict[OF *(4)[OF tr] Pi])
  }
qed

end

subsection \<open>Checking ordering via formulas\<close>

text \<open>These locales are just for avoiding duplicate assumptions\<close>

locale order_checker =
  logic_checker
  for less_eq less
  and dom_type
  and less_eq_formula (infix "\<sqsubseteq>\<^sub>f" 50)
  and less_formula (infix "\<sqsubset>\<^sub>f" 50) +
  assumes less_eq_type: "\<And>s t. s :\<^sub>f dom_type \<Longrightarrow> t :\<^sub>f dom_type \<Longrightarrow> formula (s \<sqsubseteq>\<^sub>f t)"
      and less_type: "\<And>s t. s :\<^sub>f dom_type \<Longrightarrow> t :\<^sub>f dom_type \<Longrightarrow> formula (s \<sqsubset>\<^sub>f t)"
      and less_eq_encode: "\<And>\<alpha> s t. assignment \<alpha> \<Longrightarrow> s :\<^sub>f dom_type \<Longrightarrow> t :\<^sub>f dom_type \<Longrightarrow>
        \<alpha> \<Turnstile> s \<sqsubseteq>\<^sub>f t \<longleftrightarrow> less_eq (\<lbrakk>s\<rbrakk>\<alpha>) (\<lbrakk>t\<rbrakk>\<alpha>)"
      and less_encode: "\<And>\<alpha> s t. assignment \<alpha> \<Longrightarrow> s :\<^sub>f dom_type \<Longrightarrow> t :\<^sub>f dom_type \<Longrightarrow>
        \<alpha> \<Turnstile> s \<sqsubset>\<^sub>f t \<longleftrightarrow> less (\<lbrakk>s\<rbrakk>\<alpha>) (\<lbrakk>t\<rbrakk>\<alpha>)"
begin

notation less_eq_formula (infix "\<sqsubseteq>\<^sub>f" 50)
notation less_formula (infix "\<sqsubset>\<^sub>f" 50)

end

subsection \<open>Concrete transition removal via single well-founded ranking function\<close>

locale pre_transition_removal_wf =
  pre_lts_checker where type_fixer = "TYPE('f \<times> 'v trans_var \<times> 't \<times> 'd \<times> 's)"
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's::{default,showl}) itself"
  and less_eq_formula less_formula ::
    "('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp formula"
begin

notation less_eq_formula (infix "\<sqsubseteq>\<^sub>f" 50)
notation less_formula (infix "\<sqsubset>\<^sub>f" 50)

context
  fixes rank_exp :: "'l :: showl sharp \<Rightarrow> ('f,'v,'t) exp"
    and dom_type :: "'t"
    and hinter :: "'tr :: showl \<Rightarrow> 's"
    and TD :: "'tr list"
    and Pi :: "('f,'v,'t,'l sharp,'tr) lts_impl"
begin

fun check_rank_weak where
  "check_rank_weak (tr, Transition l r \<phi>) =
   check_valid_formula (hinter tr) (Disjunction [
     rename_vars Post (rank_exp r) \<sqsubseteq>\<^sub>f rename_vars Pre (rank_exp l),
     \<not>\<^sub>f rename_vars Pre (assertion_of Pi l),
     \<not>\<^sub>f \<phi>
\<comment> \<open>disabled: \<not> rename_vars Post (assertion_of Pi r) \<close>
   ])"

fun check_rank_strict where
  "check_rank_strict (tr, Transition l r \<phi>) =
     check_valid_formula (hinter tr) (Disjunction [
       rename_vars Post (rank_exp r) \<sqsubset>\<^sub>f rename_vars Pre (rank_exp l),
       \<not>\<^sub>f rename_vars Pre (assertion_of Pi l),
       \<not>\<^sub>f \<phi>
\<comment> \<open>disabled: \<not> rename_vars Post (assertion_of Pi r) \<close>
   ])"

interpretation body: pre_transition_removal
  where check_weak = check_rank_weak
    and check_strict = check_rank_strict
    and TD = TD
    and Pi = Pi
    and type_fixer="TYPE(_)".

definition processor where
  "processor \<equiv> check_allm (\<lambda>l.
    check (rank_exp l :\<^sub>f dom_type)
      (showsl_lit (STR ''Ill-typed rank\<newline>'') o showsl (rank_exp l) o showsl_lit (STR ''\<newline>on location '') o showsl l)
   ) (nodes_lts_impl Pi) \<then> body.processor"

end

term processor

end



locale transition_removal_wf =
  wf_order less_eq less +
  pre_transition_removal_wf where type_fixer = type_fixer +
  order_checker
    where type_fixer = "TYPE(_)"
      and less_eq_formula = less_eq_formula
      and less_formula = less_formula
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's :: {default,showl}) itself"
begin

interpretation ord_syntax less_eq less.

context
  fixes rank_exp :: "'l :: showl sharp \<Rightarrow> ('f,'v,'t) exp"
    and hinter :: "'tr :: showl \<Rightarrow> 's"
    and Pi :: "('f,'v,'t,'l sharp,'tr :: showl) lts_impl"
    and TD :: "'tr list"
  assumes rank_type: "\<And>l. l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> rank_exp l :\<^sub>f dom_type"
begin

definition rank where [simp]: "rank s \<equiv> \<lbrakk>rank_exp (state.location s)\<rbrakk> (state.valuation s)"

lemma formula_less_eq:
  "\<And>l r. l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> r \<in> set (nodes_lts_impl Pi) \<Longrightarrow>
   formula (rename_vars f (rank_exp l) \<sqsubseteq>\<^sub>f rename_vars g (rank_exp r))"
  using less_eq_type by (auto simp:rank_type)

lemma formula_less:
  "\<And>l r. l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> r \<in> set (nodes_lts_impl Pi) \<Longrightarrow>
   formula (rename_vars f (rank_exp l) \<sqsubset>\<^sub>f rename_vars g (rank_exp r))"
  using less_type by (auto simp:rank_type)

abbreviation weak where "weak \<equiv> check_rank_weak rank_exp hinter Pi"
abbreviation strict where "strict \<equiv> check_rank_strict rank_exp hinter Pi"
interpretation body: transition_removal
  where less_eq = less_eq
    and less = less
    and check_weak = weak
    and check_strict = strict
    and rank = rank
    and type_fixer = "TYPE(_)"
proof
  assume ltsi: "lts_impl Pi"
  note [intro] = lts_impl_formula_assertion_of[OF ltsi]
  let ?I = "assertion_of Pi"
  let ?preI = "\<lambda>l. rename_vars Pre (?I l)"
  let ?postI = "\<lambda>l. rename_vars Post (?I l)"
  let ?preR = "\<lambda>l. rename_vars Pre (rank_exp l)"
  let ?postR = "\<lambda>l. rename_vars Post (rank_exp l)"
  fix s t \<tau> tr
  assume \<tau>: "(tr, \<tau>) \<in> set (transitions_impl Pi)"
     and s: "s \<in> reachable_states (lts_of Pi)"
     and t: "t \<in> reachable_states (lts_of Pi)" 
     and st: "(s, t) \<in> transition_step_lts (lts_of Pi) \<tau>"
  define \<alpha> \<beta> where "\<alpha> \<equiv> state.valuation s" "\<beta> \<equiv> state.valuation t"
  with st have [simp]: "s = State \<alpha> (source \<tau>)" "t = State \<beta> (target \<tau>)"
   by (subst state.collapse[symmetric], unfold state.inject, auto)
  from st \<tau> have l: "source \<tau> \<in> set (nodes_lts_impl Pi)" and r: "target \<tau> \<in> set (nodes_lts_impl Pi)"
    by (auto simp: nodes_lts_def)
  from st have \<alpha>: "assignment \<alpha>" and \<beta>: "assignment \<beta>" by auto
  from reachable_state[OF s] have sat: "\<alpha> \<Turnstile> ?I (state.location s)" by auto
  from reachable_state[OF t] have sat2: "\<beta> \<Turnstile> ?I (state.location t)" by auto
  { assume ok: "isOK (weak (tr, \<tau>))"
    show "rank s \<sqsupseteq> rank t"
    proof(cases \<tau>)
      case [simp]: (Transition l r \<psi>)
      have imp: "\<Turnstile>\<^sub>f Disjunction [?postR r \<sqsubseteq>\<^sub>f ?preR l, \<not>\<^sub>f ?preI l, \<not>\<^sub>f \<psi> \<comment> \<open>, \<not> ?postI r\<close>]"
        apply (rule check_valid_formula[OF ok[simplified]])
        by (insert \<tau> ltsi l r, auto intro!: formula_less_eq elim: lts_implE)
      from st obtain \<gamma>
      where ass: "assignment (pre_post_inter \<alpha> \<beta> \<gamma>)" and sat3: "pre_post_inter \<alpha> \<beta> \<gamma> \<Turnstile> \<psi>" by auto
      show ?thesis
        apply (unfold rank_def, fold \<alpha>_\<beta>_def)
        apply (rule iffD1[OF less_eq_encode[OF ass, of "?postR _" "?preR _", simplified]])
        using sat sat2 sat3 validD[OF imp ass] ass rank_type l r
        apply (auto simp: map_form_not[symmetric])
        done
    qed
  }
  { assume ok: "isOK (strict (tr,\<tau>))"
    show "rank s \<sqsupset> rank t"
    proof(cases \<tau>)
      case [simp]: (Transition l r \<psi>)
      have imp: "\<Turnstile>\<^sub>f Disjunction [?postR r \<sqsubset>\<^sub>f ?preR l, \<not>\<^sub>f ?preI l, \<not>\<^sub>f \<psi> \<comment> \<open>, \<not> ?postI r \<close>]"
        by (rule check_valid_formula, rule ok[simplified], insert \<tau> ltsi l r, auto intro: formula_less elim: lts_implE)
      from st obtain \<gamma>
      where ass: "assignment (pre_post_inter \<alpha> \<beta> \<gamma>)" and sat3: "pre_post_inter \<alpha> \<beta> \<gamma> \<Turnstile> \<psi>" by auto
      from sat sat2 sat3 validD[OF imp ass] ass rank_type l r
      show "rank s \<sqsupset> rank t" by (simp add: less_encode)
    qed
  }
qed

lemmas body_sound = body.sound

end

lemma sound:
  assumes "processor rank_exp dom_type h TD Pi = return Pi'"
  shows "cooperation_SN_impl Pi' \<Longrightarrow> cooperation_SN_impl Pi"
  by (rule body_sound, insert assms, auto simp: processor_def)

end


subsection \<open>Transition removal with bounds\<close>

locale pre_transition_removal_bounded =
  pre_lts_checker where type_fixer = "TYPE('f\<times>'v trans_var\<times>'t\<times>'d\<times>'s)"
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's::{default,showl}) itself"
  and dom_type :: 't
  and less_eq_formula :: "('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp formula" (infix "\<sqsubseteq>\<^sub>f" 50)
  and less_formula :: "('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp \<Rightarrow> ('f,'v trans_var,'t) exp formula" (infix "\<sqsubset>\<^sub>f" 50)
  and is_constant :: "('f,'v trans_var,'t) exp \<Rightarrow> bool"
begin

abbreviation "less_bounded_formula info s t \<equiv> s \<sqsubset>\<^sub>f t \<and>\<^sub>f (rename_vars Pre (bound_exp info)) \<sqsubseteq>\<^sub>f t"

context
  fixes info :: "(('f,'v,'t) exp, 't, 'l :: showl, 'tr :: showl, 's) transition_removal_info"
begin

interpretation body: pre_transition_removal_wf
  where type_fixer = "TYPE(_)"
    and less_eq_formula = less_eq_formula and less_formula = "less_bounded_formula info".

definition processor where "processor Pi \<equiv> do {
  check (bound_exp info :\<^sub>f dom_type) (showsl_lit (STR ''Ill-typed bound: '') o showsl (bound_exp info) );
  check (is_constant (rename_vars Pre (bound_exp info))) (showsl_lit (STR ''Non-constant bound: '') o showsl (bound_exp info));
  body.processor (rank info) dom_type (hinter info) (removed info) Pi
}"

end

end


locale transition_removal_bounded =
  pre_transition_removal_bounded where type_fixer = type_fixer +
  order_checker where type_fixer = "TYPE(_)" +
  non_inf_quasi_order less_eq less
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's::{default,showl}) itself" +
  assumes is_constant: "\<And>e \<alpha> \<beta>. is_constant e \<Longrightarrow> \<lbrakk>e\<rbrakk> \<alpha> = \<lbrakk>e\<rbrakk> \<beta>"
begin

interpretation ord_syntax less_eq less.

context
  fixes info :: "(('f,'v,'t) exp, 't, 'l :: showl, 'tr :: showl, 's) transition_removal_info"
    and bound :: 'd
  assumes bound_type[simp]: "bound_exp info :\<^sub>f dom_type"
      and bound[simp]: "\<And>\<alpha>. \<lbrakk>rename_vars Pre (bound_exp info)\<rbrakk> \<alpha> = bound"
begin

interpretation wf: wf_order less_eq "less_bounded bound" by (fact bounded)

interpretation body: transition_removal_wf
  where type_fixer = "TYPE(_)"
    and less = "less_bounded bound"
    and less_formula = "less_bounded_formula info"
  by (unfold_locales, auto simp: less_encode less_eq_encode intro!: less_eq_type less_type)

lemmas body_sound = body.sound

end

lemma sound:
  assumes ok: "processor info Pi = return Pi'" and SN: "cooperation_SN_impl Pi'"
  shows "cooperation_SN_impl Pi"
proof-
  let ?b = "rename_vars Pre (bound_exp info)"
  note ok = ok[unfolded processor_def, simplified]
  from ok is_constant obtain bound where "\<And>\<alpha>. \<lbrakk>?b\<rbrakk>\<alpha> = bound" by auto
  from body_sound[OF _ this _ SN] ok show ?thesis by auto
qed

end


subsection \<open>Lexicographic ranking\<close>

context ord begin

definition lex_leq_bounded where
  "lex_leq_bounded bs xs ys \<equiv> ord_list.less_eq (map (\<lambda>b. (less_eq, less_bounded b)) bs) xs ys"

definition lex_less_bounded where
  "lex_less_bounded bs xs ys \<equiv> ord_list.less (map (\<lambda>b. (less_eq, less_bounded b)) bs) xs ys"

end

context ord_syntax begin

abbreviation lex_leq_bounded where "lex_leq_bounded \<equiv> ord.lex_leq_bounded less_eq less"
abbreviation lex_less_bounded where "lex_less_bounded \<equiv> ord.lex_less_bounded less_eq less"

end

context quasi_order begin

interpretation bounded_list: quasi_order_list "map (\<lambda>b. (less_eq, less_bounded b)) bs"
  by (unfold quasi_order_list_def, auto intro: bounded)

lemma lex_bounded: "class.quasi_order (lex_leq_bounded bs) (lex_less_bounded bs)"
  by (unfold lex_leq_bounded_def lex_less_bounded_def, unfold_locales)

end

context non_inf_quasi_order begin

interpretation bounded_list: wf_order_list "map (\<lambda>b. (less_eq, less_bounded b)) bs"
  by (unfold wf_order_list_def, auto intro: bounded)


lemma lex_bounded: "class.wf_order (lex_leq_bounded bs) (lex_less_bounded bs)"
  by (unfold lex_leq_bounded_def lex_less_bounded_def, unfold_locales)

end

context prelogic begin

abbreviation eval_list where "eval_list \<alpha> ts \<equiv> map (\<lambda> t. \<lbrakk>t\<rbrakk> \<alpha>) ts"

abbreviation rename_vars_exp_list :: "_ \<Rightarrow> ('f,'v,'t) exp list \<Rightarrow> _"
  where "rename_vars_exp_list f es \<equiv> map (rename_vars f) es"

adhoc_overloading rename_vars \<rightleftharpoons> rename_vars_exp_list

end

context pre_transition_removal_bounded begin

abbreviation bound_exps where "bound_exps info \<equiv> map (rename_vars_exp Pre) (bound_exp info)"

fun lex_leq_formula where
  "lex_leq_formula [b] [x] [y] = (x \<sqsubseteq>\<^sub>f y)"
| "lex_leq_formula (b#b'#bs) (x#x'#xs) (y#y'#ys) =
   (x \<sqsubset>\<^sub>f y \<and>\<^sub>f b \<sqsubseteq>\<^sub>f y \<or>\<^sub>f Conjunction [x \<sqsubseteq>\<^sub>f y, lex_leq_formula (b'#bs) (x'#xs) (y'#ys)])"
| "lex_leq_formula [] [] [] = True\<^sub>f"
| "lex_leq_formula _ _ _ = False\<^sub>f"

lemma lex_leq_formula_code: 
  "lex_leq_formula xs ys zs = (case xs of 
     [] \<Rightarrow> (case ys of [] \<Rightarrow> (case zs of [] \<Rightarrow> True\<^sub>f | _ \<Rightarrow> False\<^sub>f) | _ \<Rightarrow> False\<^sub>f)
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False\<^sub>f 
  | y # ys \<Rightarrow> (case zs of [] \<Rightarrow> False\<^sub>f 
  | z # zs \<Rightarrow> (case xs 
    of [] \<Rightarrow> (case ys of [] \<Rightarrow> (case zs of [] \<Rightarrow> y \<sqsubseteq>\<^sub>f z | _ \<Rightarrow> False\<^sub>f) | _ \<Rightarrow> False\<^sub>f)
    | _ \<Rightarrow> (case ys of [] \<Rightarrow> False\<^sub>f | _ \<Rightarrow> (case zs of [] \<Rightarrow> False\<^sub>f 
    | _ \<Rightarrow> y \<sqsubset>\<^sub>f z \<and>\<^sub>f x \<sqsubseteq>\<^sub>f z \<or>\<^sub>f Conjunction [y \<sqsubseteq>\<^sub>f z, lex_leq_formula xs ys zs]))))))" 
  by (cases xs; cases ys; cases zs; cases "tl xs"; cases "tl ys"; cases "tl zs", auto)

fun lex_less_formula where
  "lex_less_formula [b] [x] [y] = (x \<sqsubset>\<^sub>f y \<and>\<^sub>f b \<sqsubseteq>\<^sub>f y)"
| "lex_less_formula (b#b'#bs) (x#x'#xs) (y#y'#ys) =
   (x \<sqsubset>\<^sub>f y \<and>\<^sub>f b \<sqsubseteq>\<^sub>f y \<or>\<^sub>f Conjunction [x \<sqsubseteq>\<^sub>f y, lex_less_formula (b'#bs) (x'#xs) (y'#ys)])"
| "lex_less_formula _ _ _ = False\<^sub>f"

lemma lex_less_formula_code: 
  "lex_less_formula xs ys zs = (case xs of 
     [] \<Rightarrow> False\<^sub>f
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False\<^sub>f 
  | y # ys \<Rightarrow> (case zs of [] \<Rightarrow> False\<^sub>f 
  | z # zs \<Rightarrow> (case xs 
    of [] \<Rightarrow> (case ys of [] \<Rightarrow> (case zs of [] \<Rightarrow> y \<sqsubset>\<^sub>f z \<and>\<^sub>f x \<sqsubseteq>\<^sub>f z | _ \<Rightarrow> False\<^sub>f) | _ \<Rightarrow> False\<^sub>f)
    | _ \<Rightarrow> (case ys of [] \<Rightarrow> False\<^sub>f | _ \<Rightarrow> (case zs of [] \<Rightarrow> False\<^sub>f 
    | _ \<Rightarrow> y \<sqsubset>\<^sub>f z \<and>\<^sub>f x \<sqsubseteq>\<^sub>f z \<or>\<^sub>f Conjunction [y \<sqsubseteq>\<^sub>f z, lex_less_formula xs ys zs]))))))" 
  by (cases xs; cases ys; cases zs; cases "tl xs"; cases "tl ys"; cases "tl zs", auto)

context
  fixes info :: "(('f,'v,'t) exp list, 't, 'l :: showl, 'tr :: showl, 's) transition_removal_info"
    and Pi :: "('f,'v,'t,'l sharp,'tr) lts_impl"
begin

fun check_lex_weak where
  "check_lex_weak (tr, Transition l r \<phi>) = do {
      let \<psi> = lex_leq_formula (bound_exps info) (rename_vars Post (rank info r)) (rename_vars Pre (rank info l));
      check (formula \<psi>) (showsl_lit (STR ''lex-leq does not encode valid formula'') o showsl_nl o showsl \<psi>); 
      check_valid_formula (hinter info tr) (Disjunction [
        \<psi>,
        \<not>\<^sub>f rename_vars Pre (assertion_of Pi l),
        \<not>\<^sub>f \<phi>
 \<comment> \<open>disabled: \<not> rename_vars Post (assertion_of Pi r) \<close>
    ])}"

fun check_lex_strict where
  "check_lex_strict (tr, Transition l r \<phi>) = do {
      let \<psi> = lex_less_formula (bound_exps info) (rename_vars Post (rank info r)) (rename_vars Pre (rank info l));
      check (formula \<psi>) (showsl_lit (STR ''lex-less does not encode valid formula'') o showsl_nl o showsl \<psi>);
      check_valid_formula (hinter info tr) (Disjunction [
         \<psi>,
         \<not>\<^sub>f rename_vars Pre (assertion_of Pi l),
         \<not>\<^sub>f \<phi>
 \<comment> \<open>disabled: \<not> rename_vars Post (assertion_of Pi r) \<close>
    ])}"


interpretation lex_body: pre_transition_removal
  where type_fixer = "TYPE(_)"
    and check_weak = check_lex_weak
    and check_strict = check_lex_strict
    and TD = "removed info" and Pi = Pi.

definition lex_processor where "lex_processor \<equiv>
  do {
    check_allm (\<lambda>l.
      check_allm (\<lambda>e.
        check (e :\<^sub>f dom_type) (showsl_lit (STR ''Unexpected type of expression:\<newline>'') o showsl e)
      ) (rank info l)
    ) (nodes_lts_impl Pi);
    check_allm (\<lambda>e.
      check (e :\<^sub>f dom_type) (showsl_lit (STR ''Unexpected type of bound: '') o showsl e)
    ) (bound_exp info);
    check_allm (\<lambda>e.
      check (is_constant e) (showsl_lit (STR ''Non-constant bound: '') o showsl e)
    ) (bound_exps info);
    lex_body.processor
  }"


end

end

context transition_removal_bounded begin

context
  fixes info :: "(('f,'v,'t) exp list, 't, 'l :: showl, 'tr :: showl, 's) transition_removal_info"
    and Pi :: "('f,'v,'t,'l sharp,'tr) lts_impl"
    and bounds :: "'d list"
  assumes ranks_type: "\<And>e l. l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> e \<in> set (rank info l) \<Longrightarrow> e :\<^sub>f dom_type"
      and bounds_type: "\<And>be. be \<in> set (bound_exp info) \<Longrightarrow> be :\<^sub>f dom_type"
      and bounds: "\<And> \<alpha>. eval_list \<alpha> (bound_exps info) = bounds"
begin

interpretation ord_syntax less_eq less.

abbreviation ranks where "ranks s \<equiv> eval_list (state.valuation s) (rank info (state.location s))"

lemma ranks_type_rename:
  "l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> e \<in> rename_vars f ` set (rank info l) \<Longrightarrow> e :\<^sub>f dom_type"
  using ranks_type by auto

lemma bound_exps_type:
  "be \<in> set (bound_exps info) \<Longrightarrow> be :\<^sub>f dom_type"
  using bounds_type by auto

lemma lex_leq_sound:
  defines "bes \<equiv> bound_exps info"
  assumes \<alpha>: "assignment \<alpha>"
      and x: "\<And>x. x \<in> set xs \<Longrightarrow> x :\<^sub>f dom_type"
      and y: "\<And>y. y \<in> set ys \<Longrightarrow> y :\<^sub>f dom_type"
  shows "\<alpha> \<Turnstile> lex_leq_formula bes xs ys \<Longrightarrow> lex_leq_bounded (eval_list \<alpha> bes) (eval_list \<alpha> xs) (eval_list \<alpha> ys)"
  using bound_exps_type[folded bes_def] x y
  apply (induct bes xs ys rule:lex_leq_formula.induct)
  using less_eq_encode[OF \<alpha>] less_encode[OF \<alpha>] by (auto simp:lex_leq_bounded_def lexcomp.less_eq_def)

lemma lex_less_sound:
  defines "bes \<equiv> bound_exps info"
  assumes \<alpha>: "assignment \<alpha>"
      and x: "\<And>x. x \<in> set xs \<Longrightarrow> x :\<^sub>f dom_type"
      and y: "\<And>y. y \<in> set ys \<Longrightarrow> y :\<^sub>f dom_type"
      and sat: "\<alpha> \<Turnstile> (lex_less_formula bes xs ys)"
  shows "lex_less_bounded (eval_list \<alpha> bes) (eval_list \<alpha> xs) (eval_list \<alpha> ys)"
  using bound_exps_type[folded bes_def] x y sat
  apply (induct bes xs ys rule: lex_less_formula.induct)
  using less_eq_encode[OF \<alpha>] less_encode[OF \<alpha>] 
  by (auto simp: lex_less_bounded_def lexcomp.less_def)

abbreviation "weak \<equiv> check_lex_weak info Pi"
abbreviation strict where "strict \<equiv> check_lex_strict info Pi"

interpretation lex_wf: wf_order "lex_leq_bounded bounds" "lex_less_bounded bounds" by (fact lex_bounded)

interpretation lex_body: transition_removal
  where type_fixer = "TYPE(_)"
    and less_eq = "lex_leq_bounded bounds"
    and less = "lex_less_bounded bounds"
    and check_weak = weak
    and check_strict = strict
    and TD = "removed info"
    and rank = ranks
proof unfold_locales
  assume Pi: "lts_impl Pi"
  note [intro] = lts_impl_formula_assertion_of[OF Pi]
  let ?I = "assertion_of Pi"
  let ?preI = "\<lambda>l. rename_vars Pre (?I l)"
  let ?postI = "\<lambda>l. rename_vars Post (?I l)"
  let ?preR = "\<lambda>l. rename_vars Pre (rank info l)"
  let ?postR = "\<lambda>l. rename_vars Post (rank info l)"
  let ?bnd = "bound_exps info" 
  fix s t \<tau> tr
  assume \<tau>: "(tr, \<tau>) \<in> set (transitions_impl Pi)"
     and s: "s \<in> reachable_states (lts_of Pi)"
     and t: "t \<in> reachable_states (lts_of Pi)" 
     and st: "(s, t) \<in> transition_step_lts (lts_of Pi) \<tau>"
  define \<alpha> \<beta> where "\<alpha> \<equiv> state.valuation s" "\<beta> \<equiv> state.valuation t"
  with st have [simp]: "s = State \<alpha> (source \<tau>)" "t = State \<beta> (target \<tau>)"
   by (subst state.collapse[symmetric], unfold state.inject, auto)
  from st \<tau> have l: "source \<tau> \<in> set (nodes_lts_impl Pi)" and r: "target \<tau> \<in> set (nodes_lts_impl Pi)"
    by (auto simp: nodes_lts_def)
  from st have \<alpha>: "assignment \<alpha>" and \<beta>: "assignment \<beta>" by auto
  from reachable_state[OF s] have sat: "\<alpha> \<Turnstile> ?I (state.location s)" by auto
  from reachable_state[OF t] have sat2: "\<beta> \<Turnstile> ?I (state.location t)" by auto

  { assume ok: "isOK (weak (tr, \<tau>))"
    show "lex_leq_bounded bounds (ranks t) (ranks s)"
    proof(cases \<tau>)
      case *[simp]: (Transition l r \<phi>)
      from st obtain \<gamma> where \<gamma>: "assignment \<gamma>" and "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> \<phi>" by auto
      with sat sat2 have sat3: "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> ?preI l \<and>\<^sub>f ?postI r \<and>\<^sub>f \<phi>" by auto
      from lts_impl_transitions_impl[OF Pi \<tau>] lts_impl_formula_assertion_of[OF Pi] ok[simplified] \<alpha> \<beta> \<gamma>
      have "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> Disjunction [lex_leq_formula ?bnd (?postR r) (?preR l), \<not>\<^sub>f ?preI l, \<not>\<^sub>f \<phi> \<comment> \<open>, \<not> ?postI r\<close>]"
        by (intro validD check_valid_formula, auto)
      with sat3 have "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> lex_leq_formula ?bnd (?postR r) (?preR l)"
        by auto
      from lex_leq_sound[OF _ _ _ this, unfolded bounds] \<alpha> \<beta> \<gamma> l r
      show ?thesis by (auto simp: o_def ranks_type_rename)
    qed
  }
  { assume ok: "isOK (strict (tr, \<tau>))"
    show "lex_less_bounded bounds (ranks t) (ranks s)"
    proof(cases \<tau>)
      case *[simp]: (Transition l r \<phi>)
      from st obtain \<gamma> where \<gamma>: "assignment \<gamma>" and "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> \<phi>" by auto
      with sat sat2 have sat3: "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> ?preI l \<and>\<^sub>f ?postI r \<and>\<^sub>f \<phi>" by auto
      from lts_impl_transitions_impl[OF Pi \<tau>] lts_impl_formula_assertion_of[OF Pi] ok[simplified] \<alpha> \<beta> \<gamma>
      have "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> Disjunction [lex_less_formula ?bnd (?postR r) (?preR l), \<not>\<^sub>f ?preI l, \<not>\<^sub>f \<phi> \<comment> \<open>, \<not> ?postI r\<close>]"
        by (intro validD check_valid_formula, auto)
      with sat3
      have "\<delta> \<alpha> \<beta> \<gamma> \<Turnstile> lex_less_formula ?bnd (?postR r) (?preR l)" by auto
      from lex_less_sound[OF _ _ _ this, unfolded bounds] \<alpha> \<beta> \<gamma> l r
      show ?thesis by (auto simp: o_def ranks_type_rename)
    qed
  }
qed

lemmas lex_body_sound = lex_body.sound

end

lemma lex_sound:
  assumes ok: "lex_processor info Pi = return Pi'"
      and "cooperation_SN_impl Pi'" (is ?SN)
  shows "cooperation_SN_impl Pi"
proof (rule lex_body_sound)
  note * = ok[unfolded lex_processor_def, simplified]
  show "l \<in> set (nodes_lts_impl Pi) \<Longrightarrow> e \<in> set (rank info l) \<Longrightarrow> e :\<^sub>f dom_type" for l e
     using * by auto
  show "pre_transition_removal.processor
    (weak info Pi) (local.strict info Pi) (removed info) Pi = return Pi'" using * by auto
  show ?SN using \<open>?SN\<close>.
  show "be \<in> set (bound_exp info) \<Longrightarrow> be :\<^sub>f dom_type" for be using * by auto
  show "\<And>\<alpha>. eval_list \<alpha> (bound_exps info) = eval_list undefined (bound_exps info)"
  proof (unfold list_eq_iff_nth_eq length_map, safe)
    fix \<alpha> i assume i: "i < length (bound_exp info)"
    with * have "is_constant (bound_exps info ! i)" by auto
    from is_constant[OF this] i
    show "eval_list \<alpha> (bound_exps info) ! i = eval_list undefined (bound_exps info) ! i" by auto
  qed
qed

end

lemmas transition_removal_code[code] =
  pre_transition_removal_wf.check_rank_strict.simps
  pre_transition_removal_wf.check_rank_weak.simps
  pre_transition_removal_wf.processor_def
  pre_transition_removal_bounded.processor_def
  pre_transition_removal_bounded.lex_processor_def
  pre_transition_removal_bounded.check_lex_strict.simps
  pre_transition_removal_bounded.check_lex_weak.simps
  pre_transition_removal_bounded.lex_less_formula_code
  pre_transition_removal_bounded.lex_leq_formula_code

end
