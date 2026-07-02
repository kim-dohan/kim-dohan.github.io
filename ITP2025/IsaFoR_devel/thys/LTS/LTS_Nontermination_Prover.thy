theory LTS_Nontermination_Prover
  imports 
    Initial_Cooperation_Program 
    Invariant_Proof_Checkers 
    Transition_Removal 
    Show_LTS
    Location_Addition 
    Fresh_Variable_Addition 
    Call_Graph_Scc_Decomp
    Invariants_To_Assertions
    Cut_Transition_Split
begin
type_synonym ('f, 'v, 't) val_impl = "(('v \<times> 't) \<times> ('f, 'v, 't) exp) list"
type_synonym ('f, 'v, 't, 'l) state_impl = "('f, 'v, 't) val_impl \<times> 'l"
type_synonym ('f,'v,'t,'l,'tr) transition_seq_impl =
  "(('tr \<times> ('f,'v,'t,'l) transition_rule) \<times> ('f, 'v, 't, 'l) state_impl) list"

datatype ('f,'v,'t,'l,'tr,'h) nontermination_proof =
  EquivalentState "('f, 'v, 't, 'l) state_impl" "('f,'v,'t,'l,'tr) transition_seq_impl" "('f,'v,'t,'l,'tr) transition_seq_impl"


definition val_of :: "('f, 'v, 't) val_impl \<Rightarrow> ('v,'t,('f, 'v, 't) exp) valuation"
  where
    "val_of ss = List.foldr (\<lambda>(x, t) \<sigma>. \<sigma> \<circ>\<^sub>s subst x t) ss Var"

definition state_of :: "('f, 'v, 't, 'l) state_impl \<Rightarrow> ('v, 't, ('f, 'v \<times> 't) Term.term, 'l) state" where
  "state_of s \<equiv> (State (val_of (fst s)) (snd s))"

locale pre_nontermination_checker =
  pre_art_checker where type_fixer = type_fixer +
  transition_removal: pre_transition_removal_bounded
    where type_fixer = "TYPE(_)"
      and logic_checker = tc2
      and showsl_atom = sa2
      and normalize_lit = ne2 
      and normalized_lit = ned2 + 
  pre_transition_definability_checker
    where type_fixer = "TYPE(_)"
  for type_fixer :: "('f:: showl \<times> 'v::showl \<times> 't:: showl \<times> ('f, 'v, 't) exp \<times> 'h::{default,showl}) itself" +
    fixes hinter :: "'tr :: showl \<Rightarrow> 'h"

locale nontermination_checker =
  pre_nontermination_checker where type_fixer = type_fixer +
  art_checker where type_fixer = type_fixer +
  transition_removal: transition_removal_bounded
    where type_fixer = "TYPE(_)"
      and logic_checker = tc2
      and showsl_atom = sa2
      and normalize_lit = ne2 
      and normalized_lit = ned2 + 
  transition_definability_checker
    where type_fixer = "TYPE(_)"
  for type_fixer :: "('f:: showl \<times> 'v::showl \<times> 't:: showl \<times> ('f, 'v, 't) exp \<times> 'h::{default,showl}) itself"

context pre_nontermination_checker
begin

definition check_equal_states :: "('f, 'v, 't, 'l) state_impl \<Rightarrow> ('f, 'v, 't, 'l) state_impl \<Rightarrow> (String.literal \<Rightarrow> String.literal) + unit"
  where
  "check_equal_states s\<^sub>1 s\<^sub>2 =
  do {
     check (snd s\<^sub>1 = snd s\<^sub>2) (showsl_lit (STR ''different locations\<newline>''));
     check (fst s\<^sub>1 = fst s\<^sub>2) (showsl_lit (STR ''different valuations\<newline>''))
  }"

lemma check_equal_states:
  assumes "isOK(check_equal_states (v\<^sub>1,l\<^sub>1) (v\<^sub>2,l\<^sub>2))"
  shows "l\<^sub>1 = l\<^sub>2 \<and> (\<forall>x. val_of v\<^sub>1 x = val_of v\<^sub>2 x)"
proof -
  note ok = assms[unfolded check_equal_states_def]
  from ok have "l\<^sub>1 = l\<^sub>2" "v\<^sub>1 = v\<^sub>2" by simp+
  thus ?thesis by auto
qed

definition check_transition_step :: " _ \<Rightarrow> _ \<Rightarrow> _"
  where
  "check_transition_step P \<tau> = (
     case \<tau> of (src, (lab, t), tgt) \<Rightarrow>
     case t of Transition l r \<phi> \<Rightarrow>
       let \<alpha> = \<delta> (val_of (fst src)) (val_of (fst tgt)) (val_of (fst src)) in
       do {
         check ((lab, t) \<in> set (transitions_impl P)) (showsl_lit (STR ''transition not available\<newline>''));
         check (state_lts (lts_of P) (state_of tgt)) (showsl_lit (STR ''target is not a state\<newline>''));
         check (\<alpha> \<Turnstile> \<phi>) (showsl_lit (STR ''condition not satisfied\<newline>''));
         check (snd src = l \<and> snd tgt = r)
           (showsl_lit (STR ''rule not applicable\<newline>''))})"

lemma check_transition_step:
  assumes "isOK(check_transition_step P (src, (lab, Transition l r \<phi>), tgt))"
  and src:"state_lts (lts_of P) (state_of src)"
  shows "(state_of src, state_of tgt) \<in> transition (lts_of P) \<and> state_lts (lts_of P) (state_of tgt)"
proof -
  note ok = assms[unfolded check_transition_step_def split]
  let ?\<tau> = "Transition l r \<phi>"
  from ok have "(lab, ?\<tau>) \<in> set (transitions_impl P)" by auto
  hence trans:"Transition l r \<phi> \<in> transition_rules (lts_of P)"
    unfolding lts_of_def transitions_impl_def by (cases P, auto)
  let ?\<alpha> = "\<delta> (val_of (fst src)) (val_of (fst tgt)) (val_of (fst src))"
  from ok have sat:"?\<alpha> \<Turnstile> \<phi>" and ass:"assignment (val_of (fst src))" unfolding state_of_def by simp+
  from ok have tgt:"state_lts (lts_of P) (state_of tgt)" by auto
  from ok have locs:"snd src = l \<and> snd tgt = r" by simp
  note mem = mem_transition_step_TransitionI[OF src tgt _ _ ass]
  have "(state_of src, state_of tgt) \<in> transition_step (state_lts (lts_of P)) ?\<tau>"
    by (rule mem, insert sat locs, unfold state_of_def, auto)
  from mem_transitionI[OF _ this] trans show ?thesis by auto
qed


fun check_transition_seq
  where
   "check_transition_seq P src [] = return src"
 | "check_transition_seq P src ((\<tau>, tgt) # ts) =
             (check_transition_seq P tgt ts \<bind>
             (\<lambda> last. check_return (check_transition_step P (src, \<tau>, tgt)) last))"

lemma check_transition_seq:
  assumes "(check_transition_seq P src ts) = return tgt"
  and src:"state_lts (lts_of P) (state_of src)"
  shows "(state_of src, state_of tgt) \<in> (transition (lts_of P))^^(length ts) \<and> state_lts (lts_of P) (state_of tgt)"
  using assms
proof(induct ts arbitrary:src)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  let ?T = "transition (lts_of P)"
  obtain \<tau> intermed where t:"t = (\<tau>, intermed)" by (cases t, auto)
  obtain lab l r \<phi> where \<tau>:"\<tau> = (lab, Transition l r \<phi>)" by (cases \<tau>, cases "snd \<tau>", auto)
  note ok = Cons(2)[unfolded check_transition_seq.simps foldl.foldl_Cons t split]
  from ok have step:"isOK(check_transition_step P (src, \<tau>, intermed))" by auto
  note step = step[unfolded \<tau>, THEN check_transition_step, OF Cons(3)]
  from ok have "check_transition_seq P intermed ts = return tgt" by auto
  from Cons(1)[OF this] step have steps:"(state_of intermed, state_of tgt) \<in> ?T^^(length ts)"
    "state_lts (lts_of P) (state_of tgt)" by auto
  from relpow_Suc_I2[OF conjunct1[OF step] steps(1)] steps(2) show ?case by simp
qed

fun check_nontermination_proof :: "showsl \<Rightarrow> ('f,'v,'t,'l,'tr) lts_impl \<Rightarrow> ('f,'v,'t,'l,'tr,'h) nontermination_proof \<Rightarrow>  _" where
  "check_nontermination_proof i P (nontermination_proof.EquivalentState s\<^sub>i\<^sub>n\<^sub>i\<^sub>t stem loop) = debug i (STR ''Equivalent state criterion'') (
    do {
    check (snd s\<^sub>i\<^sub>n\<^sub>i\<^sub>t \<in> set (initial P) \<and> state_lts (lts_of P) (state_of s\<^sub>i\<^sub>n\<^sub>i\<^sub>t)) (showsl_lit (STR ''initial state''));  
    loop_head\<^sub>1 \<leftarrow> check_transition_seq P s\<^sub>i\<^sub>n\<^sub>i\<^sub>t stem
      <+? (\<lambda> s. i o showsl_lit (STR '': error when checking stem sequence of lasso\<newline>'') o s);
    loop_head\<^sub>2 \<leftarrow> check_transition_seq P loop_head\<^sub>1 loop
      <+? (\<lambda> s. i o showsl_lit (STR '': error when checking loop sequence\<newline>'') o s);
    check (length loop \<noteq> 0) (showsl_lit (STR ''loop must have positive length''));
    check (loop_head\<^sub>1 = loop_head\<^sub>2) (showsl_lit (STR ''loop start and end do not match''))
   })"

lemma check_nontermination_proof:
  "lts_impl P \<Longrightarrow> isOK(check_nontermination_proof i P ntprf) \<Longrightarrow> \<not> lts_termination (lts_of P)" 
proof-
  assume P:"lts_impl P" and ok:"isOK(check_nontermination_proof i P ntprf)"
  let ?lts = "lts_of P"
  let ?T = "transition ?lts"
  let ?state = "\<lambda>s. state_lts (lts_of P) (state_of s)"
  show ?thesis proof(cases ntprf)
    case (EquivalentState s\<^sub>0 stem loop)
    note ok = ok[unfolded this check_nontermination_proof.simps]
    let ?k = "length loop"
    from ok have s0:"state_lts ?lts (state_of s\<^sub>0)" by auto
    from ok obtain s\<^sub>i where lh:"check_transition_seq P s\<^sub>0 stem = return s\<^sub>i" by auto
    from check_transition_seq[OF lh s0] relpow_imp_rtrancl
      have si:"(state_of s\<^sub>0, state_of s\<^sub>i) \<in> ?T\<^sup>*" "?state s\<^sub>i" by auto
    from ok lh have "check_transition_seq P s\<^sub>i loop = Inr s\<^sub>i" by auto
    from check_transition_seq[OF this si(2)] have loop:"(state_of s\<^sub>i, state_of s\<^sub>i) \<in> ?T^^?k" by auto
    from ok have k:"?k > 0" by auto
    from k loop trancl_power have loop:"(state_of s\<^sub>i, state_of s\<^sub>i) \<in> ?T\<^sup>+" by blast
    from ok have s0:"state_of s\<^sub>0 \<in> (initial_states ?lts)"
      unfolding initial_states_def state_of_def by auto
    show ?thesis proof(cases "state_of s\<^sub>0 = state_of s\<^sub>i")
      case True
      let ?f = "\<lambda>i. state_of s\<^sub>i"
      from loop have "chain (?T\<^sup>+) ?f" unfolding chain_def by auto
      with True s0 have "\<not> SN_on (?T\<^sup>+) (initial_states ?lts)" unfolding SN_on_def by auto
      then show ?thesis using SN_on_trancl by auto
    next
      case False
      with si(1)[unfolded rtrancl_eq_or_trancl] have stem:"(state_of s\<^sub>0, state_of s\<^sub>i) \<in> ?T\<^sup>+" by auto
      let ?f = "\<lambda>i. (case i of 0 \<Rightarrow> state_of s\<^sub>0 | Suc j \<Rightarrow> state_of s\<^sub>i)"
      { fix i
        have "(?f i, ?f (Suc i)) \<in> (transition (lts_of P))\<^sup>+" by (cases i, insert stem loop, auto)
      } note f = this
      have "\<exists>f. f 0 \<in> initial_states (lts_of P) \<and> chain (?T\<^sup>+) f"
        unfolding chain_def by (rule exI[of _ ?f], insert f s0 , auto)
      hence "\<not> SN_on (?T\<^sup>+) (initial_states ?lts)" unfolding SN_on_def by auto
      then show ?thesis using SN_on_trancl by auto
    qed
  qed
qed

definition check where
  "check P prf \<equiv> do {
     debug id (STR ''init - Check well-formedness'') (check_lts_impl P <+? (\<lambda> s. showsl_lit (STR ''input LTS is not well-formed'') o s));
     check_nontermination_proof id P prf
   }"

end

declare pre_nontermination_checker.check_transition_seq.simps[code]
declare pre_nontermination_checker.check_nontermination_proof.simps[code]
declare pre_nontermination_checker.check_def[code]


context nontermination_checker
begin

theorem sound: "isOK (check P prf) \<Longrightarrow> \<not> lts_termination (lts_of P)"
  using check_nontermination_proof[of P _ "prf"]
  unfolding check_def by auto

end
end
