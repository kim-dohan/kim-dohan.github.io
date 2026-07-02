theory LTS
imports 
  "Abstract-Rewriting.Abstract_Rewriting"
  Show.Show_Instances
  Deriving.Compare_Generator
  Ord.Formula
  Ord.Non_Inf_Order
  Auxx.Map_Of
begin

datatype 'v trans_var = Pre 'v | Post 'v | Intermediate 'v

instantiation trans_var :: (showl) showl
begin
fun showsl_trans_var where 
  "showsl_trans_var (Pre v) = showsl v" 
| "showsl_trans_var (Post v) = showsl v o showsl_lit (STR 0x27)" \<comment> \<open>single quote\<close>
| "showsl_trans_var (Intermediate v) = showsl v o showsl_lit (STR ''#'')"
definition "showsl_list (xs :: 'a trans_var list) = default_showsl_list showsl xs"
instance ..
end 

derive compare_order trans_var

fun untrans_var where
  "untrans_var (Pre x) = x"
| "untrans_var (Post x) = x"
| "untrans_var (Intermediate x) = x"

type_synonym ('f,'v,'t) transition_formula = "('f,'v trans_var,'t) exp formula"

datatype ('f,'v,'t,'l) transition_rule =
  Transition 'l 'l "('f,'v trans_var,'t) exp formula"

fun source where
  "source (Transition l _ _) = l"

fun target where
  "target (Transition _ r _) = r"

fun transition_formula where
  "transition_formula (Transition _ _ \<phi>) = \<phi>"


datatype ('v,'t,'d,'l) state = State (valuation: "('v,'t,'d) valuation") (location: 'l)

fun relabel_state where "relabel_state f (State \<alpha> l) = State \<alpha> (f l)"

lemma valuation_relabel_state[simp]: "valuation (relabel_state f s) = valuation s"
  and location_relabel_state[simp]: "location (relabel_state f s) = f (location s)"
  by (atomize(full), cases s, auto)

record ('f,'v,'t,'l) lts =
  initial :: "'l set" 
  transition_rules :: "('f,'v,'t,'l) transition_rule set"
  assertion :: "'l \<Rightarrow> ('f,'v,'t) exp formula" 

definition nodes_lts :: "('f,'v,'t,'l) lts \<Rightarrow> 'l set" where
  "nodes_lts P = source ` transition_rules P \<union> target ` transition_rules P"

definition sub_lts :: "('f,'v,'t,'l) lts \<Rightarrow> ('f,'v,'t,'l) lts \<Rightarrow> bool" where
  "sub_lts P Q \<equiv> initial P \<subseteq> initial Q \<and> transition_rules P \<subseteq> transition_rules Q \<and> assertion P = assertion Q"

lemma sub_ltsI[intro!]:
  assumes "initial P \<subseteq> initial Q"
      and "transition_rules P \<subseteq> transition_rules Q"
      and "assertion P = assertion Q"
  shows "sub_lts P Q" by (insert assms, auto simp: sub_lts_def)

lemma sub_ltsD:
  assumes "sub_lts P Q"
  shows "initial P \<subseteq> initial Q"
    and "transition_rules P \<subseteq> transition_rules Q"
    and "assertion P = assertion Q" 
  using assms unfolding sub_lts_def by auto

lemma sub_ltsE[elim!]:
  assumes "sub_lts P Q"
      and "initial P \<subseteq> initial Q \<Longrightarrow> transition_rules P \<subseteq> transition_rules Q \<Longrightarrow>
           assertion P = assertion Q \<Longrightarrow> thesis"
  shows thesis using assms unfolding sub_lts_def by auto

lemma sub_lts_trans[trans]: "sub_lts P Q \<Longrightarrow> sub_lts Q R \<Longrightarrow> sub_lts P R" by auto

definition call_graph_of_lts :: "('f,'v,'t,'l) lts \<Rightarrow> 'l rel" where
  "call_graph_of_lts P = { (source \<tau>, target \<tau>) | \<tau>. \<tau> \<in> transition_rules P}" 

definition delete_transitions :: "('f,'v,'t,'l) lts \<Rightarrow> ('f,'v,'t,'l) transition_rule set \<Rightarrow> ('f,'v,'t,'l) lts" where
  "delete_transitions lts ts = \<lparr>lts.initial = lts.initial lts, transition_rules = transition_rules lts - ts, assertion = assertion lts\<rparr>"

lemma delete_transitions_simps[simp]:
  "lts.initial (delete_transitions P TD) = lts.initial P"
  "transition_rules (delete_transitions lts ts) = transition_rules lts - ts"
  "assertion (delete_transitions lts ts) = assertion lts"
  by (simp_all add: delete_transitions_def)

lemma delete_transistions_eq[simp]:
  "delete_transitions P (transition_rules P \<inter> TD) = delete_transitions P TD"
   unfolding sub_lts_def delete_transitions_def by auto

lemma delete_transitions_sublts: "sub_lts (delete_transitions lts ts) lts"
  unfolding sub_lts_def delete_transitions_def by auto

(* this locale could just be prelogic, but then it's impossible to import the new definitions made
   here to independently made interpretations of prelogic (Isabelle 2017) *)
locale lts = prelogic where type_fixer = type_fixer
  for type_fixer :: "('f\<times>'t\<times>'d) itself"
begin

fun transition_rule where 
  "transition_rule (Transition l r \<phi>) = formula \<phi>" 
    
lemma transition_ruleI:
  assumes "\<And>l r \<phi>. \<tau> = Transition l r \<phi> \<Longrightarrow> formula \<phi>"
  shows "transition_rule \<tau>"
  using assms by (cases \<tau>, auto)

lemma transition_ruleE[elim]:
  assumes "transition_rule \<tau>" "\<And>l r \<phi>. \<tau> = Transition l r \<phi> \<Longrightarrow> formula \<phi> \<Longrightarrow> thesis" 
  shows thesis using assms by (cases \<tau>, auto)
  

definition state :: "('v,'t,'d,'l) state \<Rightarrow> bool" where [simp]: "state s \<equiv> assignment (valuation s)"

definition lts :: "('f,'v,'t,'l) lts \<Rightarrow> bool" where
  "lts P \<equiv> (\<forall> \<tau> \<in> transition_rules P. transition_rule \<tau>) \<and> (\<forall> l. formula (assertion P l))"

lemma ltsI[intro]:
  assumes "\<And>\<tau>. \<tau> \<in> transition_rules P \<Longrightarrow> transition_rule \<tau>" and "\<And> l. formula (assertion P l)"
  shows "lts P" using assms by (auto simp: lts_def)

lemma ltsE[elim]:
  assumes "lts P"
      and "(\<And>\<tau>. \<tau> \<in> transition_rules P \<Longrightarrow> transition_rule \<tau>) \<Longrightarrow> (\<And> l. formula (assertion P l)) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: lts_def)

fun pre_post_inter where
  "pre_post_inter \<alpha> \<beta> \<gamma> (Pre x,t) = \<alpha> (x,t)"
| "pre_post_inter \<alpha> \<beta> \<gamma> (Post x,t) = \<beta> (x,t)"
| "pre_post_inter \<alpha> \<beta> \<gamma> (Intermediate x,t) = \<gamma> (x,t)"

lemma pre_post_inter_same: "pre_post_inter \<alpha> \<alpha> \<alpha> x = \<alpha> (apfst untrans_var x)"
proof(cases x)
  case (Pair a b)
  then show ?thesis by (cases a, auto)
qed

lemma pre_post_inter_same_exp:
  "\<lbrakk>e\<rbrakk>(pre_post_inter \<alpha> \<alpha> \<alpha>) = \<lbrakk>rename_vars untrans_var e\<rbrakk>\<alpha>"
proof (induct e)
  case (Var x)
  show ?case
  proof(cases x)
    case (Pair a b)
    then show ?thesis by (cases a, auto)
  qed
next
  case (Fun x1a x2)
  then have [simp]: "(map (\<lambda>s. \<lbrakk>s\<rbrakk> (pre_post_inter \<alpha> \<alpha> \<alpha>)) x2) =
     (map (\<lambda>x. \<lbrakk>rename_vars untrans_var x\<rbrakk> \<alpha>) x2)" by (induct x2, auto)
  show ?case by (auto simp add: o_def)
qed

lemma pre_post_inter_same_satisfies:
  "pre_post_inter \<alpha> \<alpha> \<alpha> \<Turnstile> \<phi> \<longleftrightarrow> \<alpha> \<Turnstile> rename_vars untrans_var \<phi>"
  by(induct \<phi>, auto simp: pre_post_inter_same_exp)

context
  fixes \<alpha> \<beta> \<gamma> :: "('v,'t,'d) valuation"
begin

abbreviation "\<delta> \<equiv> pre_post_inter \<alpha> \<beta> \<gamma>"

lemma pre_post_inter_update[simp]:
  "\<delta>((Pre x,ty):=a) = pre_post_inter (\<alpha>((x,ty):=a)) \<beta> \<gamma>" (is "?l1 = ?r1")
  "\<delta>((Post x,ty):=a) = pre_post_inter \<alpha> (\<beta>((x,ty):=a)) \<gamma>" (is "?l2 = ?r2")
  "\<delta>((Intermediate x,ty):=a) = pre_post_inter \<alpha> \<beta> (\<gamma>((x,ty):=a))" (is "?l3 = ?r3")
proof-
  have "?l1 xx = ?r1 xx \<and> ?l2 xx = ?r2 xx \<and> ?l3 xx = ?r3 xx" for xx by(cases xx, cases "fst xx", auto)
  then show "?l1 = ?r1" "?l2 = ?r2" "?l3 = ?r3" by auto
qed

lemma assignment_pre_post_inter[simp]:
  "assignment \<delta> \<longleftrightarrow> assignment \<alpha> \<and> assignment \<beta> \<and> assignment \<gamma>" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI)
  assume ?r
  then have "\<delta> (x, t) \<in> Values_of_type t" for x t by(cases x, auto)
  then show ?l by auto
next
  assume ?l
  note assignmentD[OF this, of "(_,_)"]
  from this[of "Pre _"] this[of "Post _"] this[of "Intermediate _"] show ?r by auto
qed

lemma eval_pre_post_inter_rename_vars[simp]:
  shows "\<lbrakk>rename_vars Pre e\<rbrakk>\<delta> = \<lbrakk>e\<rbrakk>\<alpha>" (is ?a)
    and "\<lbrakk>rename_vars Post e\<rbrakk>\<delta> = \<lbrakk>e\<rbrakk>\<beta>" (is ?b)
    and "\<lbrakk>rename_vars Intermediate e\<rbrakk>\<delta> = \<lbrakk>e\<rbrakk>\<gamma>" (is ?c)
proof -
  have "?a \<and> ?b \<and> ?c"
  proof(induct e)
  case (Var xx)
    show ?case by (cases xx, auto simp: rename_vars_exp_def)
  case IH: (Fun f es)
    from IH have 1: "map (\<lambda>e.\<lbrakk>e\<rbrakk>\<delta>) (map (rename_vars Pre) es) = map (\<lambda>e.\<lbrakk>e\<rbrakk>\<alpha>) es" by(induct es; auto)
    from IH have 2: "map (\<lambda>e.\<lbrakk>e\<rbrakk>\<delta>) (map (rename_vars Post) es) = map (\<lambda>e.\<lbrakk>e\<rbrakk>\<beta>) es" by(induct es; auto)
    from IH have 3: "map (\<lambda>e.\<lbrakk>e\<rbrakk>\<delta>) (map (rename_vars Intermediate) es) = map (\<lambda>e.\<lbrakk>e\<rbrakk>\<gamma>) es" by(induct es; auto)
    show ?case unfolding rename_vars_exp_simps eval.simps 1 2 3 by auto
  qed
  then show ?a ?b ?c by auto
qed

lemma pre_post_inter_satisfies_rename_vars[simp]:
  "\<delta> \<Turnstile> rename_vars Pre \<phi> \<longleftrightarrow> \<alpha> \<Turnstile> \<phi>"
  "\<delta> \<Turnstile> rename_vars Post \<phi> \<longleftrightarrow> \<beta> \<Turnstile> \<phi>"
  "\<delta> \<Turnstile> rename_vars Intermediate \<phi> \<longleftrightarrow> \<gamma> \<Turnstile> \<phi>" by (induct \<phi>, auto)

end

definition transition_step :: "_ \<Rightarrow> _ \<Rightarrow> _" where
  "transition_step lc \<tau> \<equiv>
    case \<tau> of Transition l r \<phi> \<Rightarrow> { (s,t). \<exists> \<gamma>. lc s \<and> lc t \<and> assignment \<gamma> \<and> location s = l \<and> location t = r \<and>
       pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi>}"

lemma mem_transition_stepI:
  assumes "lc s" "lc t" 
  "\<And>l r \<phi>. \<tau> = Transition l r \<phi> \<Longrightarrow>
    assignment \<gamma> \<and> location s = l \<and> location t = r \<and> pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi>"
  shows "(s,t) \<in> transition_step lc \<tau>"
  using assms by (atomize, cases \<tau>, auto simp: transition_step_def)

lemma mem_transition_step_TransitionI[intro!]:
  assumes "lc s" "lc t" "location s = l" "location t = r" "assignment \<gamma>" "pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi>"
  shows "(s,t) \<in> transition_step lc (Transition l r \<phi>)"
  using assms by (auto simp: transition_step_def)

lemma mem_transition_stepE[elim, consumes 1, case_names Skip Transition]:
  assumes "(s,t) \<in> transition_step lc \<tau>"
  "\<And>\<phi> \<gamma>. \<tau> = Transition (location s) (location t) \<phi> \<Longrightarrow> lc s \<Longrightarrow> lc t \<Longrightarrow>
     assignment \<gamma> \<Longrightarrow> pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi> \<Longrightarrow> thesis"
  shows thesis
  using assms by (cases \<tau>; auto simp: transition_step_def)

lemma mem_transition_step_TransitionE[elim!]:
  assumes "(s,t) \<in> transition_step lc (Transition l r \<phi>)"
  "\<And>\<gamma>. lc s \<Longrightarrow> lc t \<Longrightarrow> location s = l \<Longrightarrow> location t = r \<Longrightarrow>
     assignment \<gamma> \<Longrightarrow> pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi> \<Longrightarrow> thesis"
  shows thesis using assms by auto


lemma transition_step_dom: "transition_step lc \<tau> \<subseteq> Collect lc \<times> Collect lc" by (auto elim: mem_transition_stepE)

abbreviation transitions_step where "transitions_step P \<tau>s \<equiv> \<Union> (transition_step P ` \<tau>s)"
abbreviation transitions_steps where "transitions_steps P \<tau>s \<equiv> (transitions_step P \<tau>s)\<^sup>*"

abbreviation "state_lts (P::('f,'v,'t,'l) lts) s \<equiv> state s \<and> (valuation s \<Turnstile> assertion P (location s))"
  
abbreviation transitions_lts where "transitions_lts P \<equiv> transitions_step (state_lts P)" 
abbreviation transition_step_lts where "transition_step_lts P \<equiv> transition_step (state_lts P)" 
abbreviation transitions_steps_lts where "transitions_steps_lts P \<equiv> transitions_steps (state_lts P)"
abbreviation transitions_step_lts where "transitions_step_lts P \<equiv> transitions_step (state_lts P)"

definition transition :: "('f,'v,'t,'l) lts \<Rightarrow> ('v,'t,'d,'l) state rel" where
  "transition P \<equiv> transitions_lts P (transition_rules P)"

lemma mem_transitionI[intro!]:
  "\<tau> \<in> transition_rules P \<Longrightarrow> (s,t) \<in> transition_step_lts P \<tau> \<Longrightarrow> (s,t) \<in> transition P"
  unfolding transition_def by auto

lemma mem_transitionE[elim]:
  assumes "(s,t) \<in> transition P"
      and "\<And>\<phi> \<gamma>. Transition (location s) (location t) \<phi> \<in> transition_rules P \<Longrightarrow>
           state_lts P s \<Longrightarrow> state_lts P t \<Longrightarrow> assignment \<gamma> \<Longrightarrow> pre_post_inter (valuation s) (valuation t) \<gamma> \<Turnstile> \<phi> \<Longrightarrow> thesis"
  shows "thesis"
  using assms unfolding transition_def by auto

lemma mem_transition_location:
  "(s,t) \<in> transition P \<Longrightarrow> location s \<in> nodes_lts P"
  by (auto intro!: rev_image_eqI simp: nodes_lts_def elim!: mem_transitionE)

lemma mem_transition_dom:
  assumes "(s,t) \<in> transition P"
  shows "state_lts P s" and "state_lts P t"
  using assms by auto

lemma transition_dom: "transition P \<subseteq> Collect (state_lts P) \<times> Collect (state_lts P)" by auto

definition skip_formula :: "('f,'v trans_var,'t) exp formula \<Rightarrow> bool" where
"skip_formula \<phi> \<equiv> \<forall> \<alpha>. assignment \<alpha> \<longrightarrow> (pre_post_inter \<alpha> \<alpha> \<alpha> \<Turnstile> \<phi>)"

lemma skip_formula_transition_step:
  assumes "skip_formula \<phi>" and "assignment \<alpha>"
  and lc: "lc (State \<alpha> a)" "lc (State \<alpha> b)" 
shows "(State \<alpha> a, State \<alpha> b) \<in> transition_step lc (Transition a b \<phi>)"
  using assms(1)[unfolded skip_formula_def] assms(2) lc by auto

lemma skip_formula_transitions:
  assumes "Transition a b \<phi> \<in> transition_rules P"
  and "skip_formula \<phi>"
  and "assignment \<alpha>"
  and "\<alpha> \<Turnstile> assertion P a" "\<alpha> \<Turnstile> assertion P b" 
shows "(State \<alpha> a, State \<alpha> b) \<in> transition P"
  using skip_formula_transition_step[OF assms(2-3), of "state_lts P" a b] assms(1,3-5) by auto

definition skip_transition :: "_ \<Rightarrow> bool" where
  "skip_transition \<tau> = (case \<tau> of Transition _ _ \<phi> \<Rightarrow> skip_formula \<phi>)" 

lemma skip_transition_step: assumes "skip_transition \<tau>"
  and "assignment \<alpha>" 
  and "lc (State \<alpha> (source \<tau>))" "lc (State \<alpha> (target \<tau>))" 
shows "(State \<alpha> (source \<tau>), State \<alpha> (target \<tau>)) \<in> transition_step lc \<tau>" 
proof (cases \<tau>)
  case (Transition a b \<phi>)
  with assms have "skip_formula \<phi>" unfolding skip_transition_def by auto
  from skip_formula_transition_step[OF this assms(2), of lc, OF assms(3-4)] 
  show ?thesis unfolding Transition by auto
qed 

lemma skip_transition: assumes "\<tau> \<in> transition_rules P"
  and "skip_transition \<tau>"
  and "assignment \<alpha>" 
  and "\<alpha> \<Turnstile> assertion P (source \<tau>)" "\<alpha> \<Turnstile> assertion P (target \<tau>)" 
shows "(State \<alpha> (source \<tau>), State \<alpha> (target \<tau>)) \<in> transition P"
  using assms by (auto intro!: skip_transition_step)

definition initial_states :: "('f,'v,'t,'l) lts \<Rightarrow> ('v,'t,'d,'l) state set" where
  "initial_states P = { s. location s \<in> initial P \<and> state_lts P s}"

lemma initial_states: "initial_states P \<subseteq> Collect (state_lts P)" unfolding initial_states_def by auto

lemma initial_states_delete_transitions[simp]:
  "initial_states (delete_transitions P TD) = initial_states P"
by (simp add: initial_states_def)

abbreviation lts_termination :: "('f,'v,'t,'l) lts \<Rightarrow> bool" where
  "lts_termination P \<equiv> SN_on (transition P) (initial_states P)"

abbreviation reachable_states :: "('f,'v,'t,'l) lts \<Rightarrow> ('v,'t,'d,'l) state set" where
  "reachable_states P \<equiv> (transition P)\<^sup>* `` initial_states P"

definition lts_safe :: "('f,'v,'t,'l) lts \<Rightarrow> 'l set \<Rightarrow> bool" where
  "lts_safe P err \<equiv> \<forall> \<alpha> l. l \<in> err \<longrightarrow> State \<alpha> l \<notin> reachable_states P"

lemma reachable_state: assumes "s \<in> reachable_states P" shows "state_lts P s"
proof -
  from assms obtain t where steps: "(t, s) \<in> (transition P)^*"
    and t: "state_lts P t" unfolding initial_states_def by auto
  from steps show ?thesis by (induct rule: rtrancl_induct, insert t, auto)
qed

lemma sub_lts_initial_states: "sub_lts P Q \<Longrightarrow> initial_states P \<subseteq> initial_states Q"
  by (auto simp: initial_states_def)
    
lemma reachable_states_mono:
  assumes "sub_lts P Q"
  shows "reachable_states P \<subseteq> reachable_states Q"
proof
  have tr: "transition P \<subseteq> transition Q" using assms by (auto elim!: mem_transitionE)
  fix x
  assume "x \<in> reachable_states P"
  then obtain start where "(start,x) \<in> (transition P)\<^sup>*" "start \<in> initial_states P" by auto
  then have "(start,x) \<in> (transition Q)\<^sup>*" "start \<in> initial_states Q"
    using rtrancl_mono[OF tr] assms by (auto simp: initial_states_def)
  then show "x \<in> reachable_states Q" by auto
qed

subsection\<open>Invariants\<close>

definition invariant :: "('f,'v,'t,'l) lts \<Rightarrow> 'l \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> bool" where
  "invariant P l \<phi> \<equiv> formula \<phi> \<and> (\<forall>\<alpha>. State \<alpha> l \<in> reachable_states P \<longrightarrow> \<alpha> \<Turnstile> \<phi>)"

lemma invariantI[intro]:
  assumes "formula \<phi>" and "\<And>\<alpha>. State \<alpha> l \<in> reachable_states P \<Longrightarrow> \<alpha> \<Turnstile> \<phi>" shows "invariant P l \<phi>"
  using assms by (auto simp: invariant_def)

lemma invariantE[elim]:
  assumes "invariant P l \<phi>"
      and "formula \<phi> \<Longrightarrow> (\<And>\<alpha>. State \<alpha> l \<in> reachable_states P \<Longrightarrow> \<alpha> \<Turnstile> \<phi>) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: invariant_def)

lemma invariantD[dest]:
  assumes "invariant P l \<phi>" "State \<alpha> l \<in> reachable_states P"
  shows "formula \<phi> \<and> \<alpha> \<Turnstile> \<phi>" using assms by auto

definition invariants :: "('f,'v,'t,'l) lts \<Rightarrow> ('l \<Rightarrow> ('f,'v,'t) exp formula) \<Rightarrow> bool"
  where "invariants P \<Phi> \<equiv> \<forall>l. invariant P l (\<Phi> l)"

lemma invariantsI[intro!]:
  assumes "\<And>l :: 'l. invariant P l (\<Phi> l)"
  shows "invariants P \<Phi>" by (insert assms, auto simp: invariants_def)

lemma invariantsE[elim!]:
  assumes "invariants P \<Phi>" and "(\<And>l :: 'l. invariant P l (\<Phi> l)) \<Longrightarrow> thesis"
  shows "thesis" by (insert assms, auto simp: invariants_def)

lemma invariantsD:
  assumes "invariants P \<Phi>" shows "invariant P l (\<Phi> l)" by (insert assms, auto)

lemma invariants_mono:
  assumes sub: "sub_lts P' P" and inv: "invariants P \<Phi>" shows "invariants P' \<Phi>"
proof(intro invariantsI invariantI)
  fix l \<alpha> assume "State \<alpha> l \<in> reachable_states P'"
  with reachable_states_mono[OF sub] have "State \<alpha> l \<in> reachable_states P" by auto
  from inv this show "\<alpha> \<Turnstile> \<Phi> l" by auto
next
  from inv show "formula (\<Phi> l)" for l by auto
qed

end

subsection \<open>An Implementation of Labeled Transition Systems\<close>

type_synonym ('f,'v,'t,'l,'tr) transitions_impl = "('tr \<times> ('f,'v,'t,'l) transition_rule) list"
type_synonym ('f,'v,'t,'l) assertion_impl = "('l \<times> ('f,'v,'t) exp formula) list"

datatype ('f,'v,'t,'l,'tr) lts_impl = Lts_Impl
  (initial: "'l list")
  (transitions_impl: "('f,'v,'t,'l,'tr) transitions_impl")
  (assertion_impl: "('f,'v,'t,'l) assertion_impl")

definition "transition_of Pi \<equiv> the \<circ> map_of (lts_impl.transitions_impl Pi)"
definition "assertion_of Pi = map_of_default form_True (lts_impl.assertion_impl Pi)" 

lemma transition_of_code[code]: "transition_of Pi = map_of_total 
    (\<lambda> a. showsl_lit (STR ''access to non-existing transition '') o showsl a o
  showsl_lit (STR ''\<newline>available transitions:\<newline>'') o showsl_list (map fst (lts_impl.transitions_impl Pi))) (lts_impl.transitions_impl Pi)" 
  unfolding transition_of_def by simp

definition lts_of :: "('f,'v,'t,'l,'tr) lts_impl \<Rightarrow> ('f,'v,'t,'l) lts" where
  "lts_of Pi = \<lparr>
    lts.initial = set (lts_impl.initial Pi),
    transition_rules = snd ` set (lts_impl.transitions_impl Pi),
    assertion = assertion_of Pi \<rparr>"

lemma lts_of_simps[simp]:
  "lts.initial (lts_of Pi) = set (lts_impl.initial Pi)"
  "transition_rules (lts_of Pi) = snd ` set (lts_impl.transitions_impl Pi)"
  "assertion (lts_of Pi) = assertion_of Pi"
  by (auto simp: lts_of_def)

fun succ_transitions :: "('f,'v,'t,'l,'tr) lts_impl \<Rightarrow> 'l \<Rightarrow> ('f,'v,'t,'l) transition_rule list" where
  "succ_transitions (Lts_Impl i ts lc) l = [ \<tau>. (tr,\<tau>) \<leftarrow> ts, source \<tau> = l ]"

lemma succ_transitions[simp]:
  "set (succ_transitions Pi l) =
   { \<tau>. \<tau> \<in> transition_rules (lts_of Pi) \<and> source \<tau> = l}" by (cases Pi, auto)

definition "nodes_lts_impl Pi = remdups (map (source \<circ> snd) (lts_impl.transitions_impl Pi) @ map (target o snd) (lts_impl.transitions_impl Pi))"

lemma nodes_lts_of[code_unfold]: "nodes_lts (lts_of Pi) = set (nodes_lts_impl Pi)"
  by (unfold nodes_lts_impl_def nodes_lts_def, force)

declare nodes_lts_of[symmetric,simp]


context lts begin

fun lts_impl where "lts_impl (Lts_Impl \<Phi> Ti lc) = (
  (\<forall> (tr,\<tau>) \<in> set Ti. transition_rule \<tau>) \<and>
  (\<forall> (l,\<phi>) \<in> set lc. formula \<phi>))" 

lemma lts_impl: "lts_impl P \<Longrightarrow> lts (lts_of P)"
  by (cases P, auto simp: lts_def assertion_of_def intro: map_of_defaultI)

lemma lts_implI:
  assumes
    "\<And>tr \<tau>. (tr,\<tau>) \<in> set (lts_impl.transitions_impl Pi) \<Longrightarrow> transition_rule \<tau>"
    "\<And>l \<phi>. (l,\<phi>) \<in> set (lts_impl.assertion_impl Pi) \<Longrightarrow> formula \<phi>"
  shows "lts_impl Pi"
  using assms by (cases Pi, auto)

lemma lts_implE:
  assumes "lts_impl Pi"
      and "
    (\<And>tr \<tau>. (tr,\<tau>) \<in> set (lts_impl.transitions_impl Pi) \<Longrightarrow> transition_rule \<tau>) \<Longrightarrow>
    (\<And>l \<phi>. (l,\<phi>) \<in> set (lts_impl.assertion_impl Pi) \<Longrightarrow> formula \<phi>) \<Longrightarrow> thesis"
  shows thesis
by (rule assms(2); cases Pi, insert assms(1), auto simp: assertion_of_def intro: map_of_defaultI)

lemma lts_impl_formula_assertion_of:
  assumes "lts_impl Pi"
  shows "\<And>l. formula (assertion_of Pi l)"
  by (unfold assertion_of_def, rule map_of_defaultI, insert assms, auto elim:lts_implE)

lemma lts_impl_transitions_impl:
  assumes "lts_impl Pi"
      and "(tr,\<tau>) \<in> set (lts_impl.transitions_impl Pi)"
  shows "transition_rule \<tau>"
  using assms by (elim lts_implE)

definition "check_lts_impl Pi = (case Pi of Lts_Impl I Ti lc \<Rightarrow> do {
  check_allm (\<lambda> (tr, t). check (transition_rule t) (showsl_lit (STR ''ill-formed transition in LTS''))) Ti;
  check_allm (\<lambda> (l, f). check (formula f) (showsl_lit (STR ''ill-formed location condition in LTS''))) lc})"

lemma check_lts_impl[simp]: "isOK (check_lts_impl Pi) = lts_impl Pi"
  by (cases Pi, auto simp: lts_def check_lts_impl_def)


subsection \<open>Deleting transitions\<close>

fun sub_lts_impl where "sub_lts_impl (Lts_Impl \<Phi> ts lc) (Lts_Impl I' ts' lc')
  = (\<Phi> = I' \<and> mset ts \<subseteq># mset ts' \<and> lc = lc')"

lemma set_filter_mem: "set (filter (\<lambda>x. x \<in> X) xs) = X \<inter> set xs" by auto

lemma sub_lts_impl_sub_lts: "sub_lts_impl P Q \<Longrightarrow> sub_lts (lts_of P) (lts_of Q)"
proof (cases P, cases Q, goal_cases)
  case (1 I ts lc I' ts' lc')
  then have "mset ts \<subseteq># mset ts'" by auto
  from set_mset_mono[OF this] have sub: "set ts \<subseteq> set ts'" by auto
  { fix a b
    assume "(a,b) \<in> set ts"
    with sub have "(a,b) \<in> set ts'" by auto
    then have "b \<in> snd ` set ts'" by auto
  }
  with 1 show ?thesis by (auto simp: assertion_of_def)
qed

lemma distinct_count_le_1:
  "distinct xs \<longleftrightarrow> (\<forall>x. count (mset xs) x \<le> 1)"
  by (metis count_greater_eq_one_iff distinct_count_atmost_1 eq_iff in_multiset_in_set nat_le_linear not_in_iff)

lemma distinct_mset_subseteq:
  assumes "distinct ys" and "mset xs \<subseteq># mset ys" shows "distinct xs"
  apply (insert assms, unfold distinct_count_le_1 subseteq_mset_def) using le_trans by blast

lemma sub_lts_impl: "sub_lts_impl P Q \<Longrightarrow> lts_impl Q \<Longrightarrow> lts_impl P"
proof (cases P, cases Q, goal_cases)
  case (1 \<Phi> ts lc \<Phi>' ts' lc')
  from 1 have msub: "mset ts \<subseteq># mset ts'" by auto
  from set_mset_mono[OF msub] have set: "set ts \<subseteq> set ts'" by auto
  {
    fix tr \<tau> assume "(tr, \<tau>) \<in> set ts"
    with 1 set set_filter_mem[of "set ts" ts'] have "transition_rule \<tau>" by (auto elim!: ballE[of _ _ "(tr,\<tau>)"])
  }
(*
  moreover 
  from 1 have dist: "distinct (map fst ts')" by auto
  from image_mset_subseteq_mono[OF msub]
  have "mset (map fst ts) \<subseteq># mset (map fst ts')" by auto
  from distinct_mset_subseteq[OF dist this]
  have "distinct (map fst ts)".
  ultimately
*)
  then show ?case using 1 by auto
qed

fun update_transitions_impl where
  "update_transitions_impl (Lts_Impl i ts lc) ts' = (Lts_Impl i ts' lc)"

lemma update_transitions_impl_simps[simp]:
  "transitions_impl (update_transitions_impl P v) = v"
  "initial (update_transitions_impl P v) = lts_impl.initial P"
  "assertion_impl (update_transitions_impl P v) = lts_impl.assertion_impl P" by (atomize(full),cases P,auto)

definition diff_by_label :: "('a \<times> 'b) list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) list" where
  "diff_by_label pairs L = filter (\<lambda> v. fst v \<notin> L) pairs"

lemma diff_by_label_subset [intro]:
  "set (diff_by_label a b) \<subseteq> set a"
unfolding diff_by_label_def by (induct a, auto)

lemma map_fst_diff_by_label:
  "map fst (diff_by_label pairs L) = filter (\<lambda>v. v \<notin> L) (map fst pairs)"
  by(induct pairs, auto simp: diff_by_label_def)

lemma diff_by_label_preseves_distinct:
  "distinct (map fst a) \<Longrightarrow> distinct (map fst (diff_by_label a b))"
  by (unfold map_fst_diff_by_label, rule distinct_filter)

definition del_transitions_impl ::
    "('f,'v,'t,'lx,'tr) lts_impl \<Rightarrow> 'tr list \<Rightarrow> ('f,'v,'t,'lx,'tr) lts_impl" where
"del_transitions_impl P TD
 = (update_transitions_impl P (diff_by_label (transitions_impl P) (set TD)))"

lemma transitions_of_del_transitions_impl[simp]:
  "transitions_impl (del_transitions_impl P D) = diff_by_label (transitions_impl P) (set D)"
unfolding del_transitions_impl_def by simp

lemma del_transitions_impl_set:
assumes "set transs \<subseteq> set transs2"
shows "set (diff_by_label transs (fst ` set TD)) \<subseteq> set transs2"
using diff_by_label_subset[of "transs" "(fst ` set TD)"] assms by simp

lemma del_transitions_impl:
  shows "sub_lts_impl (del_transitions_impl Pi TD) Pi"
    and "sub_lts (delete_transitions (lts_of Pi) {\<tau> | \<tau> tr. (tr,\<tau>) \<in> set (transitions_impl Pi) \<and> tr \<in> set TD})
         (lts_of (del_transitions_impl Pi TD))"
  by (atomize(full), cases Pi, intro conjI sub_ltsI,
    auto simp: assertion_of_def delete_transitions_def del_transitions_impl_def diff_by_label_def mset_filter)



definition "check_invariant_checker f \<equiv>
   \<forall> P. lts (lts_of P) \<longrightarrow> (case f P
    of Inl _ \<Rightarrow> True
    | Inr \<Phi> \<Rightarrow> \<forall>l. invariant (lts_of P) l (\<Phi> l) \<and> formula (\<Phi> l))"

subsection \<open>Refining transition formulas\<close>

fun refine_transition_formula where
  "refine_transition_formula (Transition l r \<phi>) \<psi> = Transition l r (\<phi> \<and>\<^sub>f \<psi>)"
  
definition "refine_transition_formulas P f \<equiv>
   Lts_Impl (lts_impl.initial P)
    (map (\<lambda>(tr,\<tau>). (tr, refine_transition_formula \<tau> (f tr)))
    (transitions_impl P))
    (assertion_impl P)"
  
lemma transition_refine_transition_formula: assumes "transition_rule \<tau>" 
  and "formula \<phi>"
shows "transition_rule (refine_transition_formula \<tau> \<phi>)" 
  using assms by (cases \<tau>, auto)
    
lemma lts_impl_refine_transition_formulas: assumes "lts_impl P" 
  and "\<And> tr \<tau>. (tr, \<tau>) \<in> set (transitions_impl P) \<Longrightarrow> formula (f tr)" 
shows "lts_impl (refine_transition_formulas P f)" 
  using assms unfolding refine_transition_formulas_def
  by (cases P, auto intro!: transition_refine_transition_formula)

lemma initial_refine_transition_formulas[simp]:
  "lts_impl.initial (refine_transition_formulas P f) = lts_impl.initial P"
  by (auto simp: refine_transition_formulas_def)

lemma lc_refine_transition_formulas[simp]:
  "assertion_impl (refine_transition_formulas P f) = assertion_impl P"
  by (auto simp: refine_transition_formulas_def)
    
lemma Transition_mem_refine_transition_formulas:
  assumes "(tr, Transition l r \<phi>') \<in> set (transitions_impl (refine_transition_formulas Pi f))"
  shows "\<exists>\<phi>. (tr, Transition l r \<phi>) \<in> set (transitions_impl Pi) \<and> \<phi>' = (\<phi> \<and>\<^sub>f f tr)"
proof-
  from assms[unfolded refine_transition_formulas_def,simplified]
  obtain \<tau>
  where "(tr,\<tau>) \<in> set (transitions_impl Pi)"
    and "Transition l r \<phi>' = refine_transition_formula \<tau> (f tr)"
    by auto
  moreover then obtain \<phi>
  where "\<tau> = Transition l r \<phi>" and "\<phi>' = (\<phi> \<and>\<^sub>f f tr)" by (cases \<tau>, auto)
  ultimately show ?thesis by auto
qed

subsection \<open>Switching between transition encodings\<close>


fun transition_weakening where
  "transition_weakening assr_l assr_r (Transition s_l t_l f_l) (Transition s_r t_r f_r) =
      (s_l = s_r \<and> t_l = t_r \<and>
       (f_l \<and>\<^sub>f rename_vars Pre (assr_l s_l) \<and>\<^sub>f rename_vars Post (assr_l t_l) \<Longrightarrow>\<^sub>f
        f_r \<and>\<^sub>f rename_vars Pre (assr_r s_r) \<and>\<^sub>f rename_vars Post (assr_r t_r)))"
definition transitions_weakened where
  "transitions_weakened assr_l assr_r l r
    \<equiv> \<forall> t_l \<in> l. (\<exists> t_r \<in> r. transition_weakening assr_l assr_r t_l t_r)"
definition weakened_lts where
  "weakened_lts P Q \<equiv> lts.initial P \<subseteq> lts.initial Q \<and>
     Ball (lts.initial P) (\<lambda> l. assertion P l \<Longrightarrow>\<^sub>f assertion Q l) \<and>
     transitions_weakened (assertion P) (assertion Q) (transition_rules P) (transition_rules Q)"

lemma weakened_lts_initial_states: "weakened_lts P Q \<Longrightarrow> initial_states P \<subseteq> initial_states Q"
proof fix x :: "('a, 't, 'd, 'b) state"
  assume "weakened_lts P Q"
  then have "\<forall>l\<in>lts.initial P. \<L> (assertion P l) \<subseteq> \<L> (assertion Q l)" and
        l:"location x \<in> lts.initial P \<Longrightarrow> location x \<in> lts.initial Q"
        by (auto simp: weakened_lts_def)
  then have "location x \<in> lts.initial P \<Longrightarrow>
         assignment (valuation x) \<Longrightarrow> valuation x \<Turnstile> assertion P (location x)
         \<Longrightarrow> valuation x \<Turnstile> assertion Q (location x)"
    using satisfies_Language by blast
  with l show "x \<in> initial_states P \<Longrightarrow> x \<in> initial_states Q"
     by (auto simp: initial_states_def weakened_lts_def)
qed

lemma transition_weakened_mono:
  assumes "transitions_weakened (assertion P) (assertion Q) (transition_rules P) (transition_rules Q)"
  shows "transition P \<subseteq> transition Q"
proof fix x y
  assume "(x, y) \<in> transition P"
  then obtain \<tau> where \<tau>:"\<tau> \<in> transition_rules P" "(x,y) \<in> transition_step_lts P \<tau>" by fastforce
  from assms \<tau> obtain t_r where t_r: "t_r \<in> transition_rules Q"
    "transition_weakening (assertion P) (assertion Q) \<tau> t_r"
    unfolding transitions_weakened_def by force
  then have trans_w:
    "transition_formula \<tau> \<and>\<^sub>f rename_vars Pre (assertion P (location x)) \<and>\<^sub>f rename_vars Post (assertion P (location y)) \<Longrightarrow>\<^sub>f
     transition_formula t_r \<and>\<^sub>f rename_vars Pre (assertion Q (location x)) \<and>\<^sub>f rename_vars Post (assertion Q (location y))"
    "source \<tau> = source t_r"
    "target \<tau> = target t_r"
    using \<tau> by (atomize(full),cases \<tau>,cases t_r,auto)
  from \<tau> obtain \<gamma> where
    \<gamma>:"\<delta> (valuation x) (valuation y) \<gamma> \<Turnstile> transition_formula \<tau>"
      "(valuation x) \<Turnstile> assertion P (location x)"
      "(valuation y) \<Turnstile> assertion P (location y)"
      "assignment \<gamma>" "assignment (valuation x)" "assignment (valuation y)" by auto
  then have "\<delta> (valuation x) (valuation y) \<gamma> \<Turnstile> transition_formula \<tau>
                                \<and>\<^sub>f rename_vars Pre (assertion P (location x))
                                \<and>\<^sub>f rename_vars Post (assertion P (location y))"
        "assignment (\<delta> (valuation x) (valuation y) \<gamma>)"
   by auto
  from impliesD[OF trans_w(1) this(2,1)] trans_w(2,3) \<tau>(2) \<gamma>(4-)
  have "(x,y) \<in> transition_step_lts Q t_r" by (cases t_r,auto)
  with t_r(1) show "(x, y) \<in> transition Q" by auto
qed

lemma weakened_transition_mono: "weakened_lts P Q \<Longrightarrow> transition P \<subseteq> transition Q"
    by (intro transition_weakened_mono, auto simp:weakened_lts_def)

lemma weakened_reachable_states_mono:
  assumes "weakened_lts P Q"
  shows "reachable_states P \<subseteq> reachable_states Q"
proof
  note ini= assms[THEN weakened_lts_initial_states]
  note tr = weakened_transition_mono[OF assms]
  fix x
  assume "x \<in> reachable_states P"
  then obtain start where "(start,x) \<in> (transition P)\<^sup>*" "start \<in> initial_states P" by auto
  then have "(start,x) \<in> (transition Q)\<^sup>*" "start \<in> initial_states Q"
    using rtrancl_mono[OF tr] ini by (auto simp: initial_states_def)
  then show "x \<in> reachable_states Q" by auto
qed

lemma wekend_lts_SN_on:
  assumes "weakened_lts P Q"
  shows "lts_termination Q \<Longrightarrow> lts_termination P"
proof -
  note ini= SN_on_subset2[OF weakened_lts_initial_states[OF assms]]
  note tr = SN_on_mono[OF _ weakened_transition_mono[OF assms]]
  show "SN_on (transition Q)  (initial_states Q)   \<Longrightarrow> SN_on (transition P) (initial_states P)"
    by (rule tr,rule ini)
qed

subsection \<open>Renaming variables on transitions\<close>

fun transition_renamed where
  "transition_renamed r ass_l ass_r (Transition s_l t_l f_l) (Transition s_r t_r f_r) =
   (let r' = (\<lambda>v. case v of Pre v' \<Rightarrow> Pre (r s_l v') | Post v' \<Rightarrow> Post (r t_l v') |
         Intermediate v' \<Rightarrow> Intermediate (r s_l v') )  in 
      (s_l = s_r \<and> t_l = t_r
      \<and> f_r \<Longrightarrow>\<^sub>f rename_vars r' f_l
      \<and> ass_r s_l  \<Longrightarrow>\<^sub>f rename_vars (r s_l) (ass_l s_l)
      \<and> ass_r t_l  \<Longrightarrow>\<^sub>f rename_vars (r t_l) (ass_l t_l)))"

definition renamed_lts where
  "renamed_lts r L L\<^sub>R \<equiv> lts.initial L\<^sub>R \<subseteq> lts.initial L
   \<and> (\<forall> trL\<^sub>R \<in> transition_rules L\<^sub>R.
        (\<exists> trL \<in> transition_rules L. transition_renamed r (assertion L) (assertion L\<^sub>R) trL trL\<^sub>R))"

lemma rename_delta_formula_implies:
  assumes "\<delta> v1 v2 v3 \<Turnstile> map_formula (rename_vars (\<lambda>v. case v of Pre v' \<Rightarrow> Pre (r1 v') | Post v' \<Rightarrow> Post (r2 v') |
         Intermediate v' \<Rightarrow> Intermediate (r3 v'))) \<phi>"
  shows "\<delta> (\<lambda>(x, t). v1 (r1 x, t)) (\<lambda>(x, t). v2 (r2 x, t)) (\<lambda>(x, t). v3 (r3 x, t)) \<Turnstile> \<phi>"
  (is "?\<delta> \<Turnstile> \<phi>" )
proof -
  have "?\<delta> (x, t) = \<delta> v1 v2 v3 ((\<lambda>v. case v of Pre v' \<Rightarrow> Pre (r1 v') | Post v' \<Rightarrow> Post (r2 v') |
         Intermediate v' \<Rightarrow> Intermediate (r3 v')) x, t)" for x t
    by (cases x) (auto)
  then show ?thesis
    using assms apply(subst (asm) satisfies_rename_vars[of ?\<delta>])
    by auto
qed

lemma lts_renaming_termination:
  assumes "lts_termination L" "renamed_lts r L L\<^sub>R"
  shows "lts_termination L\<^sub>R"
proof -
  have 1: False if assms': "f 0 \<in> initial_states L\<^sub>R" "\<forall>i. (f i, f (Suc i)) \<in> transition L\<^sub>R" for f
  proof -
    have af: "assignment (valuation (f i))" for i
      using lts.state_def that(2) by blast
    define f' where "f' = (\<lambda>n. case (f n) of State v l \<Rightarrow> State (\<lambda>(x, t). v (r l x, t)) l)"
    have af': "assignment (valuation (f' i))" for i
      using lts.state_def that(2) 
      by (metis (mono_tags, lifting) af f'_def old.prod.case pre_sorted_algebra.assignmentE
          pre_sorted_algebra.assignmentI snd_conv state.case_eq_if state.sel(1))
    have b: "valuation (f 0) \<Turnstile> (assertion L\<^sub>R (location (f 0)))"
      using that unfolding initial_states_def by (auto)
    have a: "f' 0 \<in> initial_states L"
    proof -
      obtain v l where f0: "f 0 = State v l"
        by (cases "f 0") auto
      obtain \<tau>\<^sub>R \<phi>\<^sub>R where \<tau>\<^sub>R: "\<tau>\<^sub>R = Transition (location (f 0)) (location (f 1)) \<phi>\<^sub>R" "\<tau>\<^sub>R \<in> transition_rules L\<^sub>R"
        using assms' by fastforce
      obtain \<tau> where \<tau>: "transition_renamed r (assertion L) (assertion L\<^sub>R) \<tau> \<tau>\<^sub>R"
        using \<tau>\<^sub>R assms unfolding renamed_lts_def by blast
      have a: "implies (assertion L\<^sub>R l) (rename_vars (r l) (assertion L l))"
        using \<tau>\<^sub>R f0 \<tau> by (cases \<tau>, cases \<tau>\<^sub>R) (simp)
      have "v \<Turnstile> rename_vars (r l) (assertion L l)"
        by (rule impliesD) (use a f0 b af[of 0] in auto)
      then have "(\<lambda>(x, t). v ((r l) x, t)) \<Turnstile> assertion L l"
        by (metis (mono_tags, lifting) old.prod.case satisfies_rename_vars)
      then have "valuation (f' 0) \<Turnstile> assertion L (location (f' 0))"
        using b f0 assms unfolding renamed_lts_def
        by (auto simp add: f'_def split: state.splits)
      then show ?thesis
        unfolding initial_states_def using af' assms that unfolding renamed_lts_def
          f'_def initial_states_def
        by (auto split: state.splits)
    qed
      (* TODO: clean up proof *)
    have b: "(f' i, f' (Suc i)) \<in> transition L" for i
    proof - 
      have "(f i, f (Suc i)) \<in> transition L\<^sub>R"
        using that by simp
      then obtain \<gamma> \<phi> where \<phi>: "Transition (location (f i)) (location (f (Suc i))) \<phi> \<in> transition_rules L\<^sub>R"
        "assignment \<gamma>" "\<delta> (valuation (f i)) (valuation (f (Suc i))) \<gamma> \<Turnstile> \<phi>"
        by auto
      define t\<^sub>R where "t\<^sub>R = Transition (location (f i)) (location (f (Suc i))) \<phi>"
      obtain t where t: "t \<in> transition_rules L" "transition_renamed r (assertion L) (assertion L\<^sub>R) t t\<^sub>R"
        apply(atomize_elim)
        using assms \<phi> unfolding renamed_lts_def t\<^sub>R_def by auto
      define \<phi>\<^sub>L where "\<phi>\<^sub>L = transition_formula t"
      obtain  x1 x2 x1a x2a where x1: "f i = State x1 x2" "f (Suc i) = State x1a x2a"
        by (metis state.exhaust state.sel)
      have a: "\<delta> (valuation (f' i)) (valuation (f' (Suc i))) (\<lambda>(x,t). \<gamma> (r (location (f' i)) x, t)) \<Turnstile> \<phi>\<^sub>L"
      proof -
        have "\<delta> x1 x1a \<gamma> \<Turnstile> \<phi>"
          using \<phi> x1 by simp
        then have "\<delta> x1 x1a \<gamma> \<Turnstile> map_formula (rename_vars (\<lambda>v. case v of Pre v' \<Rightarrow> Pre (r x2 v') | 
                   Post v' \<Rightarrow> Post (r x2a v') | Intermediate v' \<Rightarrow> Intermediate (r x2 v'))) \<phi>\<^sub>L"
          apply(cases t)
          using t x1 t\<^sub>R_def af[of i] af[of "Suc i"] transition_renamed.simps \<phi> assignment_pre_post_inter \<phi>\<^sub>L_def state.sel
          by (auto intro!: impliesD[of \<phi>] simp del : implies_Language)
        then show ?thesis
          unfolding f'_def using x1 rename_delta_formula_implies by fastforce
      qed
      have b: "Transition (location (f' i)) (location (f' (Suc i))) \<phi>\<^sub>L \<in> transition_rules L"
        using t \<phi>\<^sub>L_def unfolding t\<^sub>R_def f'_def transition_renamed.simps by (cases t) (auto split: state.splits)
      have c: "(\<lambda>(x, t). x1 (r x2 x, t)) \<Turnstile> assertion L x2"
      proof -
        have "x1 \<Turnstile> assertion L\<^sub>R x2"
          using x1 \<open>(f i, f (Suc i)) \<in> transition L\<^sub>R\<close> by  auto
        then have "x1 \<Turnstile> rename_vars (r x2) (assertion L x2)"
          using x1 t t\<^sub>R_def by (cases t, auto)
            (metis \<open>(f i, f (Suc i)) \<in> transition L\<^sub>R\<close> impliesD implies_Language mem_transitionE state.sel(1) state_def)
        then show ?thesis
          using satisfies_rename_vars by (smt case_prod_conv)
      qed
      have d: "(\<lambda>(x, t). x1a (r x2a x, t)) \<Turnstile> assertion L x2a"
      proof -
        have "x1a \<Turnstile> assertion L\<^sub>R x2a"
          using x1 \<open>(f i, f (Suc i)) \<in> transition L\<^sub>R\<close> by  auto
        then have "x1a \<Turnstile> rename_vars (r x2a) (assertion L x2a)"
          using x1 t t\<^sub>R_def by (cases t, auto)
            (metis \<open>(f i, f (Suc i)) \<in> transition L\<^sub>R\<close> impliesD implies_Language mem_transitionE state.sel(1) state_def)
        then show ?thesis
          using satisfies_rename_vars by (smt case_prod_conv)
      qed
      from a show ?thesis
        apply(intro mem_transitionI[of "Transition (location (f' i)) (location (f' (Suc i))) \<phi>\<^sub>L"])
        using f'_def x1 a b c d af[of i] af[of "Suc i"]  af'[of i] af'[of "Suc i"] \<phi>(2)
        by (auto split: state.splits intro: assignment_rename_vars simp add: assignment_rename_vars)
    qed
    then show ?thesis
      using a b assms SN_onE by  blast
  qed
  then show ?thesis
    using SN_onI by blast
qed

end

declare lts.transition_rule.simps[code]
declare lts.check_lts_impl_def[code]
declare lts.del_transitions_impl_def[code]
declare lts.refine_transition_formulas_def[code] 
declare lts.update_transitions_impl.simps[code] 
declare lts.diff_by_label_def[code]
declare lts.refine_transition_formula.simps[code]


end
