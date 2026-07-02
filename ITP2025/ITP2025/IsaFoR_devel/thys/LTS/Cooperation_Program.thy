theory Cooperation_Program
imports
  LTS
  "HOL-Library.Mapping" 
  Framework.Relative_DP_Framework (* for some notations *)
  "Well_Quasi_Orders.Well_Quasi_Orders"
  Indexed_Rewriting
  Knuth_Bendix_Order.Lexicographic_Extension
begin

hide_const (open) FuncSet.Pi

sublocale SN_order_pair \<subseteq> non_inf_order by (unfold_locales, fact SN_imp_non_inf[OF SN])

subsection \<open>Cooperation problem\<close>

datatype 'l sharp = Flat 'l | Sharp 'l

instantiation sharp :: (showl) showl
begin
fun showsl_sharp where
  "showsl_sharp (Flat s) = showsl s" 
| "showsl_sharp (Sharp s) = showsl_lit (STR ''#'') o showsl s" 
definition "showsl_list (xs :: 'a sharp list) = default_showsl_list showsl xs"
instance ..
end

derive compare_order sharp

type_synonym ('f,'v,'t,'l) cooperation_problem = "('f,'v,'t,'l sharp) lts"

fun natural where
  "natural (Sharp l) = l"
| "natural (Flat l) = l"

fun sharp_transition where
  "sharp_transition (Transition l r \<phi>) = Transition (Sharp l) (Sharp r) \<phi>"

fun "flat_transition" where
  "flat_transition (Transition l r \<phi>) = Transition (Flat l) (Flat r) \<phi>"

fun is_sharp where "is_sharp (Flat _) = False" | "is_sharp (Sharp _) = True"

abbreviation "is_sharp_transition \<tau> \<equiv> is_sharp (source \<tau>)"

lemma source_sharp_transition[simp]: "source (sharp_transition \<tau>) = Sharp (source \<tau>)"
  and source_flat_transition[simp]: "source (flat_transition \<tau>) = Flat (source \<tau>)"
  and target_sharp_transition[simp]: "target (sharp_transition \<tau>) = Sharp (target \<tau>)"
  and target_flat_transition[simp]: "target (flat_transition \<tau>) = Flat (target \<tau>)"
  and formula_sharp_transition[simp]: "transition_formula (sharp_transition \<tau>) = transition_formula \<tau>"
  and formula_flat_transition[simp]: "transition_formula (flat_transition \<tau>) = transition_formula \<tau>"
  by (atomize(full), cases \<tau>, auto)

abbreviation "sharp_state s \<equiv> relabel_state Sharp s"
abbreviation "flat_state s \<equiv> relabel_state Flat s"
abbreviation "sharp_transitions_of P \<equiv> { \<tau> \<in> transition_rules P. is_sharp_transition \<tau> }"
abbreviation "flat_transitions_of P \<equiv> { \<tau> \<in> transition_rules P. \<not> is_sharp_transition \<tau> }"

definition lift_state_conditions where "lift_state_conditions lc = lc \<circ> relabel_state natural"

fun sharp_state_pair where "sharp_state_pair (l,r) = (sharp_state l, sharp_state r)"

lemma relabel_state_natural_sharp[simp]: "relabel_state natural (sharp_state s) = s" by (cases s, auto)
lemma relabel_state_natural_flat[simp]: "relabel_state natural (flat_state s) = s" by (cases s, auto)

context lts begin

lemma
  assumes st: "(s,t) \<in> transition_step lc \<tau>"
  shows sharp_transition: "(sharp_state s, sharp_state t) \<in> transition_step (lift_state_conditions lc) (sharp_transition \<tau>)" (is ?a)
    and flat_transition: "(flat_state s, flat_state t) \<in> transition_step (lift_state_conditions lc) (flat_transition \<tau>)" (is ?b)
using st by (atomize(full), cases rule: mem_transition_stepE, auto simp: lift_state_conditions_def)

lemma flat_state_not_sharp: "flat_state s \<notin> range sharp_state"
proof (safe)
  fix t assume "flat_state s = sharp_state t" then show False by (cases s, cases t, auto)
qed

lemma sharp_transition_id:
  "transition_step (lift_state_conditions lc) (sharp_transition \<tau>) = sharp_state_pair ` (transition_step lc \<tau>)" (is "?L = ?R")
proof-
  {
    fix s t assume "(s,t) \<in> transition_step lc \<tau>"
    then have "sharp_state_pair (s,t) \<in> ?L"
      unfolding sharp_state_pair.simps by(intro sharp_transition, auto)
  }
  moreover
  {
    fix s t assume st: "(s,t) \<in> ?L"
    let ?\<tau> = "sharp_transition \<tau>"
    note * = mem_transition_stepE[OF st, unfolded lift_state_conditions_def]
    have loc: "location s = Sharp (source \<tau>)" "location t = Sharp (target \<tau>)" using st
      by (atomize(full), cases \<tau>, auto)
    from loc have [simp]: "relabel_state Sharp (relabel_state natural s) = s" by (cases s, auto)
    from loc have [simp]: "relabel_state Sharp (relabel_state natural t) = t" by (cases t, auto)
    have "(relabel_state natural s, relabel_state natural t) \<in> transition_step lc \<tau>"
      apply (cases rule:*; intro mem_transition_stepI; auto?) apply (metis natural.simps)+ done
    note imageI[OF this, of sharp_state_pair]
    then have "(s,t) \<in> ?R" by simp
  }
  ultimately show ?thesis by auto
qed

lemma sharp_transitions:
  assumes Rstep: "(s,t) \<in> transitions_step lc \<tau>s"
  shows "(sharp_state s, sharp_state t) \<in> transitions_step (lift_state_conditions lc) (sharp_transition ` \<tau>s)"
proof-
  from Rstep obtain \<tau>
    where \<tau>: "\<tau> \<in> \<tau>s" and step: "(s,t) \<in> transition_step lc \<tau>" by force
  show ?thesis
  proof
    from \<tau> show "sharp_transition \<tau> \<in> sharp_transition ` \<tau>s" by auto
    from step show "(sharp_state s, sharp_state t) \<in> transition_step (lift_state_conditions lc) (sharp_transition \<tau>)"
      by (rule sharp_transition)
  qed
qed

abbreviation "cooperation_SN P \<equiv>
  indexed_rewriting.cooperation_SN_on (transition_step_lts P)
    (flat_transitions_of P) (sharp_transitions_of P) (initial_states P)"


lemma trivial_cooperation_program:
  assumes "sharp_transitions_of P = {}" shows "cooperation_SN P"
proof-
  define freeze where "freeze \<equiv> transition_step_lts P"
  interpret indexed_rewriting "freeze".
  show ?thesis by (unfold assms, fold freeze_def, auto)
qed

definition "cooperation_SN_impl Pi \<equiv> lts_impl Pi \<longrightarrow> cooperation_SN (lts_of Pi)"

lemma cooperation_SN_implI[intro]:
  assumes "lts_impl Pi \<Longrightarrow> cooperation_SN (lts_of Pi)"
  shows "cooperation_SN_impl Pi"
  using assms by (auto simp: cooperation_SN_impl_def)

lemma cooperation_SN_implE[elim]:
  assumes "cooperation_SN_impl Pi"
      and "(lts_impl Pi \<Longrightarrow> cooperation_SN (lts_of Pi)) \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: cooperation_SN_impl_def)

end

definition call_graph_impl :: "('f,'v,'t,'l,'tr) lts_impl \<Rightarrow> ('l \<times> 'l)list" where 
  "call_graph_impl R = remdups [(source (snd \<tau>), target (snd \<tau>)). \<tau> \<leftarrow> transitions_impl R]" 

lemma call_graph_impl[simp]: "set (call_graph_impl Ri) = call_graph_of_lts (lts_of Ri)" 
  unfolding call_graph_of_lts_def call_graph_impl_def by auto

locale pre_lts_checker = lts where type_fixer = "TYPE(_)" + pre_logic_checker begin

definition "check_skip_transition \<tau> = (case \<tau> of Transition l r \<phi> \<Rightarrow> check_valid_formula default (rename_vars untrans_var \<phi>))" 

end

declare pre_lts_checker.check_skip_transition_def[code]

locale lts_checker = pre_lts_checker + logic_checker
begin

lemma check_skip_transition: assumes "isOK(check_skip_transition \<tau>)" "transition_rule \<tau>" 
  shows "skip_transition \<tau>" 
proof (cases \<tau>)
  case (Transition a b \<phi>)
  from assms[unfolded Transition check_skip_transition_def] 
  have 1: "isOK(check_valid_formula default (rename_vars untrans_var \<phi>))" "formula \<phi>" by auto
  then have 2: "formula (rename_vars untrans_var \<phi>)" by auto
  from check_valid_formula[OF 1(1) 2]
  have sk:"skip_formula \<phi>" unfolding skip_formula_def pre_post_inter_same_satisfies by auto
  then show ?thesis by (auto simp: Transition skip_transition_def)
qed 

end

context lts begin

lemma invariant_sub_lts:
  assumes "invariant P l \<phi>"
    and "sub_lts P' P"
  shows "invariant P' l \<phi>" using assms
  by (meson invariant_def reachable_states_mono set_mp)

lemma invariant_del_transitions_impl:
  assumes "invariant (lts_of P) l \<phi>"
  shows "invariant (lts_of (del_transitions_impl P TD)) l \<phi>"
  apply (rule invariant_sub_lts[OF assms])
  apply (rule sub_lts_impl_sub_lts[OF del_transitions_impl(1)])
  done

lemma cooperation_SN_sub_lts: assumes "sub_lts P Q" and "cooperation_SN Q" shows "cooperation_SN P"
  apply (insert assms)
  apply (rule indexed_rewriting.cooperation_SN_on_subset[of _ "flat_transitions_of Q" _ "sharp_transitions_of Q"])
  apply (insert sub_lts_initial_states[OF assms(1)], auto)
  done

end

end
