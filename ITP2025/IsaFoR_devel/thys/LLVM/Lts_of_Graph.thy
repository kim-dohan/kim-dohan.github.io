theory Lts_of_Graph
  imports
    SE_Graph_Pre
    LTS.LTS
begin

context IA_locale
begin

sublocale lts  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and type_fixer= "TYPE(_)".
end


context graph'
begin

fun pre_post_mapping :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ IA.formula" where
  "pre_post_mapping pre pri [] = True\<^sub>f"
| "pre_post_mapping pre pri ((lv, t) # lvs) =
      (let encode_eq  = Atom (Fun IA.EqF [Var ((pre lv, t)), Var ((pri lv, t))]) in
       encode_eq  \<and>\<^sub>f pre_post_mapping pre pri lvs)"

context
  fixes loc_of_node :: "'n \<Rightarrow> 'l"
begin

definition lts_rule_of_edge :: "'n \<Rightarrow> 'n \<Rightarrow> (IA.sig, 'lv, IA.ty, 'l) transition_rule" where
  "lts_rule_of_edge n m = (let
     as\<^sub>1 = as_of_node n;
     as\<^sub>2 = as_of_node m;
     \<mu> = renaming_of_edge (n, m);
     kb\<^sub>1 = kb as\<^sub>1;
     kb\<^sub>2 = kb as\<^sub>2;
     pre_f = pre_post_mapping Pre Intermediate (vars_formula_list kb\<^sub>1);
     kb1_f = rename_vars Intermediate kb\<^sub>1;
     post_f = pre_post_mapping Post (Intermediate o \<mu>) (vars_formula_list kb\<^sub>2);
     kb2_f = rename_vars (Intermediate o \<mu>) kb\<^sub>2
     in Transition (loc_of_node n) (loc_of_node m) (pre_f \<and>\<^sub>f post_f \<and>\<^sub>f kb1_f \<and>\<^sub>f kb2_f))"

abbreviation lts_state where "lts_state \<sigma> n \<equiv> State \<sigma> (loc_of_node n)"

definition lts_of_graph where "lts_of_graph ns = \<lparr>
   lts.initial = ns,
   transition_rules = (\<lambda> (n,m). lts_rule_of_edge n m) ` edges,
   assertion = (\<lambda> _. True\<^sub>f)
  \<rparr>"

lemma lts_rule_of_edge:
  assumes "((n,\<sigma>), (m,\<tau>)) \<in> as_step"
  shows "(lts_state \<sigma> n, lts_state \<tau> m)
         \<in> IA.transition_step (\<lambda> \<sigma>. IA.assignment (valuation \<sigma>)) (lts_rule_of_edge n m)"
  using assms
proof (induction rule: as_step.induct)
  case (1 n\<^sub>1 n\<^sub>2 \<mu> \<sigma> \<tau>)
  obtain \<sigma>' where \<sigma>': "IA.assignment \<sigma>'" "(\<forall>lv\<in>all_sym_vars (as_of_node n\<^sub>1). \<forall>ty. \<sigma> (lv, ty) = \<sigma>'(lv, ty))"
     "(\<forall>lv ty. \<tau> (lv, ty) = \<sigma>' (\<mu> lv, ty))" "IA.satisfies \<sigma>' (kb (as_of_node n\<^sub>1))"
    using 1 unfolding as_as_step.simps by blast
  have v: "IA.assignment \<sigma>" "IA.assignment \<tau>"
    using 1 by (auto simp add: as_as_step.simps comp_def IA.assignment_def)
  have Pre: "IA.satisfies (IA.\<delta> \<sigma> \<tau> \<sigma>') (pre_post_mapping Pre Intermediate xs)"
    if "fst ` set xs \<subseteq> all_sym_vars (as_of_node n\<^sub>1)" for xs
    using 1 that \<sigma>' by (induct xs, auto simp add: as_as_step.simps split: option.split)
  have Post: "IA.satisfies (IA.\<delta> \<sigma> \<tau> \<sigma>') (pre_post_mapping Post (Intermediate \<circ> \<mu>) xs)" for xs
    using 1 \<sigma>' by (induct xs, auto simp add: as_as_step.simps split: option.split)
  have id: "map_formula (rename_vars (Intermediate \<circ> \<mu>)) (kb as)
      = map_formula (rename_vars Intermediate) (map_formula (rename_vars \<mu>) (kb as))" for as
    by simp
  have kbm: "IA.satisfies (IA.\<delta> \<sigma> \<tau> \<sigma>') (map_formula (rename_vars (Intermediate \<circ> \<mu>)) (kb (as_of_node n\<^sub>2)))"
    unfolding id IA.pre_post_inter_satisfies_rename_vars
    using 1 \<sigma>' by (auto simp add: IA.satisfies_rename_vars[of \<tau>] as_as_step.simps)
  show ?case
    unfolding lts_rule_of_edge_def Let_def option.simps
    using 1 Pre Post v kbm \<sigma>'
    apply (intro IA.mem_transition_step_TransitionI[where \<gamma> = \<sigma>'], auto simp add: as_as_step.simps)
    apply(rule Pre)
    unfolding all_sym_vars_def using vars_formula_list
    by (metis Un_iff subsetI)
qed

lemma as_step_to_lts_step:
  assumes "((n,\<sigma>), (m,\<tau>)) \<in> as_step"
  shows "(lts_state \<sigma> n, lts_state \<tau> m) \<in> IA.transition (lts_of_graph ns)"
proof -
  from as_step_edge[OF assms] lts_rule_of_edge[OF assms]
  show ?thesis unfolding IA.transition_def lts_of_graph_def lts.simps IA.state_def
    by (simp, intro bexI[of _ "(n,m)"], auto)
qed

lemma lts_termination_SN_as_step:
  assumes "IA.lts_termination (lts_of_graph {loc_of_node n\<^sub>i})"
  shows "SN_on as_step {(n\<^sub>i, v)}"
proof
  fix states
  assume steps: "\<forall>i. (states i, states (Suc i)) \<in> as_step"
  assume init: "states 0 \<in> {(n\<^sub>i, v)}"
  define \<sigma> where "\<sigma> = snd o states"
  define n where "n = fst o states"
  define ls where "ls i = lts_state (\<sigma> i) (n i)" for i
  have steps: "\<And> i. ((n i, \<sigma> i), (n (Suc i), \<sigma> (Suc i))) \<in> as_step"
    using steps unfolding \<sigma>_def n_def by auto
  from steps[of 0] have n0: "n 0 \<in> nodes \<and> IA.assignment (\<sigma> 0)"
    by (induct rule: as_step.induct, auto simp add: as_as_step.simps nodes_def)
  have steps: "\<And> i. (ls i, ls (Suc i)) \<in> IA.transition (lts_of_graph {loc_of_node n\<^sub>i})"
    using as_step_to_lts_step[OF steps] unfolding ls_def by simp
  have init: "ls 0 \<in> IA.initial_states (lts_of_graph {loc_of_node n\<^sub>i})"
    unfolding IA.initial_states_def ls_def lts_of_graph_def lts.simps using n0 init
    by (auto simp add: IA.assignment_def n_def)
  from assms steps init show False by auto
qed

end
end

declare graph'.pre_post_mapping.simps [code]

end
