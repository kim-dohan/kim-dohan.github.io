theory SE_Graph_Pre
  imports
    Abstract_State
begin

type_synonym ('n,'v) as_config = "'n \<times> ('v \<times> IA.ty \<Rightarrow> IA.val)"

locale graph' =
  fixes as_of_node :: "'n \<Rightarrow> ('pos,'pv,'lv::linorder,'type) abstract_state"
    and renaming_of_edge :: "('n \<times> 'n) \<Rightarrow> ('lv \<Rightarrow> 'lv)"
    and edges ::  "('n \<times> 'n) set"
begin

definition nodes where "nodes = fst ` edges \<union> snd ` edges"

inductive_set as_step :: "(('n,'lv) as_config \<times> ('n,'lv) as_config) set"
  where
    "((n\<^sub>1,\<sigma>), (n\<^sub>2,\<tau>)) \<in> as_step"
  if
   "(n\<^sub>1, n\<^sub>2) \<in> edges"
   "renaming_of_edge (n\<^sub>1, n\<^sub>2) = \<mu>"
   "as_as_step (as_of_node n\<^sub>1) (as_of_node n\<^sub>2) \<sigma> \<tau> \<mu>"


lemma as_step_nodes: "((n\<^sub>1,\<sigma>), (n\<^sub>2,\<tau>)) \<in> as_step \<Longrightarrow> {n\<^sub>1,n\<^sub>2} \<subseteq> nodes"
  by (induct rule: as_step.induct, auto simp add: nodes_def)

lemma as_step_edge: "((n\<^sub>1,\<sigma>), (n\<^sub>2,\<tau>)) \<in> as_step \<Longrightarrow> (n\<^sub>1,n\<^sub>2) \<in> edges"
  by (induct rule: as_step.induct, auto)

end


end
