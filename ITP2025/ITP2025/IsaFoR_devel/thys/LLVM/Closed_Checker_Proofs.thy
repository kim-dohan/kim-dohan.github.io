theory Closed_Checker_Proofs
imports Closed_Checker

begin

unbundle IA_formula_notation



lemma Mapping_values:  "(x \<in> Mapping_values m) \<longleftrightarrow> (\<exists>n. Mapping.lookup m n = Some x)"
proof -
  have "\<exists>n. Mapping.lookup m n = Some x" if a: "x \<in> Mapping_values m"
  proof -
    obtain n where "n \<in> Mapping.keys m" "x = the (Mapping.lookup m n)"
      using a unfolding Mapping_values_def by auto
    then have "Mapping.lookup m n = Some x"
      by (simp add: domIff keys_dom_lookup)
    then show ?thesis
      by blast
  qed
  moreover have "x \<in> Mapping_values m" if a: "Mapping.lookup m n = Some x" for n
  proof -
    have "n \<in> Mapping.keys m"
      using a by (simp add: keys_is_none_rep)
    then show ?thesis
      unfolding Mapping_values_def using a by (force simp add: image_def)
  qed
  ultimately show ?thesis
    by blast
qed


lemma Mapping_values_ran: "Mapping_values m = ran (Mapping.lookup m)"
  using Mapping_values by (fastforce simp add: ran_def)

context formula
begin

lemma form_imp_implies: "valid (\<phi> \<longrightarrow>\<^sub>f \<rho>) \<longleftrightarrow> implies \<phi> \<rho>"
 using satisfies_Language valid_def by (auto)

end

lemma lookup_None_keys': "x \<notin> Mapping.keys m \<longleftrightarrow> Mapping.lookup m x = None"
  by (simp add: domIff keys_dom_lookup)

lemma update_asFun:
  assumes "isOK (update_asFun as\<^sub>1 as\<^sub>2 n v\<^sub>n \<phi>)"
  shows "update_as (asm_to_as as\<^sub>1) (asm_to_as as\<^sub>2) n v\<^sub>n \<phi>"
proof -
  have "IA.implies (Formula.form_and (kb as\<^sub>1) \<phi>) (kb as\<^sub>2)"
    apply(subst IA.form_imp_implies[symmetric])
    using assms by (auto intro!: IA.check_valid_formula)
  moreover have "Mapping.lookup (abstract_state_mapping.stack as\<^sub>2) x =
        (Mapping.lookup (abstract_state_mapping.stack as\<^sub>1)(n \<mapsto> v\<^sub>n)) x" for x
    apply(cases "x \<in> Mapping.keys (abstract_state_mapping.stack as\<^sub>1)")
    using assms by (auto simp add: asm_to_as_simps simp add: lookup_None_keys')
  ultimately show ?thesis
    using assms Mapping_values
    by (fastforce intro!: update_as.intros)
qed

lemma checkFormula:
  assumes "isOK (checkFormula (\<phi> \<longrightarrow>\<^sub>f \<rho>))"
  shows "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>"
  using assms
  unfolding checkFormula_def IA.form_imp_implies[symmetric]
  using IA.check_valid_formula by (force)

lemma checkFormula_formula:
  assumes "isOK (checkFormula (\<phi> \<longrightarrow>\<^sub>f \<rho>))"
  shows "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
  using assms
  unfolding checkFormula_def by (force)

context graph_exec
begin

lemma evalFun_evalInf:
  assumes "isOK (evalFun n\<^sub>1 n\<^sub>2 v\<^sub>n)"
  shows "evalInf n\<^sub>1 n\<^sub>2"
proof -
  obtain n binop o\<^sub>1 o\<^sub>2 where
    "find_statement prog (abstract_state_mapping.pos (as_map_of_node n\<^sub>1)) =
          Inr (Instruction (Assignment n (Binop binop o\<^sub>1 o\<^sub>2)))"
    using assms by (auto simp add: evalFun_def split: stuck.splits step_splits)
  then show ?thesis
    using assms
    apply(auto simp add: evalFun_def isOK_def check_def
    split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
    elim!: option_to_sum.elims)
  apply(intro evalInf.intros[of "asm_to_as (as_map_of_node n\<^sub>1)" "asm_to_as (as_map_of_node n\<^sub>2)" n\<^sub>1 n\<^sub>2])
    by (auto simp add: renaming_of_edge'_def intro!: update_asFun evalAsInf.intros)
qed

lemma evalExternalFun_evalExternalInf:
  assumes "isOK (evalExternalFun n\<^sub>1 n\<^sub>2 v\<^sub>n)"
  shows "evalExternalInf n\<^sub>1 n\<^sub>2"
proof -
  obtain n t fn as where
    "find_statement prog (abstract_state_mapping.pos (as_map_of_node n\<^sub>1)) =
          Inr (Instruction (Assignment n (R_Call (Call t fn as))))"
    using assms by (auto simp add: evalExternalFun_def split: stuck.splits step_splits)
  then show ?thesis
    using assms
    apply(auto simp add: evalExternalFun_def isOK_def check_def
    split: sum.splits option.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
llvm_fun.splits
    elim!: option_to_sum.elims)
  apply(intro evalExternalInf.intros[of n\<^sub>1 n\<^sub>2])
    by (auto simp add: renaming_of_edge'_def intro!: update_asFun evalExternalAsInf.intros)
qed

lemma genFun_genInf:
  assumes "isOK (genFun n\<^sub>1 n\<^sub>2)"
  shows "genInf n\<^sub>1 n\<^sub>2"
proof -
  have 1: "IA.implies \<phi> \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()"
                               "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "'lv IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  have "genAsInf (asm_to_as (as_map_of_node n\<^sub>1)) (asm_to_as (as_map_of_node n\<^sub>2)) (renaming_of_edge' (n\<^sub>1, n\<^sub>2))"
  using assms
    apply(auto simp add: isOK_def check_def genFun_def renaming_of_edge'_def
    split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits option.splits
    elim!: option_to_sum.elims)
    apply(rule genAsInf.intros)
             prefer 3
    apply(rule 1)
       apply (auto intro!: 1 simp add: lookup_None_keys intro!: update_asFun)
  by (metis domD domI keys_dom_lookup)
  then show ?thesis
    using assms
    apply(auto simp add: isOK_def check_def genFun_def
    split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits option.splits
    elim!: option_to_sum.elims)
    using genInf.intros[of "asm_to_as (as_map_of_node n\<^sub>1)" "asm_to_as (as_map_of_node n\<^sub>2)"]
    by (auto intro!: 1 simp add: lookup_None_keys intro!: update_asFun)
qed

lemma refineFun_refineInf:
  assumes "isOK (refineFun n n\<^sub>t n\<^sub>f \<phi> )"
  shows "refineInf n n\<^sub>t n\<^sub>f"
proof -
  have 1: "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "'lv IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  have a: "IA.check_valid_formula (abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<phi> \<longrightarrow>\<^sub>f abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>t))) = Inr ()"
    "IA.check_valid_formula (abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<not>\<^sub>f \<phi> \<longrightarrow>\<^sub>f abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>f))) = Inr ()"
    using assms by (auto simp add: isOK_def check_def refineFun_def split:  sum_bind_splits)
  have b: "IA.formula (abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<not>\<^sub>f \<phi> \<longrightarrow>\<^sub>f abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>f)))"
    "IA.formula (abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<phi> \<longrightarrow>\<^sub>f abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>t)))"
    using assms by (auto simp add: isOK_def check_def refineFun_def split: sum_bind_splits if_splits)
  have c: "abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<phi> \<Longrightarrow>\<^sub>I\<^sub>A abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>t))"
    using a b by (intro 1) auto
  have d: "abstract_state.kb (asm_to_as (as_map_of_node n)) \<and>\<^sub>f \<not>\<^sub>f \<phi> \<Longrightarrow>\<^sub>I\<^sub>A abstract_state.kb (asm_to_as (as_map_of_node n\<^sub>f))"
    using a b by (intro 1) auto
  have "refineAsInf (asm_to_as (as_map_of_node n)) (asm_to_as (as_map_of_node n\<^sub>t)) (asm_to_as (as_map_of_node n\<^sub>f))"
    using assms c d
    by (intro refineAsInf.intros[where \<phi>=\<phi>])
      (auto intro!: 1 simp add: isOK_def check_def refineFun_def split: if_splits)
  then show ?thesis
    using assms
    by (auto intro: refineInf.intros simp add: renaming_of_edge'_def isOK_def check_def refineFun_def split: sum_bind_splits if_splits)
qed

lemma phi_abstract'Fun_phi_abstract':
  assumes "isOK (phi_abstract'Fun as\<^sub>1 as\<^sub>2 x ps v\<^sub>x t\<^sub>x old_b_id)"
  shows "phi_abstract' (asm_to_as as\<^sub>1) (asm_to_as as\<^sub>2) x ps v\<^sub>x t\<^sub>x old_b_id"
proof -
  have "ran (abstract_state.stack (asm_to_as as\<^sub>1)) =
       Mapping_values (stack as\<^sub>1)"
    using Mapping_values by (fastforce simp add: ran_def)
  then show ?thesis
    using assms
    by (auto simp add: isOK_def check_def phi_abstract'Fun_def lookup_None_keys vars_formula_list
        split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits option.splits
        elim!: option_to_sum.elims intro!: update_asFun phi_abstract'.intros)
qed

lemma phi_abstractFun_phi_abstract:
  assumes "isOK (phi_abstractFun as\<^sub>1 as\<^sub>2 xs ys old_b_id)"
  shows "phi_abstract (asm_to_as as\<^sub>1) (asm_to_as as\<^sub>2) xs ys old_b_id"
proof -
  have "ran (abstract_state.stack (asm_to_as as\<^sub>1)) =
       Mapping_values (stack as\<^sub>1)"
    using Mapping_values by (fastforce simp add: ran_def)
  then show ?thesis
    using assms
    apply(induction as\<^sub>1 as\<^sub>2 xs ys old_b_id rule: phi_abstractFun.induct)
    apply(auto simp add: isOK_def check_def
        split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits option.splits
        elim!: option_to_sum.elims)
    apply(intro phi_abstract.intros)
    by (auto simp add: lookup_None_keys  intro!: update_asFun phi_abstract.intros phi_abstract'Fun_phi_abstract')
qed

lemma map_sum_is_Inr:
  assumes "map_sum f g m = Inr x"
  shows "\<exists>y. m = Inr y"
  using assms by (cases m) auto

lemma branchFun_branchInf:
  assumes "isOK (branchFun n\<^sub>1 n\<^sub>2 \<phi>s)"
  shows "branchInf n\<^sub>1 n\<^sub>2"
proof -
  have [simp]: "foldr union (map (vars_term \<circ> snd) \<phi>s) {} = \<Union> (vars_term ` snd ` set \<phi>s)" for \<phi>s
    by (induction \<phi>s) (auto)
  note find_statement.simps[simp del] find_phis.simps[simp del] formula.simps[simp del] IA.implies_Language[simp del]
  have 1: "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "name IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  obtain f_id old_b_id p where f_id: "abstract_state.pos (asm_to_as (as_map_of_node n\<^sub>1)) = (f_id, old_b_id, p)"
    using prod.exhaust by metis
  have "\<exists>new_b_id . find_statement prog (pos (as_map_of_node n\<^sub>1)) = Inr (Terminator (LLVM_Syntax.Br new_b_id))"
    using assms
    by (auto simp add: branchFun_def split: stuck.splits step_splits)
  then obtain new_b_id where t: "find_statement prog (pos (as_map_of_node n\<^sub>1)) = Inr (Terminator (LLVM_Syntax.Br new_b_id))"
    by blast
  have "\<exists>phis_stats. find_phis prog f_id new_b_id = Inr phis_stats"
    using assms t f_id
    by (auto simp add: isOK_def branchFun_def
        split: sum.splits action.splits named.splits instruction.splits terminator.splits sum_bind_splits option.splits
        elim!: option_to_sum.elims intro!: map_sum_is_Inr)
  then obtain phis_stats where phis_stats: "find_phis prog f_id new_b_id = Inr phis_stats"
    by metis
  have "branchAsInf prog (asm_to_as (as_map_of_node n\<^sub>1)) (asm_to_as (as_map_of_node n\<^sub>2))"
    apply(intro branchAsInf.intros[where as\<^sub>1 = "asm_to_as (as_map_of_node n\<^sub>1)"
          and as\<^sub>2 = "asm_to_as (as_map_of_node n\<^sub>2)" and \<phi>s=\<phi>s  and new_b_id=new_b_id
          and f_id=f_id and old_b_id=old_b_id and p=p and phis_stats=phis_stats])
    (* solving the subgoals one by one with subgoal is faster thanks to parallelism *)
    subgoal
      using t by auto
    subgoal
      using f_id by auto
    subgoal
      using assms f_id t phis_stats
      by (auto simp add: check_def branchFun_def
          split: action.splits named.splits instruction.splits sum_bind_splits if_splits)
    subgoal
      using phis_stats by auto
    subgoal
      using assms phis_stats f_id t
      by (intro phi_abstractFun_phi_abstract) (auto simp add:  check_def branchFun_def
          split: action.splits named.splits instruction.splits sum_bind_splits if_splits)
    subgoal
      using assms
      by  (auto simp add: check_def branchFun_def intro!: checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def branchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    done
  then show ?thesis
    using assms
    by(intro branchInf.intros[where as\<^sub>1 = "asm_to_as (as_map_of_node n\<^sub>1)" and as\<^sub>2 = "asm_to_as (as_map_of_node n\<^sub>2)"])
      (auto simp add: renaming_of_edge'_def isOK_def check_def branchFun_def split: sum_bind_splits if_splits option.splits prod.splits)
qed

lemma condBranchFun_condBranchInf:
  assumes "isOK (condBranchFun n\<^sub>1 n\<^sub>2 \<phi>s b)"
  shows "condBranchInf n\<^sub>1 n\<^sub>2"
proof -
  have [simp]: "foldr union (map (vars_term \<circ> snd) \<phi>s) {} = \<Union> (vars_term ` snd ` set \<phi>s)" for \<phi>s
    by (induction \<phi>s) (auto)
  note find_statement.simps[simp del] find_phis.simps[simp del] formula.simps[simp del] IA.implies_Language[simp del]
  have 1: "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "name IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  obtain f_id old_b_id p where f_id: "abstract_state.pos (asm_to_as (as_map_of_node n\<^sub>1)) = (f_id, old_b_id, p)"
    using prod.exhaust by metis
  have "\<exists>c b\<^sub>t b\<^sub>f. find_statement prog (pos (as_map_of_node n\<^sub>1)) = Inr (Terminator (LLVM_Syntax.CondBr c b\<^sub>t b\<^sub>f))"
    using assms
    by (auto simp add: condBranchFun_def
        split: sum.splits stuck.splits action.splits named.splits instruction.splits terminator.splits sum_bind_splits option.splits)
  then obtain c b\<^sub>t b\<^sub>f where t: "find_statement prog (pos (as_map_of_node n\<^sub>1)) = Inr (Terminator (LLVM_Syntax.CondBr c b\<^sub>t b\<^sub>f))"
    by blast
  have "\<exists>phis_stats. find_phis prog f_id (if b then b\<^sub>t else b\<^sub>f) = Inr phis_stats"
    using assms t f_id
    by (auto simp add: isOK_def condBranchFun_def
        split: sum.splits action.splits named.splits instruction.splits terminator.splits sum_bind_splits option.splits
        elim!: option_to_sum.elims intro!: map_sum_is_Inr)
  then obtain phis_stats where phis_stats: "find_phis prog f_id (if b then b\<^sub>t else b\<^sub>f) = Inr phis_stats"
    by metis
  have "\<exists>c'. operand_value (asm_to_as (as_map_of_node n\<^sub>1)) c = Some c'"
    using assms t f_id
    by (auto simp add: isOK_def condBranchFun_def
        split: action.splits named.splits instruction.splits terminator.splits sum_bind_splits option.splits
        elim!: option_to_sum.elims)
  then obtain c' where c': "operand_value (asm_to_as (as_map_of_node n\<^sub>1)) c = Some c'"
    by metis
  have "condBranchAsInf prog (asm_to_as (as_map_of_node n\<^sub>1)) (asm_to_as (as_map_of_node n\<^sub>2))"
    apply(intro condBranchAsInf.intros[where as\<^sub>1 = "asm_to_as (as_map_of_node n\<^sub>1)"
          and as\<^sub>2 = "asm_to_as (as_map_of_node n\<^sub>2)" and \<phi>s=\<phi>s and new_b_id="if b then b\<^sub>t else b\<^sub>f"
          and b_id_true=b\<^sub>t and b_id_false=b\<^sub>f and c=c and c'=c' and b=b
          and f_id=f_id and old_b_id=old_b_id and p=p and phis_stats=phis_stats])
    (* solving the subgoals one by one with subgoal is faster thanks to parallelism *)
    subgoal
      using t by auto
    subgoal
      using assms f_id t c' by auto
    subgoal
      using assms f_id t by auto
    subgoal
      using assms phis_stats f_id t c'
      by (auto simp add: check_def condBranchFun_def split: named.splits intro!: checkFormula)
    subgoal
      using assms phis_stats f_id t c'
      by (auto simp add: check_def condBranchFun_def split: named.splits intro!: checkFormula)
    subgoal
      using assms phis_stats f_id t c'
      by (auto simp add: check_def condBranchFun_def split: named.splits)
    subgoal
      using assms phis_stats f_id t c'
      by (auto simp add: check_def condBranchFun_def split: named.splits)
    subgoal
      using assms phis_stats f_id t c' by auto
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    subgoal
      using assms phis_stats f_id t
      by (auto simp add: check_def condBranchFun_def lookup_None_keys keys_dom_lookup split: named.splits
          intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
    done
  then show ?thesis
    using assms
    by(intro condBranchInf.intros[where as\<^sub>1 = "asm_to_as (as_map_of_node n\<^sub>1)" and as\<^sub>2 = "asm_to_as (as_map_of_node n\<^sub>2)"])
      (auto simp add: renaming_of_edge'_def isOK_def check_def condBranchFun_def split: sum_bind_splits if_splits option.splits prod.splits)
qed

lemma icmpFun_icmpInf:
  assumes "isOK (icmpFun n\<^sub>1 n\<^sub>2 v\<^sub>n b)"
  shows "icmpInf n\<^sub>1 n\<^sub>2"
proof -
  obtain n p o\<^sub>1 o\<^sub>2 where
    "find_statement prog (abstract_state_mapping.pos (as_map_of_node n\<^sub>1)) =
          Inr (Instruction (Assignment n (LLVM_Syntax.Icmp p o\<^sub>1 o\<^sub>2)))"
    using assms by (auto simp add: icmpFun_def split: stuck.splits step_splits)
  then have "icmpAsInf prog (asm_to_as (as_map_of_node n\<^sub>1)) (asm_to_as (as_map_of_node n\<^sub>2)) "
    using assms
    apply(auto simp add: icmpFun_def isOK_def check_def
    split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
    elim!: option_to_sum.elims)
    by (intro icmpAsInf.intros[where b=b and o\<^sub>1=o\<^sub>1 and o\<^sub>2=o\<^sub>2],
        auto intro!: checkFormula update_asFun simp del: IA.implies_Language)+
  then show ?thesis
    using assms
    apply(intro  icmpInf.intros[where as\<^sub>1 = "asm_to_as (as_map_of_node n\<^sub>1)" and as\<^sub>2 = "asm_to_as (as_map_of_node n\<^sub>2)"])
    subgoal
      by  ( auto intro!:  icmpInf.intros simp add: icmpFun_def isOK_def check_def
          split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
          elim!: option_to_sum.elims)
    subgoal
      by  ( auto intro!:  icmpInf.intros simp add: icmpFun_def isOK_def check_def
          split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
          elim!: option_to_sum.elims)
    subgoal
      by  ( auto intro!:  icmpInf.intros simp add: icmpFun_def isOK_def check_def
          split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
          elim!: option_to_sum.elims)
    subgoal
      by  (auto intro!:  icmpInf.intros simp add: icmpFun_def renaming_of_edge'_def)
    subgoal
      by  (auto simp add: icmpFun_def split: sum_bind_splits)
    subgoal
      by  (auto simp add: icmpFun_def split: sum_bind_splits)
    subgoal
      by  (auto simp add: icmpFun_def split: sum_bind_splits)
    done
qed


lemma returnFun_returnInf:
  assumes "isOK (returnFun n\<^sub>1)"
  shows "returnInf n\<^sub>1"
proof -
  obtain op t where "find_statement prog (pos (as_map_of_node n\<^sub>1)) = Inr (Terminator (Ret (Some op)))"
    using assms
    by (auto simp add: isOK_def check_def returnFun_def simp del: find_statement.simps find_phis.simps formula.simps
        split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits option.splits
        prod.splits terminator.splits stuck.splits
        elim!: option_to_sum.elims)
  then show ?thesis
    using assms
    apply(auto simp add: returnFun_def isOK_def check_def
        split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
        elim!: option_to_sum.elims)
     apply(intro returnInf.intros[of "asm_to_as (as_map_of_node n\<^sub>1)"])
    by (auto intro!: checkFormula update_asFun simp del: IA.implies_Language)
qed

end

context graph_exec'
begin

(* TODO: move to Misc_Aux *)
lemma isOK_map_sum:
  assumes "isOK (map_sum e f m)"
  shows "isOK m"
  using assms by (cases m) auto

lemma closedGraphFun':
  assumes  "isOK closedGraphFun" "n \<in> nodes"
  shows "isOK (option_to_sum (Mapping.lookup edge n) ((showsl STR ''No edge found for node: '' \<circ>\<circ> showsl) n) \<bind> checkEdge' n)"
proof -
  have a: "nodes = set (map fst (nodes_as seg))"
    using assms unfolding closedGraphFun_def by (auto)
  show ?thesis
    by (rule sequence_isOK[of closedGraphFun'])
       (use assms in \<open>auto dest!: isOK_map_sum  simp add: collectErrorMessages_sequence a closedGraphFun_def closedGraphFun'_def\<close>)
qed

lemmas seg_fun_inf = evalFun_evalInf genFun_genInf refineFun_refineInf
         branchFun_branchInf condBranchFun_condBranchInf
         icmpFun_icmpInf returnFun_returnInf evalExternalFun_evalExternalInf

lemma valid_edge_fun_intros:
  "isOK (evalFun n n' v\<^sub>n) \<Longrightarrow> valid_edge n"
  "isOK (genFun n n') \<Longrightarrow> valid_edge n"
  "isOK (refineFun n n\<^sub>t n\<^sub>f \<phi>) \<Longrightarrow> valid_edge n"
  "isOK (branchFun n n' \<phi>s) \<Longrightarrow> valid_edge n"
  "isOK (condBranchFun n n' \<phi>s b) \<Longrightarrow> valid_edge n"
  "isOK (icmpFun n n' v\<^sub>n b) \<Longrightarrow> valid_edge n"
  "isOK (returnFun n) \<Longrightarrow> valid_edge n"
  "isOK (evalExternalFun n n' v\<^sub>n) \<Longrightarrow> valid_edge n"
  by (auto intro: valid_edge.intros seg_fun_inf)

lemma closedGraphFun:
  assumes "isOK (closedGraphFun)"
  shows "seg_represents"
proof -
  let ?f = "(\<lambda>n. option_to_sum (Mapping.lookup edge n) ((showsl STR ''No edge found for node: '' \<circ>\<circ> showsl) n) \<bind> checkEdge' n)"
  have "valid_edge n" if "Mapping.lookup local.edge n = Some e" "isOK (checkEdge' n e)" for n e
    using that by (cases e) (auto dest!: isOK_map_sum
        simp add:  choice_collect_error_messages_def checkEdge'_def
        intro: valid_edge_fun_intros isOK_map_sum)
  then have "valid_edge n" if "isOK (?f n)" for n
    using that
    by(cases "Mapping.lookup edge n")
      (auto split: sum.splits simp add: checkEdge'_def elim!: checkEdge.elims)
  then show ?thesis
    using assms closedGraphFun' unfolding seg_represents_def closedGraphFun_def
    by (auto)
qed

end

unbundle no_IA_formula_notation

end