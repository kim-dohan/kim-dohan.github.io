theory Inference_Rules_Soundness
  imports Inference_Rules
"HOL-ex.Sketch_and_Explore"
begin


lemma (in ll_mem_funs_extra) evalAsInf_represents:
  assumes
    "evalAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  (* I choose this format for the lemmas, so that the lemma namespace doesn't get too crowded *)
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: evalAsInf.induct)
    case (1 n binop o\<^sub>1 o\<^sub>2 l\<^sub>1 te\<^sub>1 l\<^sub>2 te\<^sub>2 \<phi> v\<^sub>n)
    note u = `update_as_var as\<^sub>1 as\<^sub>2 n (IntType l\<^sub>1) v\<^sub>n \<phi>`
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    obtain i\<^sub>1 where i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>1 = IA.Int i\<^sub>1"
      using \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>1 = Some (IntType l\<^sub>1, te\<^sub>1)\<close> v IA.assignment_eval_int[of v\<^sub>1]
      unfolding represents_frame.simps
      by (cases o\<^sub>1)
        (fastforce simp add: operand_value_cases same_stack_names.simps valid_var_mapping.simps
          split: llvm_constant.splits)+
    obtain i\<^sub>2 where i\<^sub>2: "IA.eval te\<^sub>2 v\<^sub>1 = IA.Int i\<^sub>2"
      using \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)\<close> v IA.assignment_eval_int[of v\<^sub>1]
      unfolding represents_frame.simps
      by (cases o\<^sub>2)
        (fastforce simp add: operand_value_cases same_stack_names.simps valid_var_mapping.simps
          split: llvm_constant.splits)+
    note a1 = operand_value_vvm_ssn[OF \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>1 = Some (IntType l\<^sub>1, te\<^sub>1)\<close>]
    note a2 = operand_value_vvm_ssn[OF \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)\<close>]
    have o\<^sub>1: "operand_value o\<^sub>1 = Inr (IntegerValue l\<^sub>1 i\<^sub>1)" "operand_value o\<^sub>2 = Inr (IntegerValue l\<^sub>1 i\<^sub>2)"
      using v 1 i\<^sub>1 i\<^sub>2 a1 a2
      unfolding represents_frame.simps type_int_to_stack_value_def
      by (fastforce)+
    define s\<^sub>2 where
      "s\<^sub>2 = Mapping.update n (IntegerValue l\<^sub>1 (binop_instruction binop i\<^sub>1 i\<^sub>2)) (frame.stack f\<^sub>1)"
    define f\<^sub>2 where "f\<^sub>2 = update_pos (\<lambda>_. (fn, bn, Suc p)) (LLVM_State.update_stack (\<lambda>_. s\<^sub>2) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2 # fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using o\<^sub>1 cs\<^sub>1 1 p' p by (auto simp add: cs\<^sub>2_def f\<^sub>2_def s\<^sub>2_def)
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1((v\<^sub>n, IA.IntT) := IA.Int (binop_instruction binop i\<^sub>1 i\<^sub>2))"
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have v\<^sub>2: "v\<^sub>2 (v\<^sub>n, IA.IntT) = IA.Int (binop_instruction binop i\<^sub>1 i\<^sub>2)"
        unfolding v\<^sub>2_def by simp
      have [simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have v\<^sub>2_i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>2 = IA.Int i\<^sub>1" "IA.eval te\<^sub>2 v\<^sub>2 = IA.Int i\<^sub>2"
        using 1 i\<^sub>1 i\<^sub>2 unfolding v\<^sub>2_def update_as_var.simps
        by (auto simp add: IA.eval_with_fresh_var[OF operand_value_fresh])
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
      proof -
        have "(v\<^sub>n, IA.IntT) \<notin> vars_formula (kb as\<^sub>1)"
          using u by (auto simp add: all_sym_vars_def update_as_var.simps)
        then show ?thesis
          using u v by (auto simp add: represents_frame.simps v\<^sub>2_def)
      qed
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A \<phi>"
        unfolding `\<phi> = encode_binop_formula binop v\<^sub>n te\<^sub>1 te\<^sub>2` by (cases binop) (auto simp add: i\<^sub>1 i\<^sub>2 v\<^sub>2_i\<^sub>1 v\<^sub>2)
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        apply(rule IA.impliesD[of "kb as\<^sub>1 \<and>\<^sub>f \<phi>"])
        using update_as_var.simps u apply(metis)
        using represents_frame.simps by (auto)
      have a: "same_stack_names s\<^sub>2 (abstract_state.stack as\<^sub>2)"
        using v unfolding represents_frame.simps s\<^sub>2_def
        by (intro ssn_update[OF u, of "frame.stack f\<^sub>1"]) auto
      have x: "\<forall>lv\<in>all_sym_vars as\<^sub>1. \<forall>ty. v\<^sub>1 (lv, ty) = v\<^sub>2 (lv, ty)"
        using u unfolding update_as_var.simps by (auto simp add: v\<^sub>2_def)
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>2) v\<^sub>2"
        using x v 1 unfolding represents_frame.simps f\<^sub>2_def update_as_var.simps 
        by(auto intro:  valid_mem_as_mem_unchanged[where v\<^sub>1=v\<^sub>1])
      have vvm: "valid_var_mapping s\<^sub>2 (abstract_state.stack as\<^sub>2) v\<^sub>2"
          unfolding s\<^sub>2_def
          apply(rule vvm_update[OF _ u, of "frame.stack f\<^sub>1" v\<^sub>1, where y="IntegerValue l\<^sub>1 (binop_instruction binop i\<^sub>1 i\<^sub>2)"])
          using represents_frame.cases v apply blast
          using v\<^sub>2_def by (auto)
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        using a vvm vm 1 by (auto simp add: f\<^sub>2_def represents_frame.simps p)

      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
        using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
        apply(rule as_as_step.intros[where v\<^sub>1'=v\<^sub>2])
        using v u x unfolding represents_frame.simps update_as_var.simps by (auto)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

(*
lemma (in IA_locale) 
  assumes "has_type x IA.IntT" "has_type y IA.IntT" "IA.satisfies v (Atom (Fun IA.EqF [x, y]))"
  shows "eval x v = eval y v"
  find_theorems IA.eval IA.has_type 
*)

lemma (in ll_mem_funs_extra) genAsInf_represents:
  assumes "genAsInf as\<^sub>1 as\<^sub>2 \<mu>" "represents_state cs as\<^sub>1 v\<^sub>1"
  shows "\<exists>v\<^sub>2. represents_state cs as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 \<mu>"
  using assms proof (induction rule: genAsInf.induct)
  case (1)
  obtain f fs where cs: "frames cs = f#fs"
    using 1 unfolding represents_state.simps by (meson list.exhaust)
  have r: "represents_frame f as\<^sub>1 v\<^sub>1"
    using 1 cs unfolding represents_state.simps by auto
  have v: "valid_var_mapping (frame.stack f) (abstract_state.stack as\<^sub>1) v\<^sub>1" "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
    "IA.assignment v\<^sub>1" "valid_mem as\<^sub>1 (mem f) v\<^sub>1"
    and pos: "frame.pos f = abstract_state.pos as\<^sub>1" and sn: "same_stack_names (frame.stack f) (abstract_state.stack as\<^sub>1)"
    using r unfolding represents_frame.simps by auto
  define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1 \<circ> (\<lambda>(v,t). (\<mu> v, t))"
  have a: "IA.assignment v\<^sub>1" "IA.assignment v\<^sub>2"
    using v(3) unfolding v\<^sub>2_def unfolding IA.assignment_def by auto
  have sn': "same_stack_names (frame.stack f) (abstract_state.stack as\<^sub>2)"
    using sn `dom (Abstract_State.stack as\<^sub>1) = dom (Abstract_State.stack as\<^sub>2)` 
    unfolding same_stack_names.simps by (blast)
  have b: "\<lbrakk>te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = IA.Int (stack_value_to_int y) \<and> t = ll_typeof y"
    if a: "Mapping.lookup (frame.stack f) n = Some y" "abstract_state.stack as\<^sub>2 n = Some (t, te\<^sub>2)"
    for te\<^sub>2 y t n
  proof -
    obtain te\<^sub>1 where te\<^sub>1: "abstract_state.stack as\<^sub>1 n = Some (t, te\<^sub>1)"
      "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2)"
      using 1 a by blast
    have I: "\<lbrakk>te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = \<lbrakk>rename_vars \<mu> te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1"
      by (subst IA.eval_rename_vars[of v\<^sub>2 v\<^sub>1 \<mu>]) (auto simp add: v\<^sub>2_def)
    have II: "IA.satisfies v\<^sub>1 (encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2))"
      using v te\<^sub>1 by blast
    have III: "IA.has_type (rename_vars \<mu> te\<^sub>2) IA.IntT" "IA.has_type te\<^sub>1 IA.IntT"
      using a 1 v te\<^sub>1 unfolding valid_var_mapping.simps by (fastforce)+
    have IV: "\<lbrakk>rename_vars \<mu> te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1 = \<lbrakk>te\<^sub>1\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1"
      using III II IA.to_int_iff[of v\<^sub>1] v by (auto) 
    show ?thesis
      unfolding I IV
      using te\<^sub>1 a v unfolding valid_var_mapping.simps by (auto)
  qed
  have vvm: "valid_var_mapping (frame.stack f) (abstract_state.stack as\<^sub>2) v\<^sub>2"  
    using 1 a b unfolding valid_var_mapping.simps by metis
  have kbt: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
  proof -
    have "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A map_formula (rename_vars \<mu>) (kb as\<^sub>2)"
      using v 1 a by blast
    then show ?thesis
      using a unfolding v\<^sub>2_def
      by (subst IA.satisfies_rename_vars[symmetric, where r=\<mu> and \<beta>=v\<^sub>1]) (auto)
  qed
  have aas: "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 \<mu>"
    using kbt v a by (auto intro!: as_as_step.intros simp add: v\<^sub>2_def)
  have allocs: "valid_allocs (allocs as\<^sub>2) v\<^sub>2 (mem f)"
    using 1 v
    by (intro valid_allocs.intros) (auto simp add: valid_allocs.simps v\<^sub>2_def  valid_mem.simps)
  have inits: "valid_inits (inits as\<^sub>2) v\<^sub>2 (mem f)"
    using v 1 unfolding valid_mem.simps valid_inits.simps v\<^sub>2_def
    by (fastforce)
  have b: "valid_load_with_value a t y (mem f)" if 
  a: "pointers as\<^sub>2 w = Some (t, te\<^sub>2)" "v\<^sub>2 (w, IA.IntT) = IA.Int a" "\<lbrakk>te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = IA.Int y"
for te\<^sub>2 y t a w
  proof -
    have I: "\<lbrakk>te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = \<lbrakk>rename_vars \<mu> te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1"
      by (subst IA.eval_rename_vars[of v\<^sub>2 v\<^sub>1 \<mu>]) (auto simp add: v\<^sub>2_def)
    have II: "v\<^sub>1 (\<mu> w, IA.IntT) = IA.Int a"
      using a unfolding v\<^sub>2_def by simp
    obtain te\<^sub>1 where te\<^sub>1: "abstract_state.pointers as\<^sub>1 (\<mu> w) = Some (t, te\<^sub>1)"
      "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2)"
      using II 1 a by metis
    have III: "IA.satisfies v\<^sub>1 (encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2))"
      using v te\<^sub>1 by blast
    have IV: "IA.has_type (rename_vars \<mu> te\<^sub>2) IA.IntT" "IA.has_type te\<^sub>1 IA.IntT"
      using a 1 v te\<^sub>1 unfolding valid_mem.simps valid_pointers.simps by (fastforce)+
    have V: "\<lbrakk>rename_vars \<mu> te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1 = \<lbrakk>te\<^sub>1\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1"
      using III IV IA.to_int_iff[of v\<^sub>1] v by (auto)
    show ?thesis
      using \<open>\<lbrakk>te\<^sub>2\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = IA.Int y\<close> unfolding I V
      using v unfolding valid_mem.simps valid_pointers.simps
      using te\<^sub>1 II by blast
  qed
  have pointers: "valid_pointers (pointers as\<^sub>2) v\<^sub>2 (mem f)"
    using 1 v b unfolding valid_mem.simps valid_pointers.simps by metis
  have "represents_state cs as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 \<mu>"
    using a sn' cs aas kbt vvm allocs r 1 pointers inits
    unfolding represents_state.simps represents_frame.simps valid_mem.simps by (auto)
  then show ?thesis
    by blast
qed

lemma (in ll_mem) allocAsInf_represents:
  assumes
    "allocAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: allocAsInf.induct)
    case (1 n lt o\<^sub>1 l\<^sub>1 te\<^sub>1 vub vlb \<phi>)
    note o\<^sub>1 = 1(3)[symmetric]
    note u = `update_as_var as\<^sub>1 as\<^sub>2 n (PointerType lt) vlb \<phi>`
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have kb: "IA.satisfies v\<^sub>1 (kb as\<^sub>1)" "IA.assignment v\<^sub>1"
      using v unfolding represents_frame.simps by auto
    have ht: "IA.has_type te\<^sub>1 IA.IntT"
      using v 1 unfolding represents_frame.simps valid_var_mapping.simps
      by (auto split: option.splits operand.splits llvm_constant.splits  simp add: operand_value_cases)
        metis
    have "\<exists>i\<^sub>1. IA.eval te\<^sub>1 v\<^sub>1 = IA.Int i\<^sub>1"
      using v IA.eval_types[OF _ ht] unfolding represents_frame.simps by auto
    then obtain i\<^sub>1 where i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>1 = IA.Int i\<^sub>1"
      by blast
    have some_o\<^sub>1: "Inference_Rules.operand_value as\<^sub>1 x = Some (IntType l\<^sub>1, te\<^sub>1)" if "o\<^sub>1 = Some x" for x
      using that o\<^sub>1 by (auto)
    have o\<^sub>1_i\<^sub>1: "(case o\<^sub>1 of None \<Rightarrow> Inr (IntegerValue 32 1) | Some x \<Rightarrow> local.operand_value x)
          = Inr (IntegerValue l\<^sub>1 i\<^sub>1)"
      using v o\<^sub>1 some_o\<^sub>1 1 i\<^sub>1 operand_value_vvm_ssn[OF some_o\<^sub>1]
      unfolding represents_frame.simps type_int_to_stack_value_def
      by (fastforce split: option.splits)
    have i\<^sub>1_0: "0 < i\<^sub>1"
    proof -
      have "IA.satisfies v\<^sub>1 (encode_sig IA.LessF (encode_int_const 0) te\<^sub>1)"
        using 1(5) kb by blast
      then show ?thesis
        using i\<^sub>1 by simp
    qed
    obtain lb ub mem' where mem': "alloc (mem f\<^sub>1) lt i\<^sub>1 = Inr ((lb, ub), mem')"
      using i\<^sub>1_0 S2 by fast
    define f\<^sub>2 where "f\<^sub>2 = update_pos inc_pos (LLVM_State.update_stack (Mapping.update n (Pointer lt lb)) (update_mem (\<lambda>_. mem') f\<^sub>1))"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2 # fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using cs\<^sub>1 1 v o\<^sub>1_i\<^sub>1 mem' unfolding cs\<^sub>2_def f\<^sub>2_def represents_frame.simps 
      by (auto split: prod.splits)
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1((vub, IA.IntT) := IA.Int ub, (vlb, IA.IntT) := IA.Int lb)"
    have ub: "ub = lb + len_of lt * i\<^sub>1"
      using mem' S3 by fastforce
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have v\<^sub>2: "v\<^sub>2 (vlb, IA.IntT) = IA.Int lb"
        "v\<^sub>2 (vub, IA.IntT) = IA.Int (lb + len_of lt * i\<^sub>1)"
        using 1 unfolding v\<^sub>2_def ub by (auto)
      have [simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have "(vlb, IA.IntT) \<notin> vars_term te\<^sub>1" "(vub, IA.IntT) \<notin> vars_term te\<^sub>1"
        using 1 u o\<^sub>1 operand_value_fresh unfolding update_as_var.simps by (fastforce split: option.splits)+
      then have v\<^sub>2_i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>2 = IA.Int i\<^sub>1"
        unfolding v\<^sub>2_def using i\<^sub>1 by auto
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
      proof -
        have "(vlb, IA.IntT) \<notin> vars_formula (kb as\<^sub>1)" "(vub, IA.IntT) \<notin> vars_formula (kb as\<^sub>1)"
          using 1 u by (auto simp add: all_sym_vars_def update_as_var.simps)
        then show ?thesis
          using u v by (auto simp add: represents_frame.simps v\<^sub>2_def)
      qed
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A \<phi>"
        unfolding `\<phi> =  encode_alloc vlb vub te\<^sub>1 lt` by (auto simp add: v\<^sub>2_i\<^sub>1 v\<^sub>2)
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        apply(rule IA.impliesD[of "kb as\<^sub>1 \<and>\<^sub>f \<phi>"])
        using update_as_var.simps u apply(metis)
        using represents_frame.simps by (auto)
      have a: "same_stack_names (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2)"
        using v unfolding represents_frame.simps
        by (intro ssn_update[OF u, of "frame.stack f\<^sub>1"]) (auto simp add: f\<^sub>2_def)
      have va: "valid_allocs (allocs as\<^sub>2) v\<^sub>2 (mem f\<^sub>2)"
      proof -
        have "bounds (mem f\<^sub>2) a = Some (lb', ub')"
          if a: "(lbv, ubv) \<in> allocs as\<^sub>2" "v\<^sub>2 (lbv, IA.IntT) = IA.Int lb'"
            "v\<^sub>2 (ubv, IA.IntT) = IA.Int ub'" "lb' \<le> a" "a < ub'" for lbv ubv lb' ub' a
        proof -
          have b: "lb = lb' \<and> ub = ub'" if "lb \<le> a \<and> a < ub"
          proof (cases "lbv = vlb \<and> ubv = vub")
            case True
            then show ?thesis
              using a 1 by (auto simp add: v\<^sub>2_def)
          next
            case False
            then have c: "(lbv, ubv) \<in> allocs as\<^sub>1"
              using 1 a by blast
            have d: "lbv \<noteq> vlb" "ubv \<noteq> vub" "lbv \<noteq> vub" "ubv \<noteq> vlb"
              using c 1 u unfolding update_as_var.simps all_sym_vars_def by auto
            have "bounds (mem f\<^sub>1) a = Some (lb', ub')"
              using c d a v
              unfolding v\<^sub>2_def represents_frame.simps valid_mem.simps valid_allocs.simps by (auto)
            then have False
              using mem' a S7 that by auto
            then show ?thesis
              by simp
          qed
          have c: "bounds (mem f\<^sub>1) a = Some (lb', ub')" if "a \<notin> {lb..<ub}"
          proof -
            have c: "(lbv, ubv) \<in> allocs as\<^sub>1"
              using 1 a that by (auto simp add: v\<^sub>2_def)
            have d: "lbv \<noteq> vlb" "ubv \<noteq> vub" "lbv \<noteq> vub" "ubv \<noteq> vlb"
              using c 1 u unfolding update_as_var.simps all_sym_vars_def by auto
            show ?thesis
              using c d a v
              unfolding v\<^sub>2_def represents_frame.simps valid_mem.simps valid_allocs.simps by (auto)
          qed
          show ?thesis
            apply(subst alloc_allocated_address_def[of "mem f\<^sub>1" lt i\<^sub>1 lb ub])
            using a b c mem' f\<^sub>2_def by (auto)
        qed
        then show ?thesis
          by (auto intro: valid_allocs.intros)
      qed
      have vp: "valid_pointers (pointers as\<^sub>2) v\<^sub>2 (mem f\<^sub>2)"
      proof (rule valid_pointers.intros, goal_cases case1 case2)
        case (case1 a llt x a' x')
        have a: "a \<noteq> vlb" "a \<noteq> vub"
          using 1(6) 1(11) case1 u ranI unfolding update_as_var.simps all_sym_vars_def by fastforce+
        have b: "fst ` vars_term x \<subseteq> all_sym_vars as\<^sub>1"
          using case1 unfolding all_sym_vars_def 1 by (auto) (metis img_fst prod.sel(2) ranI)
        have c: "vlb \<notin> fst ` vars_term x" "vub \<notin> fst ` vars_term x"
          using b 1(6) 1(11) case1 u ranI unfolding update_as_var.simps by auto
        then have d: "v\<^sub>2 (a, IA.IntT) = v\<^sub>1 (a, IA.IntT)"
          using a that 1 u unfolding update_as_var.simps v\<^sub>2_def all_sym_vars_def by auto
        have e: "IA.eval x v\<^sub>2 = IA.eval x v\<^sub>1"
          unfolding v\<^sub>2_def using c by fastforce
        have aa': "valid_load_with_value a' llt x' (mem f\<^sub>1)"
          using v case1 d e
          unfolding 1 represents_frame.simps valid_mem.simps valid_pointers.simps
          by (auto)
        have albub: "a' \<notin> {lb..<ub}"
          using aa' S7[OF mem'] unfolding valid_load_with_value.simps allocated_address_def
          by metis
        then have "allocated_address (mem f\<^sub>2) a'"
          using aa' albub mem' S6
          unfolding valid_load_with_value.simps allocated_address_def f\<^sub>2_def
          by (simp)
        then show ?case
          using albub mem' aa' S4[OF mem' albub] unfolding valid_load_with_value.simps f\<^sub>2_def
          by (auto)
      next
        case (case2 a lt x)
        then show ?case
          unfolding 1 using v
          by (auto simp add: valid_mem.simps valid_pointers.simps represents_frame.simps)
      qed
      have vi: "valid_inits (inits as\<^sub>2) v\<^sub>2 (mem f\<^sub>2)"
      proof (rule valid_inits.intros, goal_cases case1)
         case (case1 a ilb q t lb' q' p)
        have "ilb \<noteq> vlb" "ilb \<noteq> vub" "q \<noteq> vlb" "q \<noteq> vub"
          using 1(6) 1(12) case1 u ranI unfolding update_as_var.simps all_sym_vars_def by fastforce+
        then have a: "v\<^sub>2 (ilb, IA.IntT) = v\<^sub>1 (ilb, IA.IntT) \<and> v\<^sub>2 (q, IA.IntT) = v\<^sub>1 (q, IA.IntT)"
          using that 1 u unfolding update_as_var.simps v\<^sub>2_def all_sym_vars_def by auto
        have aa': "valid_load a t (mem f\<^sub>1)"
          using v case1 a
          unfolding 1 represents_frame.simps valid_mem.simps valid_inits.simps by metis
        then have albub: "a \<notin> {lb..<ub}"
          unfolding allocated_address_def valid_load.simps using S7 mem' by metis
        then have "allocated_address (mem f\<^sub>2) a"
          using aa' mem' S6 unfolding valid_load.simps allocated_address_def f\<^sub>2_def by (simp)
        then show ?case
          using albub mem' aa' S4[OF mem' albub] unfolding valid_load.simps f\<^sub>2_def by (auto)
      qed
      have vm: "valid_mem as\<^sub>2 mem' v\<^sub>2"
        using va vi vp unfolding valid_mem.simps f\<^sub>2_def by auto
      have vvm: "valid_var_mapping (Mapping.update n (Pointer lt lb) (frame.stack f\<^sub>1)) (abstract_state.stack as\<^sub>2) v\<^sub>2"
        apply(rule vvm_update[OF _ u, of "frame.stack f\<^sub>1" "v\<^sub>1((vub, IA.IntT) := IA.Int (lb + len_of lt * i\<^sub>1))",
              where y="Pointer lt lb"])
        subgoal
          apply(rule vvm_non_update_stack)
            defer 
            apply(simp)
          using 1 apply(blast)
          using v unfolding represents_frame.simps by simp
        using v\<^sub>2_def apply(simp add: ub)
        using v\<^sub>2_def by (auto)
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        using vm vvm 1 a  by (auto simp add: f\<^sub>2_def represents_frame.simps p' p)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
        using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
      proof -
        have "\<forall>lv\<in>all_sym_vars as\<^sub>1. \<forall>ty. v\<^sub>1 (lv, ty) = v\<^sub>2 (lv, ty)"
          using 1 u unfolding update_as_var.simps v\<^sub>2_def by auto
        then show ?thesis
          using v u 1 unfolding represents_frame.simps update_as_var.simps
          by (intro as_as_step.intros[where v\<^sub>1'=v\<^sub>2]) (auto)
      qed
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem) storeAsInf_represents:
  assumes
    "storeAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: storeAsInf.induct)
    case (1 t ov na type\<^sub>a term\<^sub>a v\<^sub>a type\<^sub>v term\<^sub>v pt)
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have kb: "IA.satisfies v\<^sub>1 (kb as\<^sub>1)" "IA.assignment v\<^sub>1"
      using v unfolding represents_frame.simps by auto
    have ht: "IA.has_type term\<^sub>v IA.IntT" "IA.has_type term\<^sub>a IA.IntT"
      using v 1 unfolding represents_frame.simps valid_var_mapping.simps
      by (auto split: option.splits operand.splits llvm_constant.splits  simp add: operand_value_cases)
        metis
    obtain i\<^sub>v where i\<^sub>v: "IA.eval term\<^sub>v v\<^sub>1 = IA.Int i\<^sub>v"
      using v IA.eval_types[OF _ ht(1)] unfolding represents_frame.simps by auto
    obtain i\<^sub>a where i\<^sub>a: "IA.eval term\<^sub>a v\<^sub>1 = IA.Int i\<^sub>a"
      using v IA.eval_types[OF _ ht(2)] unfolding represents_frame.simps by auto
    obtain x where ov: "operand_value ov = Inr x" "stack_value_to_int x = i\<^sub>v" "ll_typeof x = type\<^sub>v"
      using v 1 i\<^sub>v operand_value_vvm_ssn[of as\<^sub>1 ov type\<^sub>v term\<^sub>v f\<^sub>1 v\<^sub>1 i\<^sub>v]
      unfolding represents_frame.simps type_int_to_stack_value_def
      by (auto split: llvm_type.splits)
    have oa: "operand_value (LocalReference na) = Inr (Pointer type\<^sub>v i\<^sub>a)"
      apply(subst operand_value_vvm_ssn(1)[of _ _ type\<^sub>a])
      using 1 i\<^sub>a v unfolding represents_frame.simps type_int_to_stack_value_def
      by (auto)
    obtain v\<^sub>l\<^sub>b v\<^sub>u\<^sub>b where v\<^sub>l\<^sub>b: "(v\<^sub>l\<^sub>b, v\<^sub>u\<^sub>b) \<in> allocs as\<^sub>1"
      "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_sig IA.LeF (encode_int_var v\<^sub>l\<^sub>b) (encode_int_var v\<^sub>a)"
      "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_sig IA.LeF ((Fun (IA.SumF 2)
                     [encode_int_var v\<^sub>a, encode_int_const (len_of type\<^sub>v)])) (encode_int_var v\<^sub>u\<^sub>b)"
      using 1 unfolding proper_store.simps by auto
    define lb ub where lb_ub_def:
      "lb = IA.to_int (v\<^sub>1 (v\<^sub>l\<^sub>b, IA.IntT))" "ub = IA.to_int (v\<^sub>1 (v\<^sub>u\<^sub>b, IA.IntT))"
    then have lb_ub_alt_def: "v\<^sub>1 (v\<^sub>l\<^sub>b, IA.IntT) = IA.Int lb" "v\<^sub>1 (v\<^sub>u\<^sub>b, IA.IntT) = IA.Int ub"
      using IA.assignment_eval_to_int v unfolding represents_frame.simps by metis+
    have "v\<^sub>1 \<in> {\<alpha>. IA.assignment \<alpha> \<and> IA.to_int (\<alpha> (v\<^sub>l\<^sub>b, IA.IntT)) \<le> IA.to_int (\<alpha> (v\<^sub>a, IA.IntT))}"
      "v\<^sub>1 \<in> {\<alpha>. IA.assignment \<alpha> \<and> IA.to_int (\<alpha> (v\<^sub>a, IA.IntT)) + int (len_of type\<^sub>v) \<le> IA.to_int (\<alpha> (v\<^sub>u\<^sub>b, IA.IntT))}"
      using v v\<^sub>l\<^sub>b unfolding represents_frame.simps by (auto simp add: IA.satisfies_Language)
    then have lbub: "lb \<le> i\<^sub>a" "i\<^sub>a + int (len_of type\<^sub>v) \<le> ub"
      unfolding lb_ub_def using 1 i\<^sub>a by auto
    have i\<^sub>a_ub: "i\<^sub>a < ub"
      using lbub S1 by auto
    then have bounds_i\<^sub>a: "bounds (mem f\<^sub>1) i\<^sub>a = Some (lb, ub)"
      using v\<^sub>l\<^sub>b lbub v lb_ub_alt_def
      unfolding represents_frame.simps valid_allocs.simps valid_mem.simps by auto
    obtain mem' where mem': "store (mem f\<^sub>1) i\<^sub>a (ll_typeof x) x = Inr mem'"
      using S8 bounds_i\<^sub>a lbub i\<^sub>a_ub 1 ov by blast
    define f\<^sub>2 where "f\<^sub>2 = update_pos inc_pos (update_mem (\<lambda>_. mem') f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2#fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using cs\<^sub>1 1 v ov oa mem' unfolding represents_frame.simps cs\<^sub>2_def f\<^sub>2_def by auto
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1"
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have [simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have v\<^sub>2_kb\<^sub>1: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
        using v unfolding represents_frame.simps v\<^sub>2_def by auto
      have v\<^sub>2_kb: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        using v\<^sub>2_kb\<^sub>1 1  IA.impliesD[of "kb as\<^sub>1" "kb as\<^sub>2"] by auto
      have a: "same_stack_names (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2)"
        using v 1 unfolding represents_frame.simps f\<^sub>2_def by (auto)
      have va: "valid_allocs (allocs as\<^sub>2) v\<^sub>2 (mem f\<^sub>2)"
        apply(rule valid_allocs_mem_unchanged_intro[of "allocs as\<^sub>1" v\<^sub>1 "mem f\<^sub>1"])
        using v 1 S9 mem'
        by (auto simp add: all_sym_vars_def v\<^sub>2_def f\<^sub>2_def represents_frame.simps valid_mem.simps)
      have vvm: "valid_var_mapping (frame.stack f\<^sub>1) (abstract_state.stack as\<^sub>1) v\<^sub>2"
        using v unfolding represents_frame.simps v\<^sub>2_def by auto
      have vp: "valid_pointers (pointers as\<^sub>2) v\<^sub>2 (mem f\<^sub>2)"
      proof (rule valid_pointers.intros, goal_cases case1 case2)
        case (case1 av llt xv a' x')
        consider (a) "pt av = Some (llt, xv)" | (b) "av = v\<^sub>a"
          using case1 unfolding 1 by fastforce
        then show ?case
        proof cases
          case a
          define \<phi> where "\<phi> = (encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var v\<^sub>a, encode_int_const (len_of type\<^sub>v)]) (encode_int_var av)
                     \<or>\<^sub>f encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var av, encode_int_const (len_of llt)]) (encode_int_var v\<^sub>a))"
          have p: "(pointers as\<^sub>1) av = Some (llt, xv)" and k: "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A \<phi>"
            using a 1 unfolding \<phi>_def filter_pointers.simps by blast+
          have aa': "valid_load_with_value a' llt x' (mem f\<^sub>1)"
            using p case1 v
            unfolding represents_frame.simps valid_mem.simps valid_pointers.simps
            by (fastforce simp add: v\<^sub>2_def)
          have "IA.satisfies v\<^sub>1 \<phi>"
            using k v unfolding represents_frame.simps by blast
          then have "a' + int (len_of llt) \<le> i\<^sub>a \<or> i\<^sub>a + int (len_of (ll_typeof x)) \<le> a'"
            using 1 case1 i\<^sub>a unfolding \<phi>_def ov by (auto simp add: v\<^sub>2_def)
          then have l: "load mem' llt a' = load (mem f\<^sub>1) llt a'"
            using S10 mem' by blast
          have "allocated_address mem' a'"
            using aa' mem' S9 unfolding allocated_address_def valid_load_with_value.simps by auto
          then show ?thesis
            using l aa' unfolding f\<^sub>2_def valid_load_with_value.simps by (auto)
        next
          case b
          then have c: "llt = type\<^sub>v" "xv = term\<^sub>v" 
            using case1 unfolding 1 by auto
          have a': "a' = i\<^sub>a"
            using case1 b i\<^sub>a 1 by (auto simp add: v\<^sub>2_def all_sym_vars_def)
          have x': "stack_value_to_int x = x' \<and> ll_typeof x = llt"
            using i\<^sub>v case1 ov c by (simp add: v\<^sub>2_def)
          then have l: "load mem' llt a' = Inr x"
            using mem' a' S11  ov c by (auto)
          have "allocated_address mem' a'"
            using a' bounds_i\<^sub>a S9[OF mem'] unfolding allocated_address_def by simp
          then show ?thesis
            using x' l by (auto simp add: f\<^sub>2_def valid_load_with_value.simps)
        qed
      next
        case (case2 a lt x)
        have  "(pointers as\<^sub>1) a = Some (lt, x)" if "a \<noteq> v\<^sub>a"
          using that case2 1 by (auto simp add: filter_pointers.simps split: if_splits)
        then show ?case
          using case2 a 1 ht v
          unfolding represents_frame.simps valid_mem.simps valid_pointers.simps 
          by (auto split: if_splits)
      qed
      have vi: "valid_inits (inits as\<^sub>2) v\<^sub>2 mem'"
      proof -
        have "allocated_address mem' a \<and> (\<exists>y. load mem' t a = Inr y \<and> ll_typeof y = t)"
          if "(lb, q, t) \<in> inits as\<^sub>2" "v\<^sub>2 (lb, IA.IntT) = IA.Int lb'" "v\<^sub>2 (q, IA.IntT) = IA.Int q'"
            "a = lb' + int (len_of t) * p" "0 \<le> p" "p < q'"
          for a lb q t lb' q' p
        proof -
          have a: "(lb,q,t) \<in> inits as\<^sub>1"
            using 1 that unfolding filter_inits.simps by simp
          have b: "v\<^sub>2 (lb, IA.IntT) = v\<^sub>1 (lb, IA.IntT)" "v\<^sub>2 (q, IA.IntT) = v\<^sub>1 (q, IA.IntT)"
            using a unfolding v\<^sub>2_def by (auto simp add: all_sym_vars_def)
          have c: "valid_load a t (mem f\<^sub>1)"
            using b that a v unfolding represents_frame.simps valid_mem.simps valid_inits.simps
            by metis
          obtain y where y: "allocated_address (mem f\<^sub>1) a" "load (mem f\<^sub>1) t a = Inr y" "ll_typeof y = t"
            using c unfolding valid_load.simps by auto
          have d: "allocated_address mem' a"
            using S9 mem' y unfolding allocated_address_def by auto
          have g: "\<lbrakk>encode_int_var v\<^sub>a\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = IA.Int i\<^sub>a"
            using i\<^sub>a 1 unfolding v\<^sub>2_def by (auto simp add: all_sym_vars_def)
          define \<phi> where "\<phi> = (encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var v\<^sub>a, encode_int_const (int (len_of type\<^sub>v))]) (encode_int_var lb) \<or>\<^sub>f
      encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var lb, encode_arit IA.ProdF [encode_int_var q, encode_int_const (int (len_of t))]]) (encode_int_var v\<^sub>a))"
          have l: "IA.implies (kb as\<^sub>1) \<phi>"
            using `filter_inits (kb as\<^sub>1) (inits as\<^sub>1) (inits as\<^sub>2) term\<^sub>a type\<^sub>v` that
            unfolding 1 \<phi>_def filter_inits.simps by blast
          have f: "IA.satisfies v\<^sub>2 \<phi>"
            using l v\<^sub>2_kb\<^sub>1 by fastforce
          have h: "lb' + int (len_of t) * q' \<le> i\<^sub>a \<or> i\<^sub>a + int (len_of type\<^sub>v) \<le> lb'"
            using f g that by (auto simp add: ac_simps \<phi>_def)
          have k: "p + 1 \<le> q'"
            using that by auto
          have j: "lb' \<le> a \<and> lb' + int (len_of t) * (p + 1) \<le> lb' + int (len_of t) * q'"
            using k that by (cases "len_of t = 0") (auto)
          have i: "a + int (len_of t) \<le> i\<^sub>a \<or> i\<^sub>a + int (len_of type\<^sub>v) \<le> a"
            using h j unfolding that by (auto simp add: algebra_simps)
          have e: "load mem' t a = Inr y"
            using S10 mem' ov i y by (auto)
          show ?thesis
            using d e y by auto
        qed
        then show ?thesis
          by (auto intro: valid_inits.intros simp add: valid_load.simps)
      qed
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        apply(rule)
        using v 1 a va vp v\<^sub>2_kb vvm vi
        by (auto simp add: f\<^sub>2_def represents_frame.simps valid_mem.simps)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
        using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1  unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
        apply(rule as_as_step.intros[where v\<^sub>1'=v\<^sub>2])
        using 1 v v\<^sub>2_kb v\<^sub>2_kb\<^sub>1 unfolding represents_frame.simps
         by (auto simp add: v\<^sub>2_def)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem) loadAsInf_represents:
  assumes
    "loadAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  (* I choose this format for the lemmas, so that the lemma namespace doesn't get too crowded *)
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: loadAsInf.induct)
    case (1 n t\<^sub>1 na t\<^sub>2 term\<^sub>p v\<^sub>p' t\<^sub>3 term\<^sub>v)
    note u =  \<open>update_as_term as\<^sub>1 as\<^sub>2 n t\<^sub>1 term\<^sub>v True\<^sub>f\<close>
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have vp: "valid_pointers (pointers as\<^sub>1) v\<^sub>1 (mem f\<^sub>1)"
      using v unfolding represents_frame.simps valid_mem.simps by auto
    have ht: "IA.has_type term\<^sub>p IA.IntT" "IA.has_type term\<^sub>v IA.IntT"
      using v 1
      unfolding represents_frame.simps valid_var_mapping.simps valid_mem.simps valid_pointers.simps
      by (auto split: option.splits operand.splits llvm_constant.splits  simp add: operand_value_cases)
        metis
    obtain i\<^sub>a where i\<^sub>a: "IA.eval term\<^sub>p v\<^sub>1 = IA.Int i\<^sub>a"
      using v IA.eval_types[OF _ ht(1)] unfolding represents_frame.simps by auto
    then have ov: "operand_value (LocalReference na) = Inr (Pointer t\<^sub>1 i\<^sub>a)"
      apply(subst operand_value_vvm_ssn)
      using 1 i\<^sub>a v 
      unfolding represents_frame.simps type_int_to_stack_value_def
      by auto
    have v\<^sub>p'_i\<^sub>a: "IA.eval (encode_int_var v\<^sub>p') v\<^sub>1 = IA.Int i\<^sub>a"
    proof -
      have "IA.satisfies v\<^sub>1 (encode_eq term\<^sub>p (encode_int_var v\<^sub>p'))"
        using 1 v unfolding represents_frame.simps by blast
      then show ?thesis
        using i\<^sub>a v IA.assignment_eval_to_int unfolding represents_frame.simps by fastforce
    qed
    obtain i\<^sub>v where i\<^sub>v: "IA.eval term\<^sub>v v\<^sub>1 = IA.Int i\<^sub>v"
      using v IA.eval_types[OF _ ht(2)] unfolding represents_frame.simps by auto
    have vlv: "valid_load_with_value i\<^sub>a t\<^sub>1 i\<^sub>v (mem f\<^sub>1)"
      using vp unfolding valid_pointers.simps using 1 v\<^sub>p'_i\<^sub>a i\<^sub>v by fastforce
    obtain y where y: "allocated_address (mem f\<^sub>1) i\<^sub>a"
       "load (mem f\<^sub>1) t\<^sub>1 i\<^sub>a = Inr y \<and> stack_value_to_int y = i\<^sub>v \<and> ll_typeof y = t\<^sub>1"
     using vlv unfolding valid_load_with_value.simps by fastforce
    define f\<^sub>2 where
      "f\<^sub>2 = update_pos inc_pos (LLVM_State.update_stack (\<lambda>_. Mapping.update n y (frame.stack f\<^sub>1)) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2#fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using y ov  cs\<^sub>1 1 p' p by (auto simp add: cs\<^sub>2_def f\<^sub>2_def)
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1"
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have [simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
        using v unfolding v\<^sub>2_def represents_frame.simps by auto
      have v\<^sub>2_kb: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        apply(rule IA.impliesD[of "kb as\<^sub>1"])
        using v u unfolding represents_frame.simps update_as_term.simps by (auto)
      have a: "same_stack_names (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2)"
        using 1 v 
        unfolding f\<^sub>2_def represents_frame.simps same_stack_names.simps update_as_term.simps
        by auto
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>2) v\<^sub>2"
        using 1 v u unfolding v\<^sub>2_def represents_frame.simps f\<^sub>2_def
        unfolding update_as_term.simps by (auto intro: valid_mem_as_mem_unchanged)
      have p: "frame.pos f\<^sub>2 = abstract_state.pos as\<^sub>2"
        using v 1  by (auto simp add: f\<^sub>2_def represents_frame.simps)
      have vvm: "valid_var_mapping (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2) v\<^sub>2"
      proof (rule valid_var_mapping.intros, goal_cases case1 case2)
        case (case1 v pv lterm t)
        then show ?case
          using u v i\<^sub>v y unfolding represents_frame.simps valid_var_mapping.simps update_as_term.simps
          by (auto simp add: f\<^sub>2_def v\<^sub>2_def split: if_splits)
      next
        case (case2 pv lterm t)
        then show ?case
          using u v ht
          unfolding update_as_term.simps represents_frame.simps valid_var_mapping.simps v\<^sub>2_def
          by (fastforce split: if_splits)
      qed
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        using vvm p vm v\<^sub>2_kb a by (auto simp add:  represents_frame.simps)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
        using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
        using v\<^sub>2_kb v unfolding represents_frame.simps v\<^sub>2_def
        by (intro as_as_step.intros[where v\<^sub>1'=v\<^sub>1]) (auto)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem) loadAsInitsInf_represents:
  assumes
    "loadAsInitsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  (* I choose this format for the lemmas, so that the lemma namespace doesn't get too crowded *)
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: loadAsInitsInf.induct)
    case (1 n t\<^sub>1 na t\<^sub>2 term\<^sub>p lb q t pv v\<^sub>n)
    note u =  \<open>update_as_var as\<^sub>1 as\<^sub>2 n t\<^sub>1 v\<^sub>n True\<^sub>f\<close>
    define \<phi> where "\<phi> = (encode_eq term\<^sub>p (encode_arit IA.SumF [encode_int_var lb, encode_arit IA.ProdF [encode_int_var pv, encode_int_const (len_of t)]])
    \<and>\<^sub>f encode_sig IA.LessF (encode_int_var pv) (encode_int_var q) \<and>\<^sub>f encode_sig IA.LeF (encode_int_const 0) (encode_int_var pv))"
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have vi: "valid_inits (inits as\<^sub>1) v\<^sub>1 (mem f\<^sub>1)"
      using v unfolding represents_frame.simps valid_mem.simps by auto
    have ht: "IA.has_type term\<^sub>p IA.IntT"
      using v 1
      unfolding represents_frame.simps valid_var_mapping.simps
      by (auto split: option.splits operand.splits llvm_constant.splits simp add: operand_value_cases)
        metis
    obtain i\<^sub>a i\<^sub>p i\<^sub>l\<^sub>b i\<^sub>q where i\<^sub>a: "IA.eval term\<^sub>p v\<^sub>1 = IA.Int i\<^sub>a"
      and i\<^sub>p: "IA.eval (encode_int_var pv) v\<^sub>1 = IA.Int i\<^sub>p"
      and i\<^sub>l\<^sub>b: "IA.eval (encode_int_var lb) v\<^sub>1 = IA.Int i\<^sub>l\<^sub>b"
      and i\<^sub>q: "IA.eval (encode_int_var q) v\<^sub>1 = IA.Int i\<^sub>q"
      using v IA.assignment_eval_int[of v\<^sub>1] IA.eval_types[OF _ ht]
      unfolding represents_frame.simps by (fastforce)
    then have ov: "operand_value (LocalReference na) = Inr (Pointer t\<^sub>1 i\<^sub>a)"
      apply(subst operand_value_vvm_ssn)
      using 1 i\<^sub>a v 
      unfolding represents_frame.simps type_int_to_stack_value_def
      by auto
    have v\<^sub>1_\<phi>: "IA.satisfies v\<^sub>1 \<phi>"
      using 1 v unfolding \<phi>_def represents_frame.simps by blast
    have i\<^sub>a_i\<^sub>l\<^sub>b: "i\<^sub>a = i\<^sub>l\<^sub>b + len_of t * i\<^sub>p" "0 \<le> i\<^sub>p" "i\<^sub>p < i\<^sub>q"
      using v\<^sub>1_\<phi> i\<^sub>p i\<^sub>a i\<^sub>l\<^sub>b i\<^sub>q unfolding \<phi>_def by (auto)
    have y': "valid_load i\<^sub>a t\<^sub>1 (mem f\<^sub>1)"
      using vi i\<^sub>a_i\<^sub>l\<^sub>b i\<^sub>p i\<^sub>a i\<^sub>l\<^sub>b i\<^sub>q 1 unfolding valid_inits.simps by (auto)
    obtain y where y: "allocated_address (mem f\<^sub>1) i\<^sub>a" "load (mem f\<^sub>1) t\<^sub>1 i\<^sub>a = Inr y" "ll_typeof y = t\<^sub>1"
      using y' unfolding valid_load.simps by auto
    define f\<^sub>2 where
      "f\<^sub>2 = update_pos inc_pos (LLVM_State.update_stack (\<lambda>_. Mapping.update n y (frame.stack f\<^sub>1)) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2#fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using y ov  cs\<^sub>1 1 p' p by (auto simp add: cs\<^sub>2_def f\<^sub>2_def)
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1((v\<^sub>n, IA.IntT) := IA.Int (stack_value_to_int y))"
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have v\<^sub>2: "v\<^sub>2 (v\<^sub>n, IA.IntT) = IA.Int (stack_value_to_int y)"
        unfolding v\<^sub>2_def by simp
      have a_v\<^sub>2[simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have v\<^sub>2_kb\<^sub>1[simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
      proof -
        have "(v\<^sub>n, IA.IntT) \<notin> vars_formula (kb as\<^sub>1)"
          using u by (auto simp add: all_sym_vars_def update_as_var.simps)
        then show ?thesis
          using u v by (auto simp add: represents_frame.simps v\<^sub>2_def)
      qed
      have v\<^sub>2_kb\<^sub>2[simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        apply(rule IA.impliesD[of "kb as\<^sub>1 \<and>\<^sub>f True\<^sub>f"])
        using update_as_var.simps u \<phi>_def apply(metis)
        using represents_frame.simps by (auto)
      have a: "same_stack_names (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2)"
        using v unfolding f\<^sub>2_def represents_frame.simps
        by (intro ssn_update[OF u, of "frame.stack f\<^sub>1"]) auto
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>2) v\<^sub>2"
        using 1 v u unfolding v\<^sub>2_def represents_frame.simps f\<^sub>2_def
        unfolding update_as_var.simps by (auto intro!: valid_mem_as_mem_unchanged[of as\<^sub>1 _ _ v\<^sub>1])
      have p: "frame.pos f\<^sub>2 = abstract_state.pos as\<^sub>2"
        using v 1  by (auto simp add: f\<^sub>2_def represents_frame.simps)
      have vvm: "valid_var_mapping (frame.stack f\<^sub>2) (abstract_state.stack as\<^sub>2) v\<^sub>2"
          using 1 u v y by (intro vvm_update[of "frame.stack f\<^sub>1" as\<^sub>1 v\<^sub>1 as\<^sub>2])
           (auto simp add: \<phi>_def represents_frame.simps v\<^sub>2_def f\<^sub>2_def)
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        using vvm p vm  a by (auto simp add:  represents_frame.simps)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
        using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
        apply(rule as_as_step.intros[where v\<^sub>1'=v\<^sub>2])
        using a_v\<^sub>2 v\<^sub>2_kb\<^sub>1 v\<^sub>2_kb\<^sub>2 v u
        unfolding represents_frame.simps update_as_var.simps by (auto simp add: v\<^sub>2_def)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem_funs_extra) refineAsInf_represents:
  assumes "refineAsInf as as\<^sub>t as\<^sub>f" "represents_state cs as v"
  shows
  "represents_state cs as\<^sub>t v \<and> as_as_step as as\<^sub>t v v id
   \<or> represents_state cs as\<^sub>f v \<and> as_as_step as as\<^sub>f v v id"
using assms proof (induction rule: refineAsInf.induct)
  case (1 \<phi>)
  obtain f where fcs: "frames cs = [f]" "represents_frame f as v"
    using 1[unfolded represents_state.simps] by (cases "frames cs", auto)
  from this(2)[unfolded represents_frame.simps]
  have pos: "frame.pos f = abstract_state.pos as" and
    stack: "same_stack_names (frame.stack f) (abstract_state.stack as)" and
    ass: "IA.assignment v" and
    var: "valid_var_mapping (frame.stack f) (abstract_state.stack as) v" and
    kb:  "v \<Turnstile>\<^sub>I\<^sub>A kb as" and
    vp: "valid_mem as (mem f) v"
    by blast+
  define \<phi>' where "\<phi>' = (if IA.satisfies v \<phi> then \<phi> else \<not>\<^sub>f \<phi>)"
  define as' where "as' = (if IA.satisfies v \<phi> then as\<^sub>t else as\<^sub>f)"
  have pos': "frame.pos f = abstract_state.pos as'"
    using 1 pos unfolding as'_def unfolding refineAsInf'.simps by auto
  have \<phi>': "IA.satisfies v \<phi>'"
    unfolding \<phi>'_def by auto
  have id':  "refineMapping (abstract_state.stack as) (abstract_state.stack as') (kb as \<and>\<^sub>f \<phi>')"
  "refineMapping (abstract_state.pointers as) (abstract_state.pointers as') (kb as \<and>\<^sub>f \<phi>')"
   "dom (abstract_state.stack as') = dom (abstract_state.stack as)"
   "dom (abstract_state.pointers as') \<subseteq> dom (abstract_state.pointers as)"
   "inits as' = inits as"
   "allocs as' = allocs as"
    using 1 unfolding as'_def \<phi>'_def refineAsInf'.simps by (auto)
  have kb': "IA.satisfies v (kb as')"
    apply(rule IA.impliesD[of "kb as \<and>\<^sub>f \<phi>'"])
    using 1 kb ass unfolding \<phi>'_def as'_def refineAsInf'.simps by (auto)
  have stack': "same_stack_names (frame.stack f) (abstract_state.stack as')"
    using id' stack unfolding same_stack_names.simps by blast
  have var': "valid_var_mapping (frame.stack f) (abstract_state.stack as') v"
  proof (intro valid_var_mapping.intros, goal_cases)
    case (1 sv pv lterm t)
    have b: "\<exists>x y. abstract_state.stack as pv = Some (x,y)"
      using 1 id'(3) unfolding refineMapping.simps by fast
    obtain x y where x: "abstract_state.stack as pv = Some (x,y)"
      using b by blast
    have xt: "x = t"
      using 1 id' x unfolding refineMapping.simps by fastforce
    have ylterm: "IA.satisfies v (encode_eq y lterm)"
      apply(rule IA.impliesD[of " kb as \<and>\<^sub>f \<phi>'"])
      using 1 id' xt x \<phi>' kb ass unfolding refineMapping.simps
      by (auto)
    have a: "IA.has_type lterm IA.IntT"
      using 1 id' xt x \<phi>' kb ass unfolding refineMapping.simps
      by (auto)
    have "\<lbrakk>y\<rbrakk>\<^sub>I\<^sub>A v = IA.Int (stack_value_to_int sv) \<and> x = ll_typeof sv"
      using 1 x var unfolding valid_var_mapping.simps by auto
    then show ?case
      using a ass ylterm xt by (auto simp add: IA.IA_exp_to_tpoly)
  next
    case (2 pv lterm t)
    have b: "\<exists>x y. abstract_state.stack as pv = Some (x,y)"
      using 2 id'(3) unfolding refineMapping.simps by fast
    obtain x y where x: "abstract_state.stack as pv = Some (x,y)"
      using b by blast
    have xt: "x = t"
      using 2 id' x unfolding refineMapping.simps by fastforce
    show ?case
      using 2 id' xt x unfolding refineMapping.simps by fastforce
  qed          
  have vp': "valid_pointers (abstract_state.pointers as') v (mem f)"
  proof (intro valid_pointers.intros, goal_cases case1 case2)
    case (case1 a lt x a' x')
    obtain k l where x: "abstract_state.pointers as a = Some (k,l)"
      using 1 case1 id' by auto
    have xt: "k = lt"
      using case1 id' x unfolding refineMapping.simps by fastforce
    have ylterm: "IA.satisfies v (encode_eq l x)"
      apply(rule IA.impliesD[of "kb as \<and>\<^sub>f \<phi>'"])
      using case1 id' xt x \<phi>' kb ass unfolding refineMapping.simps
      by (auto simp del: encode_eq.simps IA.implies_Language)
    have a: "lt = k \<and> IA.has_type x IA.IntT \<and> kb as \<and>\<^sub>f \<phi>' \<Longrightarrow>\<^sub>I\<^sub>A encode_eq l x"
      using case1 x id' unfolding refineMapping.simps by blast
    have b: "IA.has_type l IA.IntT"
      using x vp unfolding valid_mem.simps valid_pointers.simps by blast
    have c: "\<lbrakk>l\<rbrakk>\<^sub>I\<^sub>A v = \<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v"
      using ylterm ass a b by (auto simp add: IA.to_int_iff)
    show ?case
      using vp x case1 c xt unfolding valid_mem.simps valid_pointers.simps by (auto)
  next
    case (case2 a lt x)
    obtain k l where x: "abstract_state.pointers as a = Some (k,l)"
      using 1 case2 id' by auto
    have xt: "k = lt"
      using case2 id' x unfolding refineMapping.simps by fastforce
    show ?case
      using case2 x id' unfolding refineMapping.simps by blast
  qed
  have viva': "valid_inits (inits as') v (mem f)" "valid_allocs (allocs as') v (mem f)"
    using vp unfolding valid_mem.simps id' by auto
  have repr': "represents_frame f as' v"
    using pos' fcs id' kb' var' ass stack' viva' vp'
    unfolding represents_frame.simps as_mem_unchanged.simps valid_mem.simps
    by (auto)
  have as: "as_as_step as as' v v id"
    unfolding  fcs list.sel using ass kb kb' 1
    by (auto simp: id' intro!: as_as_step.intros)
  show ?case
    using as repr' fcs unfolding as'_def represents_state.simps
    by (auto split: if_splits)
qed

lemma (in ll_mem_funs_extra) branchAsInf_represents:
  assumes
    "branchAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: branchAsInf.induct)
    case (1 new_b_id f_id old_b_id p phis_stats \<phi>s)
    note phi = \<open>phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id\<close>
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (meson list.exhaust)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have "isOK (compute_phis old_b_id phis_stats)"
      using phi proof (induction phis_stats arbitrary: \<phi>s)
      case (Cons p phis_stats)
      obtain n ps where p: "p = (n,ps)"
        by fastforce
      obtain  type_term t\<^sub>x \<phi>s' where \<phi>s_def: "\<phi>s = (type_term, t\<^sub>x)#\<phi>s'"
        using Cons(2) by (rule phi_abstract.cases) (auto)
      have pa': "phi_abstract' as\<^sub>1 as\<^sub>2 n ps type_term t\<^sub>x old_b_id"
        using Cons(2) p \<phi>s_def apply - by (rule phi_abstract.cases) (auto)
      have pa: "phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s' old_b_id"
        using Cons(2) \<phi>s_def apply - by (rule phi_abstract.cases) (auto)
      obtain x where x: "LLVM_Step.option_to_sum (phi_bid old_b_id ps) err = Inr x"
        "Inference_Rules.operand_value as\<^sub>1 x = Some (type_term, t\<^sub>x)" for err :: stuck
        using pa' unfolding phi_abstract'.simps option_to_sum_def by auto
      have sv: "\<exists>sv. operand_value x = Inr sv"
      proof (cases x)
        case (LocalReference x1)
        then show ?thesis
          using x v unfolding represents_frame.simps same_stack_names.simps
          by (auto split: option.splits simp add:  option_to_sum_def)
      qed (auto)
      show ?case
        using Cons p x sv pa by (auto)
    qed (auto)
    then obtain ps where ps: "compute_phis old_b_id phis_stats = Inr ps"
      by blast
    define s\<^sub>2 where "s\<^sub>2 = foldr (\<lambda>(x, y). Mapping.update x y) ps (frame.stack f\<^sub>1)"
    define f\<^sub>2 where
      "f\<^sub>2 = update_pos (\<lambda>_. (f_id, new_b_id, length phis_stats)) (LLVM_State.update_stack (\<lambda>_. s\<^sub>2) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2#fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using 1 cs\<^sub>1 v ps
      by (auto simp add: represents_frame.simps terminate_frame_def c_pos_def cs\<^sub>2_def f\<^sub>2_def s\<^sub>2_def)
    have s': "Mapping.lookup s\<^sub>2 x = (case map_of ps x of None \<Rightarrow> Mapping.lookup (frame.stack f\<^sub>1) x | y \<Rightarrow> y)" for x
      unfolding s\<^sub>2_def by (induction ps) (auto)
    have d1: "map fst ps = map fst phis_stats"
      using ps by (induction old_b_id phis_stats arbitrary: ps rule: compute_phis.induct )
        (fastforce split: Option.bind_splits sum_bind_splits)+
    then have d: "fst ` set ps = fst ` set phis_stats"
      by (metis list.set_map)
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>1 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      note dom = \<open>dom (abstract_state.stack as\<^sub>2) = dom (abstract_state.stack as\<^sub>1) \<union> fst ` set phis_stats\<close>
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have a: "same_stack_names s\<^sub>2 (abstract_state.stack as\<^sub>2)"
      proof -
        have a: "\<exists>a b. abstract_state.stack as\<^sub>2 pv = Some (a, b)"
          if "map_of ps pv = None" and "Mapping.lookup (frame.stack f\<^sub>1) pv = Some y" for pv y
        proof -
          have "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using that v unfolding represents_frame.simps same_stack_names.simps by auto
          then have "pv \<in> dom (abstract_state.stack as\<^sub>2)"
            using 1 by blast
          then show ?thesis
            by auto
        qed
        have b: "\<exists>y. Mapping.lookup (frame.stack f\<^sub>1) pv = Some y"
          if "map_of ps pv = None" and "abstract_state.stack as\<^sub>2 pv = Some (a, b)"for pv a b
        proof -
          have "pv \<notin> fst ` set phis_stats"
            using that dom d map_of_eq_None_iff by metis
          then have "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using 1 that by blast
          then show ?thesis
            using v unfolding represents_frame.simps same_stack_names.simps by blast
        qed
        have c: "\<exists>a b. abstract_state.stack as\<^sub>2 pv = Some (a, b)"
          if "map_of ps pv = Some x2" for pv x2
        proof -
          have "pv \<in> fst ` set phis_stats"
            using that dom d map_of_eq_None_iff by (metis domI domIff)
          then have "pv \<in> dom (abstract_state.stack as\<^sub>2)"
            using 1 that by blast
          then show ?thesis
            by auto
        qed
        show ?thesis
          apply(rule)
          unfolding  s' using a b c by (auto intro: same_stack_names.intros split: option.splits)
      qed
      have c: "valid_var_mapping s\<^sub>2 (abstract_state.stack as\<^sub>2) v\<^sub>1"
      proof -
        have a: "IA.eval lv v\<^sub>1 = IA.Int (stack_value_to_int v) \<and> t = ll_typeof v"
          if i: "Mapping.lookup s\<^sub>2 pv = Some v" "abstract_state.stack as\<^sub>2 pv = Some (t, lv)" for lv pv v t
        proof (cases "map_of ps pv")
          case None
          have a: "pv \<notin> fst ` set phis_stats"
            using None d map_of_eq_None_iff by metis
          have b: "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using dom i a by blast
          have c: "abstract_state.stack as\<^sub>2 pv = abstract_state.stack as\<^sub>1 pv"
            using 1 b a by blast
          have d: "Mapping.lookup s\<^sub>2 pv = Mapping.lookup (frame.stack f\<^sub>1) pv"
            using None i unfolding s' by (auto)
          show ?thesis
            using i v unfolding c d unfolding represents_frame.simps valid_var_mapping.simps
            by blast
        next
          case (Some a)
          have av: "v = a"
            using Some i unfolding s' by auto
          have a: "pv \<in> fst ` set phis_stats"
            using Some d map_of_eq_None_iff[of ps pv] by auto
          obtain phi_assignments where pa: "(pv, phi_assignments) \<in> set phis_stats"
            using a by auto
          have b: "\<exists>type_term term\<^sub>x. phi_abstract' as\<^sub>1 as\<^sub>2 pv phi_assignments type_term term\<^sub>x old_b_id"
            using phi pa by (induction rule: phi_abstract.induct) (auto)
          obtain y\<^sub>x where y\<^sub>x: "small_step.phi_bid old_b_id phi_assignments = Some y\<^sub>x"
            "Inference_Rules.operand_value as\<^sub>1 y\<^sub>x = Some (t, lv)"
            using i b unfolding phi_abstract'.simps by auto
          have d: "(pv, v) \<in> set ps"
            using Some av by (simp add: map_of_SomeD)
          have e: "distinct (map fst ps)"
            using 1 d1 by simp
          have f: "local.operand_value y\<^sub>x = Inr v"
            using ps d y\<^sub>x(1) pa e `distinct (map fst phis_stats)`
            proof (induction old_b_id phis_stats arbitrary: pv v ps phi_assignments rule: compute_phis.induct)
              case (1 old_b_id a psss as)
              show ?case
              proof (cases "a = pv")
                case True
                have "psss = phi_assignments"
                  using 1 True by (metis distinct_map_fstD list.set_intros(1))
                then show ?thesis
                  using True 1 by (auto simp add: option_to_sum_def  split: sum_bind_splits)
              next
                case False
                then show ?thesis
                  using 1 by (auto split: sum_bind_splits)
              qed
            qed (auto)
          show ?thesis
            using v y\<^sub>x f unfolding represents_frame.simps valid_var_mapping.simps
            by (auto simp add: option_to_sum_def operand_value_cases
                split: operand.splits llvm_constant.splits option.splits)
        qed
        have b: "IA.has_type lterm IA.IntT" if i: "abstract_state.stack as\<^sub>2 pv = Some (t, lterm)"
          for pv t lterm
        proof (cases "map_of ps pv")
          case None
          have a: "pv \<notin> fst ` set phis_stats"
            using None d map_of_eq_None_iff by metis
          have b: "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using dom i a by blast
          have c: "abstract_state.stack as\<^sub>2 pv = abstract_state.stack as\<^sub>1 pv"
            using 1 b a by blast
          then show ?thesis
            using v i unfolding represents_frame.simps valid_var_mapping.simps by metis
        next
          case (Some a)
          have a: "pv \<in> fst ` set phis_stats"
            using Some d map_of_eq_None_iff[of ps pv] by auto
          obtain phi_assignments where pa: "(pv, phi_assignments) \<in> set phis_stats"
            using a by auto
          have b: "\<exists>type_term term\<^sub>x. phi_abstract' as\<^sub>1 as\<^sub>2 pv phi_assignments type_term term\<^sub>x old_b_id"
            using phi pa by (induction rule: phi_abstract.induct) (auto)
          obtain y\<^sub>x where y\<^sub>x: "small_step.phi_bid old_b_id phi_assignments = Some y\<^sub>x"
            "Inference_Rules.operand_value as\<^sub>1 y\<^sub>x = Some (t, lterm)"
            using i b unfolding phi_abstract'.simps by auto
          then show ?thesis
            using v unfolding represents_frame.simps valid_var_mapping.simps
            by (fastforce simp add: operand_value_cases split: operand.splits llvm_constant.splits) 
        qed
        show ?thesis
          using a b by (intro valid_var_mapping.intros) (auto)
      qed
      have d: "valid_mem as\<^sub>2 (mem f\<^sub>1) v\<^sub>1"
        apply(rule valid_mem_as_mem_unchanged[of as\<^sub>1 as\<^sub>2 _ v\<^sub>1])
        using v 1 unfolding represents_frame.simps by (auto)
      have f: "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        using 1 v  IA.impliesD[of "kb as\<^sub>1" "kb as\<^sub>2"] unfolding represents_frame.simps
        by blast
      have g: "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id"
        apply(rule as_as_step.intros[of _ v\<^sub>1]) 
        using v f by (fastforce simp add: represents_frame.simps)+
      show ?thesis
        using 1
        unfolding represents_state.simps represents_frame.simps cs\<^sub>2' cs\<^sub>2_def f\<^sub>2_def
        using cs\<^sub>1 a c d f g by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem_funs_extra) condBranchAsInf_represents:
  assumes
    "condBranchAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: condBranchAsInf.induct)
    case (1 c b_id_true b_id_false c' new_b_id b f_id old_b_id p phis_stats \<phi>s)
    note phi = \<open>phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id\<close>
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (meson list.exhaust)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have "isOK (compute_phis old_b_id phis_stats)"
      using phi proof (induction phis_stats arbitrary: \<phi>s)
      case (Cons p phis_stats)
      obtain n ps where p: "p = (n,ps)"
        by fastforce
      obtain  type_term t\<^sub>x \<phi>s' where \<phi>s_def: "\<phi>s = (type_term, t\<^sub>x)#\<phi>s'"
        using Cons(2) by (rule phi_abstract.cases) (auto)
      have pa': "phi_abstract' as\<^sub>1 as\<^sub>2 n ps type_term t\<^sub>x old_b_id"
        using Cons(2) p \<phi>s_def apply - by (rule phi_abstract.cases) (auto)
      have pa: "phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s' old_b_id"
        using Cons(2) \<phi>s_def apply - by (rule phi_abstract.cases) (auto)
      obtain x where x: "LLVM_Step.option_to_sum (phi_bid old_b_id ps) err = Inr x"
        "Inference_Rules.operand_value as\<^sub>1 x = Some (type_term, t\<^sub>x)" for err :: stuck
        using pa' unfolding phi_abstract'.simps option_to_sum_def by auto
      have sv: "\<exists>sv. operand_value x = Inr sv"
      proof (cases x)
        case (LocalReference x1)
        then show ?thesis
          using x v unfolding represents_frame.simps same_stack_names.simps
          by (auto split: option.splits simp add:  option_to_sum_def)
      qed (auto)
      show ?case
        using Cons p x sv pa by (auto)
    qed (auto)
    then obtain ps where ps: "compute_phis old_b_id phis_stats = Inr ps"
      by blast
    define s\<^sub>2 where "s\<^sub>2 = foldr (\<lambda>(x, y). Mapping.update x y) ps (frame.stack f\<^sub>1)"
    define f\<^sub>2 where
      "f\<^sub>2 = update_pos (\<lambda>_. (f_id, new_b_id, length phis_stats)) (LLVM_State.update_stack (\<lambda>_. s\<^sub>2) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2#fs\<^sub>1)"
    have a1: "IA.to_int (\<lbrakk>c'\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1) = (if b then 1 else 0)"
      using IA.satisfies_Language[of v\<^sub>1] 1(4,5) v unfolding represents_frame.simps by auto
    have c: "small_step.operand_value f\<^sub>1 c = Inr (IntegerValue 1 (if b then 1 else 0))"
      apply(subst operand_value_vvm_ssn)
      using \<open>Inference_Rules.operand_value as\<^sub>1 c = Some (IntType 1, c')\<close> v a1
      unfolding represents_frame.simps type_int_to_stack_value_def 
      by auto
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using 1 cs\<^sub>1 v ps
      by (auto split: if_splits
          simp add: c represents_frame.simps terminate_frame_def c_pos_def cs\<^sub>2_def f\<^sub>2_def s\<^sub>2_def)
    have s': "Mapping.lookup s\<^sub>2 x = (case map_of ps x of None \<Rightarrow> Mapping.lookup (frame.stack f\<^sub>1) x | y \<Rightarrow> y)" for x
      unfolding s\<^sub>2_def by (induction ps) (auto)
    have d1: "map fst ps = map fst phis_stats"
      using ps by (induction old_b_id phis_stats arbitrary: ps rule: compute_phis.induct )
        (fastforce split: Option.bind_splits sum_bind_splits)+
    then have d: "fst ` set ps = fst ` set phis_stats"
      by (metis list.set_map)
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>1 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      note dom = \<open>dom (abstract_state.stack as\<^sub>2) = dom (abstract_state.stack as\<^sub>1) \<union> fst ` set phis_stats\<close>
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have a: "same_stack_names s\<^sub>2 (abstract_state.stack as\<^sub>2)"
      proof -
        have a: "\<exists>a b. abstract_state.stack as\<^sub>2 pv = Some (a, b)"
          if "map_of ps pv = None" and "Mapping.lookup (frame.stack f\<^sub>1) pv = Some y" for pv y
        proof -
          have "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using that v unfolding represents_frame.simps same_stack_names.simps by auto
          then have "pv \<in> dom (abstract_state.stack as\<^sub>2)"
            using 1 by blast
          then show ?thesis
            by auto
        qed
        have b: "\<exists>y. Mapping.lookup (frame.stack f\<^sub>1) pv = Some y"
          if "map_of ps pv = None" and "abstract_state.stack as\<^sub>2 pv = Some (a, b)"for pv a b
        proof -
          have "pv \<notin> fst ` set phis_stats"
            using that dom d map_of_eq_None_iff by metis
          then have "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using 1 that by blast
          then show ?thesis
            using v unfolding represents_frame.simps same_stack_names.simps by blast
        qed
        have c: "\<exists>a b. abstract_state.stack as\<^sub>2 pv = Some (a, b)"
          if "map_of ps pv = Some x2" for pv x2
        proof -
          have "pv \<in> fst ` set phis_stats"
            using that dom d map_of_eq_None_iff by (metis domI domIff)
          then have "pv \<in> dom (abstract_state.stack as\<^sub>2)"
            using 1 that by blast
          then show ?thesis
            by auto
        qed
        show ?thesis
          apply(rule)
          unfolding  s' using a b c by (auto intro: same_stack_names.intros split: option.splits)
      qed
      have c: "valid_var_mapping s\<^sub>2 (abstract_state.stack as\<^sub>2) v\<^sub>1"
      proof -
        have a: "IA.eval lv v\<^sub>1 = IA.Int (stack_value_to_int v) \<and> t = ll_typeof v"
          if i: "Mapping.lookup s\<^sub>2 pv = Some v" "abstract_state.stack as\<^sub>2 pv = Some (t, lv)" for lv pv v t
        proof (cases "map_of ps pv")
          case None
          have a: "pv \<notin> fst ` set phis_stats"
            using None d map_of_eq_None_iff by metis
          have b: "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using dom i a by blast
          have c: "abstract_state.stack as\<^sub>2 pv = abstract_state.stack as\<^sub>1 pv"
            using 1 b a by blast
          have d: "Mapping.lookup s\<^sub>2 pv = Mapping.lookup (frame.stack f\<^sub>1) pv"
            using None i unfolding s' by (auto)
          show ?thesis
            using i v unfolding c d unfolding represents_frame.simps valid_var_mapping.simps
            by blast
        next
          case (Some a)
          have av: "v = a"
            using Some i unfolding s' by auto
          have a: "pv \<in> fst ` set phis_stats"
            using Some d map_of_eq_None_iff[of ps pv] by auto
          obtain phi_assignments where pa: "(pv, phi_assignments) \<in> set phis_stats"
            using a by auto
          have b: "\<exists>type_term term\<^sub>x. phi_abstract' as\<^sub>1 as\<^sub>2 pv phi_assignments type_term term\<^sub>x old_b_id"
            using phi pa by (induction rule: phi_abstract.induct) (auto)
          obtain y\<^sub>x where y\<^sub>x: "small_step.phi_bid old_b_id phi_assignments = Some y\<^sub>x"
            "Inference_Rules.operand_value as\<^sub>1 y\<^sub>x = Some (t, lv)"
            using i b unfolding phi_abstract'.simps by auto
          have d: "(pv, v) \<in> set ps"
            using Some av by (simp add: map_of_SomeD)
          have e: "distinct (map fst ps)"
            using 1 d1 by simp
          have f: "local.operand_value y\<^sub>x = Inr v"
            using ps d y\<^sub>x(1) pa e `distinct (map fst phis_stats)`
            proof (induction old_b_id phis_stats arbitrary: pv v ps phi_assignments rule: compute_phis.induct)
              case (1 old_b_id a psss as)
              show ?case
              proof (cases "a = pv")
                case True
                have "psss = phi_assignments"
                  using 1 True by (metis distinct_map_fstD list.set_intros(1))
                then show ?thesis
                  using True 1 by (auto simp add: option_to_sum_def  split: sum_bind_splits)
              next
                case False
                then show ?thesis
                  using 1 by (auto split: sum_bind_splits)
              qed
            qed (auto)
          show ?thesis
            using v y\<^sub>x f unfolding represents_frame.simps valid_var_mapping.simps
            by (auto simp add: option_to_sum_def operand_value_cases
                split: operand.splits llvm_constant.splits option.splits)
        qed
        have b: "IA.has_type lterm IA.IntT" if i: "abstract_state.stack as\<^sub>2 pv = Some (t, lterm)"
          for pv t lterm
        proof (cases "map_of ps pv")
          case None
          have a: "pv \<notin> fst ` set phis_stats"
            using None d map_of_eq_None_iff by metis
          have b: "pv \<in> dom (abstract_state.stack as\<^sub>1)"
            using dom i a by blast
          have c: "abstract_state.stack as\<^sub>2 pv = abstract_state.stack as\<^sub>1 pv"
            using 1 b a by blast
          then show ?thesis
            using v i unfolding represents_frame.simps valid_var_mapping.simps by metis
        next
          case (Some a)
          have a: "pv \<in> fst ` set phis_stats"
            using Some d map_of_eq_None_iff[of ps pv] by auto
          obtain phi_assignments where pa: "(pv, phi_assignments) \<in> set phis_stats"
            using a by auto
          have b: "\<exists>type_term term\<^sub>x. phi_abstract' as\<^sub>1 as\<^sub>2 pv phi_assignments type_term term\<^sub>x old_b_id"
            using phi pa by (induction rule: phi_abstract.induct) (auto)
          obtain y\<^sub>x where y\<^sub>x: "small_step.phi_bid old_b_id phi_assignments = Some y\<^sub>x"
            "Inference_Rules.operand_value as\<^sub>1 y\<^sub>x = Some (t, lterm)"
            using i b unfolding phi_abstract'.simps by auto
          then show ?thesis
            using v unfolding represents_frame.simps valid_var_mapping.simps
            by (fastforce simp add: operand_value_cases split: operand.splits llvm_constant.splits) 
        qed
        show ?thesis
          using a b by (intro valid_var_mapping.intros) (auto)
      qed
      have d: "valid_mem as\<^sub>2 (mem f\<^sub>1) v\<^sub>1"
        apply(rule valid_mem_as_mem_unchanged[of as\<^sub>1 as\<^sub>2 _ v\<^sub>1])
        using v 1 unfolding represents_frame.simps by (auto)
      have f: "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        using 1 v  IA.impliesD[of "kb as\<^sub>1" "kb as\<^sub>2"] unfolding represents_frame.simps
        by blast
      have g: "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id"
        apply(rule as_as_step.intros[of _ v\<^sub>1]) 
        using v f by (fastforce simp add: represents_frame.simps)+
      show ?thesis
        using 1
        unfolding represents_state.simps represents_frame.simps cs\<^sub>2' cs\<^sub>2_def f\<^sub>2_def
        using cs\<^sub>1 a c d f g by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem_funs_extra) icmpAsInf_represents:
  assumes
    "icmpAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: icmpAsInf.induct)
    case (1 n p o\<^sub>1 o\<^sub>2 \<phi> t\<^sub>1 t\<^sub>2 \<chi> b type\<^sub>1 type\<^sub>2)
    note IA.implies_Language[simp del]
    note u = `update_as_term as\<^sub>1 as\<^sub>2 n (IntType 1) \<chi> (if b then \<phi> else (\<not>\<^sub>f \<phi>))`
    define ins where "ins = (Assignment n (Icmp p o\<^sub>1 o\<^sub>2))"
    obtain f\<^sub>1 fs\<^sub>1 where cs\<^sub>1: "frames cs\<^sub>1 = f\<^sub>1 # fs\<^sub>1"
      using 1 unfolding represents_state.simps
      by (metis list.exhaust_sel llvm_state.collapse)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn pp where p: "abstract_state.pos as\<^sub>1 = (fn, bn, pp)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, pp)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    obtain i\<^sub>1 where i\<^sub>1: "IA.to_int (IA.eval t\<^sub>1 v\<^sub>1) = i\<^sub>1"
      by blast
    obtain i\<^sub>2 where i\<^sub>2: "IA.to_int (IA.eval t\<^sub>2 v\<^sub>1) = i\<^sub>2"
      by blast
    have o\<^sub>1: "operand_value o\<^sub>1 = Inr (type_int_to_stack_value type\<^sub>1 i\<^sub>1)"
      using 1 i\<^sub>1 v unfolding represents_frame.simps by (auto intro: operand_value_vvm_ssn)
    have o\<^sub>2: "operand_value o\<^sub>2 = Inr (type_int_to_stack_value type\<^sub>2 i\<^sub>2)"
      using 1 i\<^sub>2 v unfolding represents_frame.simps by (auto intro: operand_value_vvm_ssn)
    define c where
      "c = icmp_llvm_constant p (type_int_to_stack_value type\<^sub>1 i\<^sub>1) (type_int_to_stack_value type\<^sub>2 i\<^sub>2)"
    define cs\<^sub>2 where "cs\<^sub>2 = update_frames (\<lambda>_. (update_pos inc_pos (update_stack f\<^sub>1 n c)#fs\<^sub>1)) cs\<^sub>1"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using 1 cs\<^sub>1 v o\<^sub>1 o\<^sub>2 p unfolding represents_frame.simps cs\<^sub>2_def c_def
      by (auto simp add: frame.expand)
(*
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1"
    note b1 = Inference_Rules.operand_value_fresh[OF \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>1 = Some (type\<^sub>1, t\<^sub>1)\<close>]
    note b2 = Inference_Rules.operand_value_fresh[OF \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>2 = Some (type\<^sub>2, t\<^sub>2)\<close>]
    have \<chi>: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A \<chi>"
      unfolding 1  by (auto simp add: vv_def v\<^sub>2_def)
    have kb2: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
      apply(rule IA.impliesD[of "kb as\<^sub>1 \<and>\<^sub>f \<chi>"])
      using v u \<chi> kb1  unfolding update_as.simps represents_frame.simps by (auto)
*)
    have v\<^sub>1_\<phi>: "IA.satisfies v\<^sub>1 (if b then \<phi> else (\<not>\<^sub>f \<phi>))"
      using u v unfolding update_as_term.simps represents_frame.simps by blast
    have c1: "stack_value_to_int c = (if b then 1 else 0)"
      using 1 v v\<^sub>1_\<phi> unfolding c_def represents_frame.simps
      by (cases p) 
        (fastforce simp add: type_int_to_stack_value_def i\<^sub>1 i\<^sub>2 split: llvm_type.splits if_splits)+
    have c2: "ll_typeof c = IntType 1"
      using 1 unfolding c_def by (cases p) (fastforce simp add: type_int_to_stack_value_def)+
    have r: "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>1 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have [simp]: "cs\<^sub>2' = cs\<^sub>2"
        using cs\<^sub>2 that by auto
      have ssn: "same_stack_names (Mapping.update n c (frame.stack f\<^sub>1)) (abstract_state.stack as\<^sub>2)"
        using u v unfolding represents_frame.simps update_as_term.simps same_stack_names.simps
        by (auto intro: same_stack_names.intros)
      have vvm: "valid_var_mapping (Mapping.update n c (frame.stack f\<^sub>1)) (abstract_state.stack as\<^sub>2) v\<^sub>1"
        using u 1 c1 c2 v
        unfolding update_as_term.simps represents_frame.simps valid_var_mapping.simps
        by (auto split: if_splits)
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>1) v\<^sub>1"
        apply(rule valid_mem_as_mem_unchanged[of as\<^sub>1 as\<^sub>2 _ v\<^sub>1])
        using v u 1 unfolding represents_frame.simps update_as_term.simps all_sym_vars_def
        by (auto)
      have r: "represents_frame (update_pos inc_pos (update_stack f\<^sub>1 n c)) as\<^sub>2 v\<^sub>1"
        using u 1 vm v ssn vvm unfolding represents_frame.simps update_as_term.simps
        by (auto intro: represents_frame.intros)
      have r: "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>1"
        using 1 r cs\<^sub>1 by (auto intro: represents_state.intros simp add: cs\<^sub>2_def represents_state.simps)
      have a: "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id"
        using v u
        unfolding represents_frame.simps update_as_term.simps all_sym_vars_def
        by (auto intro: as_as_step.intros[of _ v\<^sub>1])
      show ?thesis
        using a r by blast
    qed
    show ?thesis
      using cs\<^sub>2 r by blast
  qed
  then show
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
    by auto
qed

lemma (in ll_mem_funs_extra) returnInf_represents: "returnAsInf prog as\<^sub>1 \<Longrightarrow>
  represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1 \<Longrightarrow>
  (\<exists>c. step prog cs\<^sub>1 = Inl (ReturnValue c))"
proof(induction rule: returnAsInf.induct)
  case (1 prog as\<^sub>1 op type\<^sub>1 t\<^sub>1)
  obtain f\<^sub>1 where cs\<^sub>1: "frames cs\<^sub>1 = [f\<^sub>1]" 
    using 1 unfolding represents_state.simps
    using list_decomp_1 by blast
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 "[]" .
  have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
    by (simp add: cs\<^sub>1)
  obtain fn bn pp where p: "abstract_state.pos as\<^sub>1 = (fn, bn, pp)"
      using prod_cases3 by blast
  then have p': "frame.pos f\<^sub>1 = (fn, bn, pp)"
    using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
  have a: "step prog cs\<^sub>1 = (operand_value op \<bind> (\<lambda>c. Inl (ReturnValue c)))"
    using cs\<^sub>1 1 p p' by (auto simp add: small_step.terminate_frame_def)
  have "(\<exists>c. operand_value op = Inr c)"
    apply(subst operand_value_vvm_ssn)
    using 1 unfolding represents_state.simps represents_frame.simps by (auto)
  then obtain c where "operand_value op = Inr c"
    by auto
  then show ?case
    using a by auto
qed

lemma (in ll_mem_funs_extra) GepAsInf_represents:
  assumes
    "gepAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  (* I choose this format for the lemmas, so that the lemma namespace doesn't get too crowded *)
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: gepAsInf.induct)
    case (1 n o\<^sub>1 o\<^sub>2 t\<^sub>1 te\<^sub>1 l\<^sub>2 te\<^sub>2 \<phi> v\<^sub>n)
    note u = `update_as_var as\<^sub>1 as\<^sub>2 n (PointerType t\<^sub>1) v\<^sub>n \<phi>`
    note o1 = \<open>operand_value as\<^sub>1 o\<^sub>1 = Some (PointerType t\<^sub>1, te\<^sub>1)\<close>
    note o2 = \<open>operand_value as\<^sub>1 o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)\<close>
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have te_type: "IA.has_type te\<^sub>1 IA.IntT" "IA.has_type te\<^sub>2 IA.IntT"
      using 1 v
      unfolding represents_frame.simps operand_value_cases valid_var_mapping.simps
      by (fastforce split: operand.splits llvm_constant.splits)+
    obtain i\<^sub>1 where i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>1 = IA.Int i\<^sub>1"
      using te_type v unfolding represents_frame.simps by (meson IA.IA_exp_to_tpoly)
    obtain i\<^sub>2 where i\<^sub>2: "IA.eval te\<^sub>2 v\<^sub>1 = IA.Int i\<^sub>2"
      using te_type v unfolding represents_frame.simps by (meson IA.IA_exp_to_tpoly)
    note a1 = operand_value_vvm_ssn[OF o1]
    note a2 = operand_value_vvm_ssn[OF o2]
    have o\<^sub>1: "operand_value o\<^sub>1 = Inr (Pointer t\<^sub>1 i\<^sub>1)" "operand_value o\<^sub>2 = Inr (IntegerValue l\<^sub>2 i\<^sub>2)"
      using v 1 i\<^sub>1 i\<^sub>2 a1 a2
      unfolding represents_frame.simps type_int_to_stack_value_def
      by (fastforce)+
    define new_i where "new_i = Pointer t\<^sub>1 (i\<^sub>1 + int (len_of t\<^sub>1) * i\<^sub>2)"
    define s\<^sub>2 where
      "s\<^sub>2 = Mapping.update n new_i (frame.stack f\<^sub>1)"
    define f\<^sub>2 where "f\<^sub>2 = update_pos (\<lambda>_. (fn, bn, Suc p)) (LLVM_State.update_stack (\<lambda>_. s\<^sub>2) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2 # fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using o\<^sub>1 cs\<^sub>1 1 p' p by (auto intro!: update_pos_cong simp add: cs\<^sub>2_def f\<^sub>2_def s\<^sub>2_def new_i_def)
    define v\<^sub>2 where "v\<^sub>2 = v\<^sub>1((v\<^sub>n, IA.IntT) := IA.Int (i\<^sub>1 + int (len_of t\<^sub>1) * i\<^sub>2))"
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have v\<^sub>2: "v\<^sub>2 (v\<^sub>n, IA.IntT) = IA.Int (i\<^sub>1 + int (len_of t\<^sub>1) * i\<^sub>2)"
        unfolding v\<^sub>2_def by simp
      have [simp]: "IA.assignment v\<^sub>2"
        using v unfolding v\<^sub>2_def represents_frame.simps by fastforce
      have v\<^sub>2_i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>2 = IA.Int i\<^sub>1" "IA.eval te\<^sub>2 v\<^sub>2 = IA.Int i\<^sub>2"
        using 1 i\<^sub>1 i\<^sub>2 unfolding v\<^sub>2_def update_as_var.simps
        by (auto simp add: IA.eval_with_fresh_var[OF operand_value_fresh])
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>1"
      proof -
        have "(v\<^sub>n, IA.IntT) \<notin> vars_formula (kb as\<^sub>1)"
          using u by (auto simp add: all_sym_vars_def update_as_var.simps)
        then show ?thesis
          using u v by (auto simp add: represents_frame.simps v\<^sub>2_def)
      qed
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A \<phi>"
        unfolding `\<phi> = encode_eq (encode_int_var v\<^sub>n)
                 (Fun (IA.SumF 2) [te\<^sub>1, (Fun (IA.ProdF 2) [te\<^sub>2, encode_int_const (len_of t\<^sub>1)])])`
        by  (auto simp add: i\<^sub>1 i\<^sub>2 v\<^sub>2_i\<^sub>1 v\<^sub>2)
      have [simp]: "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        apply(rule IA.impliesD[of "kb as\<^sub>1 \<and>\<^sub>f \<phi>"])
        using update_as_var.simps u apply(metis)
        using represents_frame.simps by (auto)
      have a: "same_stack_names s\<^sub>2 (abstract_state.stack as\<^sub>2)"
        using v unfolding represents_frame.simps s\<^sub>2_def
        by (intro ssn_update[OF u, of "frame.stack f\<^sub>1"]) auto
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>1) v\<^sub>2"
        apply(rule valid_mem_as_mem_unchanged[of as\<^sub>1 as\<^sub>2 _ v\<^sub>1])
        using v u 1 unfolding represents_frame.simps update_as_var.simps all_sym_vars_def
        by (auto simp add: v\<^sub>2_def)
      have vvm: "valid_var_mapping s\<^sub>2 (abstract_state.stack as\<^sub>2) v\<^sub>2"
          unfolding s\<^sub>2_def
          apply(rule vvm_update[OF _ u, of "frame.stack f\<^sub>1" v\<^sub>1, where y="new_i"])
          using represents_frame.cases v apply blast
          using v\<^sub>2_def by (auto simp add: new_i_def)
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>2"
        using a vm 1 vvm by (auto simp add: f\<^sub>2_def represents_frame.simps p)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2"
         using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
        apply(rule as_as_step.intros[where v\<^sub>1'=v\<^sub>2])
        using v unfolding represents_frame.simps
        using u unfolding update_as_var.simps apply (auto)
        using u unfolding update_as_var.simps by (auto simp add: v\<^sub>2_def)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

lemma (in ll_mem_funs_extra) ptrToIntAsInf_represents:
  assumes
    "ptrToIntAsInf prog as\<^sub>1 as\<^sub>2"
    "represents_state cs\<^sub>1 as\<^sub>1 v\<^sub>1"
  shows 
    "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id)"
proof -
  (* I choose this format for the lemmas, so that the lemma namespace doesn't get too crowded *)
  have "isOK (step prog cs\<^sub>1)
     \<and> (\<forall>cs\<^sub>2. step prog cs\<^sub>1 = Inr cs\<^sub>2 \<longrightarrow> (\<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id))"
    using assms proof(induction rule: ptrToIntAsInf.induct)
    case (1 n o\<^sub>1 t pt\<^sub>1 te\<^sub>1 l)
    note u = `update_as_term as\<^sub>1 as\<^sub>2 n t te\<^sub>1 True\<^sub>f`
    obtain f\<^sub>1 fs\<^sub>1  where cs\<^sub>1: "frames cs\<^sub>1 = (f\<^sub>1 # fs\<^sub>1)"
      using 1 unfolding represents_state.simps by (metis hd_Cons_tl)
    interpret small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .
    have [simp]: "hd (frames cs\<^sub>1) = f\<^sub>1"
      by (simp add: cs\<^sub>1)
    obtain fn bn p where p: "abstract_state.pos as\<^sub>1 = (fn, bn, p)"
      using prod_cases3 by blast
    then have p': "frame.pos f\<^sub>1 = (fn, bn, p)"
      using 1 cs\<^sub>1 by (auto simp add: represents_state.simps represents_frame.simps)
    have v: "represents_frame f\<^sub>1 as\<^sub>1 v\<^sub>1"
      using 1 unfolding represents_state.simps by auto
    have te\<^sub>1_type: "IA.has_type te\<^sub>1 IA.IntT"
      using \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>1 = Some (PointerType pt\<^sub>1, te\<^sub>1)\<close> v 
      unfolding represents_frame.simps operand_value_cases valid_var_mapping.simps
      by (fastforce split: operand.splits llvm_constant.splits)
    obtain i\<^sub>1 where i\<^sub>1: "IA.eval te\<^sub>1 v\<^sub>1 = IA.Int i\<^sub>1"
      using te\<^sub>1_type v unfolding represents_frame.simps by (meson IA.IA_exp_to_tpoly)
    note a1 = operand_value_vvm_ssn[OF \<open>Inference_Rules.operand_value as\<^sub>1 o\<^sub>1 = Some (PointerType pt\<^sub>1, te\<^sub>1)\<close>]
    have o\<^sub>1: "operand_value o\<^sub>1 = Inr (Pointer pt\<^sub>1 i\<^sub>1)"
      using v 1 i\<^sub>1 a1 unfolding represents_frame.simps type_int_to_stack_value_def by (fastforce)+
    define s\<^sub>2 where
      "s\<^sub>2 = Mapping.update n (IntegerValue l i\<^sub>1) (frame.stack f\<^sub>1)"
    define f\<^sub>2 where "f\<^sub>2 = update_pos (\<lambda>_. (fn, bn, Suc p)) (LLVM_State.update_stack (\<lambda>_. s\<^sub>2) f\<^sub>1)"
    define cs\<^sub>2 where "cs\<^sub>2 = Llvm_state (f\<^sub>2 # fs\<^sub>1)"
    have cs\<^sub>2: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      using o\<^sub>1 cs\<^sub>1 1 p' p by (auto simp add: cs\<^sub>2_def f\<^sub>2_def s\<^sub>2_def intro!: update_pos_cong)
    have "represents_state cs\<^sub>2' as\<^sub>2 v\<^sub>1 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id" if "step prog cs\<^sub>1 = Inr cs\<^sub>2'" for cs\<^sub>2'
    proof -
      have cs\<^sub>2': "cs\<^sub>2' = cs\<^sub>2"
        using that cs\<^sub>2 by simp
      have v\<^sub>1_kb\<^sub>2: "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A kb as\<^sub>2"
        using u v unfolding update_as_term.simps represents_frame.simps by blast
      have a: "same_stack_names s\<^sub>2 (abstract_state.stack as\<^sub>2)"
        using v u
        unfolding update_as_term.simps represents_frame.simps s\<^sub>2_def same_stack_names.simps
        by auto
      have vm: "valid_mem as\<^sub>2 (mem f\<^sub>1) v\<^sub>1"
        apply(rule valid_mem_as_mem_unchanged[of as\<^sub>1 as\<^sub>2 _ v\<^sub>1])
        using v u 1 unfolding represents_frame.simps update_as_term.simps all_sym_vars_def
        by (auto)
      have vvm: "valid_var_mapping s\<^sub>2 (abstract_state.stack as\<^sub>2) v\<^sub>1"
      proof (rule valid_var_mapping.intros, goal_cases case1 case2)
        case (case1 v pv lterm t)
        then show ?case
          using 1 u v i\<^sub>1 unfolding represents_frame.simps valid_var_mapping.simps update_as_term.simps
          by (auto simp add: f\<^sub>2_def s\<^sub>2_def split: if_splits)
      next
        case (case2 pv lterm t)
        then show ?case
          using u v te\<^sub>1_type
          unfolding update_as_term.simps represents_frame.simps valid_var_mapping.simps
          by (fastforce split: if_splits)
      qed
      have r_f\<^sub>2_v\<^sub>2: "represents_frame f\<^sub>2 as\<^sub>2 v\<^sub>1"
        using v\<^sub>1_kb\<^sub>2 v a vm 1 vvm by (auto simp add: f\<^sub>2_def represents_frame.simps p)
      have "represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>1"
         using r_f\<^sub>2_v\<^sub>2 1 cs\<^sub>1 unfolding cs\<^sub>2_def represents_state.simps by auto
      moreover have "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>1 id"
        apply(rule as_as_step.intros[where v\<^sub>1'=v\<^sub>1])
        using v u v\<^sub>1_kb\<^sub>2 unfolding represents_frame.simps update_as_term.simps by (auto)
      ultimately show ?thesis
        using cs\<^sub>2' by auto
    qed
    then show ?case
      using cs\<^sub>2 by blast
  qed
  then show "isOK (step prog cs\<^sub>1)"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>2. represents_state cs\<^sub>2 as\<^sub>2 v\<^sub>2 \<and> as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 id"
    by blast+
qed

end