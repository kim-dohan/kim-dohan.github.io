theory SE_Graph
  imports
    Inference_Rules_Soundness
    SE_Graph_Pre
    "HOL-ex.Sketch_and_Explore"
begin

locale llvm_se_graph =
  graph' as_of_node
  + ll_mem _ _ _ _ empty_mem
  for as_of_node :: "'n \<Rightarrow> ('lv::linorder) abstract_state"
  and empty_mem :: "'mem"
  +
  fixes prog :: llvm_prog
begin

inductive represents for cs n v where
  "represents cs n v"
if "n \<in> nodes" "represents_state cs (as_of_node n) v"

inductive one_successor for as\<^sub>1 as\<^sub>2 \<mu> where
  "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "evalAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "branchAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "condBranchAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "icmpAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "storeAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "allocAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "loadAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "GepAsInf prog as\<^sub>1 as\<^sub>2" "\<mu> = id"
| "one_successor as\<^sub>1 as\<^sub>2 \<mu>" if "genAsInf as\<^sub>1 as\<^sub>2 \<mu>"

inductive valid_edge where
  "valid_edge n" if "one_successor (as_of_node n) (as_of_node n') (renaming_of_edge (n,n'))" "(n,n') \<in> edges"
| "valid_edge n" if
  "refineAsInf (as_of_node n) (as_of_node n\<^sub>t) (as_of_node n\<^sub>f)" "(n,n\<^sub>t) \<in> edges" "(n,n\<^sub>f) \<in> edges"
  "renaming_of_edge (n,n\<^sub>t) = id"  "renaming_of_edge (n,n\<^sub>f) = id"
| "valid_edge n" if "returnAsInf prog (as_of_node n)" "n \<in> nodes"

definition seg_represents where
  "seg_represents = (\<forall> n \<in> nodes. valid_edge n)"

context
  fixes cs :: "nat \<Rightarrow> 'mem llvm_state"
  assumes closed: seg_represents
  and inf_run: "step prog (cs i) = Inr (cs (Suc i))"
begin

lemma closed_graph_inf_run_successor:
  assumes repr: "represents (cs i) n v"
  shows "\<exists> j m v'. represents (cs j) m v' \<and> ((n, v), (m, v')) \<in> as_step"
proof -
  have r: "represents_state (cs i) (as_of_node n) v"
    using repr unfolding represents.simps by blast
  note inf_rules = 
    evalAsInf_represents(2)[OF _ r inf_run]
    branchAsInf_represents(2)[OF _ r inf_run]
    condBranchAsInf_represents(2)[OF _ r inf_run]
    icmpAsInf_represents(2)[OF _ r inf_run]
    storeAsInf_represents(2)[OF _ r inf_run]
    allocAsInf_represents(2)[OF _ r inf_run]
    loadAsInf_represents(2)[OF _ r inf_run]
    GepAsInf_represents(2)[OF _ r inf_run]
    genAsInf_represents[OF _ r]
    refineAsInf_represents[OF _ r]
    returnInf_represents[OF _ r]
  from repr[unfolded represents.simps] have n: "n \<in> nodes" by auto
  from closed[unfolded seg_represents_def, rule_format, OF n]
  consider
      (one) n' where "one_successor (as_of_node n) (as_of_node n') (renaming_of_edge (n, n'))" "(n,n') \<in> edges"
    | (ref) n\<^sub>t n\<^sub>f where "refineAsInf (as_of_node n) (as_of_node n\<^sub>t) (as_of_node n\<^sub>f)" "(n,n\<^sub>t) \<in> edges" "(n,n\<^sub>f) \<in> edges"
      "renaming_of_edge (n,n\<^sub>t) = id"  "renaming_of_edge (n,n\<^sub>f) = id"
    | (ret) "returnAsInf prog (as_of_node n)" "n \<in> nodes"
    unfolding valid_edge.simps by auto
  then show ?thesis
  proof cases
    case (one n')
    then have "\<exists>v'. represents (cs (Suc i)) n' v' \<and> ((n, v), (n', v')) \<in> as_step"
      if "\<not> genAsInf (as_of_node n) (as_of_node n') (renaming_of_edge (n, n'))"
      unfolding one_successor.simps
      using inf_rules that
      by (auto simp add: represents.simps as_step.simps nodes_def)
    moreover have "\<exists>v'. represents (cs i) n' v' \<and> ((n, v), (n', v')) \<in> as_step"
      if "genAsInf (as_of_node n) (as_of_node n') (renaming_of_edge (n, n'))"
      using one unfolding one_successor.simps
      using inf_rules that
      by (auto simp add: represents.simps as_step.simps nodes_def)
    ultimately show ?thesis
      by blast
  next
    case (ref n\<^sub>t n\<^sub>f)
    then have "\<exists>v'. represents (cs i) n\<^sub>t v' \<and> ((n, v), (n\<^sub>t, v')) \<in> as_step \<or>
                   represents (cs i) n\<^sub>f v' \<and> ((n, v), (n\<^sub>f, v')) \<in> as_step"
      using refineAsInf_represents[OF ref(1) r]
      by (auto simp add: represents.simps as_step.simps nodes_def)
    then show ?thesis
      by blast
  next
    case (ret)
    then show ?thesis
      using inf_rules inf_run
      by (metis sum.simps)
  qed
qed

context
  fixes n_init :: 'n
    and i_init :: nat
    and v_init ::  "'lv \<times> IA.ty \<Rightarrow> IA.val"
  assumes init: "represents (cs i_init) n_init v_init"
begin
fun ni where
  "ni 0 = (n_init, i_init, v_init)"
| "ni (Suc k) = (let (n, i, v) = ni k in
  (SOME (n', i', v'). represents (cs i') n' v' \<and> ((n, v), (n', v')) \<in> as_step))"


declare ni.simps[simp del]

lemma inf_simulation: 
  assumes "ni k = (n, i, v)" "ni (Suc k) = (n', i', v')"
  shows "((n, v) , (n', v')) \<in> as_step"
proof -
  have "?thesis \<and> represents (cs i) n v \<and> represents (cs i') n' v'"

    using assms proof (induction k arbitrary: n i v n' i' v')
    case 0
    let ?P = "\<lambda>x. case x of (n', i', v') \<Rightarrow> represents (cs i') n' v' \<and> ((n, v), (n', v')) \<in> as_step"
    have a: "n_init = n" "v_init = v"
      using 0 by (auto simp add: ni.simps)
    have "\<exists>j m v'. represents (cs j) m v' \<and> ((n, v), m, v') \<in> as_step"
      using 0 closed_graph_inf_run_successor init unfolding ni.simps by blast
    then have b: "\<exists>x. ?P x"
      by blast
    have "?P (ni (Suc 0))"
      unfolding ni.simps unfolding Let_def a using someI_ex[OF b] by auto
    then show ?case
      using 0 init ni.simps by auto 
  next
    case (Suc k)
    let ?P = "\<lambda>x. case x of (n', i', v') \<Rightarrow> represents (cs i') n' v' \<and> ((n, v), (n', v')) \<in> as_step"
    have a: "represents (cs i) n v"
      using Suc prod.exhaust by metis
    then have "\<exists>j m v'. represents (cs j) m v' \<and> ((n, v), m, v') \<in> as_step"
      using closed_graph_inf_run_successor by auto
    then have b: "\<exists>x. ?P x"
      by blast
    have "?P (ni (Suc (Suc k)))"
      apply(subst ni.simps) unfolding Let_def Suc using  someI_ex[OF b] by auto
    then show ?case
      using a Suc by auto
  qed
  then show ?thesis
    by simp
qed

end
end
end

fun initial_abstract_state where
  "initial_abstract_state p fn as =
   (let op = do {
    fu \<leftarrow> find_fun p fn;
    let bn = basic_block.name (hd_blocks fu);
    let p = map parameter_name (params fu);
    Inr (set p = dom (abstract_state.stack as)
         \<and> inj_on (abstract_state.stack as) (dom (abstract_state.stack as))
         \<and> abstract_state.pos as = (fn, bn, 0)
         \<and> IA.valid (kb as))
    }
    in case op of Inr x \<Rightarrow> x | Inl _ \<Rightarrow> False)"

fun initial_llvm_frame where
  "initial_llvm_frame p fn fr =
   (let op = do {
    fu \<leftarrow> find_fun p fn;
    let bn = basic_block.name (hd_blocks fu);
    let p = map parameter_name (params fu);
    Inr (Mapping.keys (frame.stack fr) = set p \<and> frame.pos fr = (fn, bn, 0))
    }
    in case op of Inr x \<Rightarrow> x | Inl _ \<Rightarrow> False)"

fun initial_fun_llvm_state where
  "initial_fun_llvm_state p fn s =
    (case frames s of
        (f#fs) \<Rightarrow> initial_llvm_frame p fn f
      | [] \<Rightarrow> False)"

context llvm_se_graph
begin

lemma SN_as_step_imp_SN_step'_relation:
  assumes seg_represents: seg_represents
  and repr: "represents c n v"
  and SN: "SN_on as_step {(n, v)}"
shows "SN_on (step_relation prog) {c}"
proof
  fix cs :: "nat \<Rightarrow> 'mem llvm_state"
  assume a: "cs 0 \<in> {c}"
  hence repr: "represents (cs 0) n v"
    using repr by auto
  assume b: "\<forall> i. (cs i, cs (Suc i)) \<in> step_relation prog"
  hence inf_run: "step prog (cs i) = (Inr (cs (Suc i)))" for i
    unfolding step_relation_def by auto
  define cs' where "cs' = (\<lambda>i. (cs i, assig_of_state (cs i)))"
  let ?v = "\<lambda>x. case x of (n,i,v) \<Rightarrow> v"
  let ?n = "\<lambda>x. case x of (n,i,v) \<Rightarrow> n"
  define vs where "vs k = (?n (ni cs n 0 v k), ?v ((ni cs n 0 v k)))" for k
  have c: "vs 0 \<in> {(n, v)}"
    unfolding vs_def ni.simps[OF seg_represents, of cs, OF inf_run repr] using a by auto
  note d = inf_simulation[OF seg_represents, of cs, OF inf_run repr, unfolded ni.simps]
  then have "(vs k, vs (Suc k)) \<in> as_step" for k
    unfolding vs_def by (auto split: prod.splits)
  then show False
    using c SN by auto
qed

(*
lemma SN_on_step'_step:
  assumes "SN_on (step'_relation prog) {c}" "stack_size c = 1"
  shows "SN_on (step_relation prog) {c}"
proof
  fix cs :: "nat \<Rightarrow> llvm_state"
  assume 1: "cs 0 \<in> {c}"
  assume 2: "\<forall> i. (cs i, cs (Suc i)) \<in> step_relation prog"
  then have "step prog (cs i) = Inr (cs (Suc i))" for i
    unfolding step_relation_def by simp
  then interpret inf_run cs prog
    by unfold_locales simp
  define cs' where "cs' x = cs (inf_run.r cs prog x)" for x
  have 3: "cs' 0 = cs 0"
    unfolding cs'_def
    using stack_never_empty assms 1
    apply(auto simp add: k\<^sub>m\<^sub>i\<^sub>n_def min_stack_size_def s\<^sub>c\<^sub>s_def)
    apply(rule arg_cong[of _ _ cs])
    apply(rule Least_eq_0)
    apply(simp add: image_def)
    apply(rule Least_equality[symmetric])
     apply(metis)
    using nat_geq_1_eq_neqz by auto
  have "step' prog (cs' i) (Inr (cs' (Suc i)))" for i
    using inf_run_step' unfolding cs'_def by simp
  then show False
    using assms 1 3 step'_relation_def by blast
qed
*)
(*
lemma same_stack_names_dom:
  assumes "dom m' = Mapping.keys m"
  shows "same_stack_names m m'"
    using assms by (auto intro!: same_stack_names.intros simp add: dom_def keys_dom_lookup)

lemma SN_on_initial_state:
  assumes "SN_on as_step {(n, assig_of_state c)}"
    "initial_abstract_state prog f (as_of_node n)" "n \<in> nodes"
    "initial_llvm_frame prog f fr" "frames c = [fr]" "seg_represents"
  shows "SN_on (step'_relation prog) {c}"
proof -
  have "\<exists>v. represents_frame (hd (frames c)) (as_of_node n) v"
  proof -
    let ?lookup_f = "Mapping.lookup (frame.stack (hd (frames c)))"
    let ?lookup_as = "abstract_state.stack (as_of_node n)"
    define v where "v =
      (\<lambda>t. case t of
              (lv, IA.IntT) \<Rightarrow>
                 (if (\<exists>pv. ?lookup_as pv = Some lv)
                   then IA.Int (integerValue (the (?lookup_f (SOME pv. ?lookup_as pv = Some lv))))
                   else IA.Int 0)
             | _ \<Rightarrow> IA.Bool True)"
    have "IA.assignment v"
      unfolding v_def by (auto split: prod.splits IA.ty.splits)
    moreover have "same_stack_names (frame.stack (hd (frames c))) (abstract_state.stack (as_of_node n))"
      using assms by (intro same_stack_names_dom) (auto split: list.splits sum_bind_splits)
    moreover have "valid_var_mapping (frame.stack (hd (frames c))) (abstract_state.stack (as_of_node n)) v"
    proof -
      have "integerValue (the (?lookup_f (SOME pv. ?lookup_as pv = Some lv))) = i"
        if a: "?lookup_f pv = Some (IntConstant l i)" "?lookup_as pv = Some lv"
        for pv lv l i
      proof -
        have b: "x = pv" if "?lookup_as x = Some lv" for x
          using assms a that by (auto split: option.splits sum_bind_splits simp add: domI inj_onD)
        then have c: "integerValue (the (?lookup_f x)) = i"
          if "abstract_state.stack (as_of_node n) x = Some lv" for x
          using that a by (subst b) (auto)
        show ?thesis
          by(rule someI2[of _ pv])
            (use that assms c in \<open>auto split: option.splits Option.bind_splits\<close>)
      qed
      then show ?thesis
        by (auto intro!: valid_var_mapping.intros simp add: v_def)
    qed
    ultimately show ?thesis
      using assms
      by (intro exI[of _ v]) (auto intro: represents_frame.intros split: list.splits sum_bind_splits)
  qed
  then have "represents c n"
    using assms unfolding represents.simps represents_state.simps
    by (auto split: option.splits)
  then show ?thesis
    using assms by (auto intro: SN_as_step_imp_SN_step'_relation)
qed

end
*)
unbundle no_IA_formula_notation

end
end
