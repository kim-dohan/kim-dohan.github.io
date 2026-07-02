theory Step_Prime
  imports
    Step_External
    Misc_Aux
begin

section \<open>Draft\<close>

lemmas step_splits =
  action.splits
  call.splits
  list.splits
  option.splits
  named.splits
  instruction.splits
  llvm_fun.splits
  prod.splits
  r_instruction.splits
  sum_bind_splits
  sum.splits
  terminator.splits

ML \<open>
fun split_thms ctxt t =
  (case first_field "case_" t of
    NONE => []
  | SOME (_, stuff) =>
     (Proof_Context.get_thms ctxt (stuff ^ ".splits") handle _ => [])
  )

fun find_split_rules ctxt (a $ b) = find_split_rules ctxt a @ find_split_rules ctxt b
  | find_split_rules _ (Free (_, _)) = []
  | find_split_rules ctxt (Const (name, _)) = split_thms ctxt name
  | find_split_rules ctxt (Abs (_, _, a)) = find_split_rules ctxt a
  | find_split_rules _ (Bound _) = []
  | find_split_rules _ (Var _) = []

(*taken from the definition of the split tactic*)
fun gen_split_tac _ [] = K no_tac
  | gen_split_tac ctxt (split::splits) =
      split_tac ctxt [split] ORELSE'
         gen_split_tac ctxt splits;

fun splitter ctxt i thm =
   (CHANGED_PROP o gen_split_tac ctxt (@{thms if_splits} @ find_split_rules ctxt (Thm.prop_of thm))) i thm
\<close>

method_setup mysplit = \<open>
  Scan.optional Attrib.thms [] >>
    (fn thms => fn ctxt =>
      METHOD (fn facts => REPEAT (HEADGOAL (splitter ctxt))))
\<close> "apply splits the goal"

subsection \<open>Dropping frames\<close>

definition drop_frames where
  "drop_frames k cs = update_frames (\<lambda>fs. drop_tail k fs) cs"

subsection \<open>Extending small_step\<close>

context small_step
begin

lemmas simps =
  run_instruction.simps
  update_frames_stack.simps
  update_frame.simps
  terminate_frame_def
  ret_from_frame.simps
  call_function.simps
  enter_frame.simps



definition terminate_frame' :: "terminator \<Rightarrow> llvm_state error" where
  "terminate_frame' t = do {
    (case t of
       Ret (Some o1) \<Rightarrow> do {c \<leftarrow> operand_value o1;
                            error (ReturnValue c)}
    | _ \<Rightarrow> terminate_frame t)}"

lemma terminate_frame':
  assumes "\<nexists>o1. t = Ret (Some o1)"
  shows "terminate_frame' t = terminate_frame t"
  using assms
  by (auto simp add: terminate_frame'_def split: option.splits named.splits terminator.splits)

end

subsection \<open>step relation with sum type instead of @{term llvm_state}}\<close>

definition step_rel_e :: "llvm_prog \<Rightarrow> (stuck + llvm_state) rel" where
  "step_rel_e prog = { (bef, aft) . bef \<bind> step prog = aft }"

lemma step_relation_step_rel_e:
  assumes "(cs\<^sub>1, cs\<^sub>n) \<in> step_relation prog"
  shows "(Inr cs\<^sub>1, Inr cs\<^sub>n) \<in> step_rel_e prog"
  using assms unfolding step_relation_def step_rel_e_def by (auto simp del: step.simps)

lemma step_relation_step_rel_e_trancl:
  assumes "(cs\<^sub>1, cs\<^sub>n) \<in> (step_relation prog)\<^sup>+"
  shows "(Inr cs\<^sub>1, Inr cs\<^sub>n) \<in> (step_rel_e prog)\<^sup>+"
  using assms by (induction cs\<^sub>1 cs\<^sub>n rule: trancl.induct)
  (use step_relation_step_rel_e in \<open>auto intro: trancl.intros\<close>)

lemma step_relation_step_rel_e_rtrancl:
  assumes "(cs\<^sub>1, cs\<^sub>n) \<in> (step_relation prog)\<^sup>*"
  shows "(Inr cs\<^sub>1, Inr cs\<^sub>n) \<in> (step_rel_e prog)\<^sup>*"
  using assms by (induction cs\<^sub>1 cs\<^sub>n rule: rtrancl.induct)
  (use step_relation_step_rel_e in \<open>auto intro: rtrancl.intros\<close>)


subsection \<open>step' semantics\<close>

inductive step_call for prog s f fs n t g ps s' where
  "step_call prog s f fs n t g ps s'"
if "small_step.call_external_function prog s f fs g ps n s'"
| "step_call prog s f fs n t g ps s'"
if "Inr f' = small_step.enter_frame prog f g ps"
   "(Inr (update_frames (\<lambda>_. [f']) s), Inl (ReturnValue c)) \<in> (step_rel_e prog)\<^sup>+"
   "s' = small_step.update_frames_stack s f fs n (Inr c)"

definition step' :: "llvm_prog \<Rightarrow> llvm_state \<Rightarrow> llvm_state error \<Rightarrow> bool" where
  "step' prog s s' = (case frames s of
      (f#fs) \<Rightarrow>
        (case find_statement prog (frame.pos f)
        of Inr (Terminator t)  \<Rightarrow> s' = small_step.terminate_frame' prog s f fs t
        |  Inr (Instruction (Assignment n (R_Call (Call t g ps)))) \<Rightarrow> step_call prog s f fs n t g ps s'
        |  _ \<Rightarrow> s' = step prog s)
     | [] \<Rightarrow> s' = step prog s)"

definition step'_relation :: "llvm_prog \<Rightarrow> llvm_state rel" where
  "step'_relation prog = {(bef, aft) . step' prog bef (Inr aft)}"

subsection \<open>Stack size\<close>

definition stack_size where
  "stack_size cs = length (frames cs)"

lemma stack_size_non_call:
  assumes
    "\<nexists>n c. find_statement prog (frame.pos (hd (frames cs\<^sub>1))) = Inr (Instruction (Assignment n (R_Call c)))"
    "step prog cs\<^sub>1 = Inr cs\<^sub>2"
  shows
    "stack_size cs\<^sub>1 \<ge> stack_size cs\<^sub>2"
  using assms

  by (auto split: list.splits option.splits action.splits named.splits instruction.splits r_instruction.splits
   sum_bind_splits prod.splits terminator.splits sum.splits call.splits simp add: small_step.simps stack_size_def
   elim!: option_to_sum.elims)

(* not yet supporting void functions *)
definition is_call where
  "is_call prog s = (case frames s of
      (f#fs) \<Rightarrow>
        (case find_statement prog (frame.pos f)
        of Inr (Instruction (Assignment n (R_Call c))) \<Rightarrow> True
        |  _ \<Rightarrow> False)
     | [] \<Rightarrow> False)"

locale inf_run =
  fixes cs :: "nat \<Rightarrow> llvm_state" and prog :: "llvm_prog"
  assumes inf_run: "step prog (cs i) = Inr (cs (Suc i))"
begin

subsection \<open>Stack size in an infinite chain of steps\<close>

definition s\<^sub>c\<^sub>s where
  "s\<^sub>c\<^sub>s x = stack_size (cs x)"

lemma stack_never_empty: "0 < s\<^sub>c\<^sub>s i"
  using inf_run[of i] by (auto simp add: stack_size_def s\<^sub>c\<^sub>s_def)

definition min_stack_size where "min_stack_size = (LEAST i. i \<in> range s\<^sub>c\<^sub>s)"

lemma min_stack_size: "min_stack_size \<le> s\<^sub>c\<^sub>s i"
  unfolding min_stack_size_def by (auto intro!: Least_le)

definition k\<^sub>m\<^sub>i\<^sub>n where "k\<^sub>m\<^sub>i\<^sub>n = (LEAST k. s\<^sub>c\<^sub>s k = min_stack_size)"

lemma k_min_stack_size: "s\<^sub>c\<^sub>s k\<^sub>m\<^sub>i\<^sub>n = min_stack_size"
proof -
  have "\<exists>x. s\<^sub>c\<^sub>s x = min_stack_size"
    by (smt LeastI comp_apply min_stack_size_def rangeE range_eqI)
  then show ?thesis
    unfolding k\<^sub>m\<^sub>i\<^sub>n_def by (rule LeastI_ex)
qed


lemma stack_size_dec_inc:
  "s\<^sub>c\<^sub>s (Suc i) \<in> {s\<^sub>c\<^sub>s i, s\<^sub>c\<^sub>s i + 1, s\<^sub>c\<^sub>s i - 1}"
proof -
  show ?thesis
    unfolding s\<^sub>c\<^sub>s_def
    using inf_run[of i, symmetric]
    by (auto split: list.splits option.splits action.splits named.splits r_instruction.splits call.splits
        instruction.splits sum.splits llvm_fun.splits sum_bind_splits prod.splits terminator.splits
        simp add: frames_simp small_step.simps stack_size_def elim!: option_to_sum.elims)
qed

lemma stack_size_IVT: "\<exists>j \<le> l. s\<^sub>c\<^sub>s (k + j) = s\<^sub>c\<^sub>s k - 1" if "s\<^sub>c\<^sub>s (k + l) < s\<^sub>c\<^sub>s k"
  using that proof (induction l)
  case (Suc l)
  consider "s\<^sub>c\<^sub>s (k + Suc l) = s\<^sub>c\<^sub>s (k + l)"
    | "s\<^sub>c\<^sub>s (k + Suc l) = s\<^sub>c\<^sub>s (k + l) + 1"
    | "s\<^sub>c\<^sub>s (k + Suc l) = s\<^sub>c\<^sub>s (k + l) - 1"
    using stack_size_dec_inc by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using Suc nat_less_le by fastforce
  next
    case 2
    then show ?thesis
      using Suc le_SucI add_lessD1 by (metis)
  next
    case 3
    then consider "local.s\<^sub>c\<^sub>s (k + l) = local.s\<^sub>c\<^sub>s k" | "local.s\<^sub>c\<^sub>s (k + l) < local.s\<^sub>c\<^sub>s k"
      using Suc by arith
    then show ?thesis
      using Suc 3 le_SucI by (cases) (auto, use le_SucI in blast)
  qed
qed (auto)

lemma stack_size_eq_call:
  assumes "is_call prog (cs j)" "j < k" "s\<^sub>c\<^sub>s k < s\<^sub>c\<^sub>s j"
  shows "\<exists>i. j < i \<and> i < k \<and> s\<^sub>c\<^sub>s j = s\<^sub>c\<^sub>s i"
proof -
  have 1: "s\<^sub>c\<^sub>s (j + 1) = s\<^sub>c\<^sub>s j + 1"
    unfolding s\<^sub>c\<^sub>s_def using inf_run[of j, symmetric] assms
    by (auto split: list.splits option.splits action.splits named.splits r_instruction.splits
        call.splits
        instruction.splits llvm_fun.splits sum_bind_splits sum.splits
        simp add: is_call_def small_step.simps stack_size_def)
  then have "local.s\<^sub>c\<^sub>s (j + 1 + (k - j - 1)) < local.s\<^sub>c\<^sub>s (j + 1)"
    using assms by auto
  then obtain i where i: "i\<le>k - j - 1" "s\<^sub>c\<^sub>s (j + 1 + i) = s\<^sub>c\<^sub>s (j + 1) - 1"
    using stack_size_IVT by blast
  then have "j < j + 1 + i" "j + 1 + i < k" "s\<^sub>c\<^sub>s (j + 1 + i) = s\<^sub>c\<^sub>s j"
    using 1 assms nat_neq_iff by fastforce+
  then show ?thesis
    by metis
qed

subsection \<open>Reindexing infinite chain of steps to infinite chain of step'\<close>

fun r :: "nat \<Rightarrow> nat" where
  "r 0 = k\<^sub>m\<^sub>i\<^sub>n"
| "r (Suc i) = (
         let j = r i in
         if \<not> is_call prog (cs j)
           then j + 1
         else if (\<forall>j' > j. stack_size (cs j) < stack_size (cs j'))
           then j + 1
         else (LEAST j'. j' > j \<and> stack_size (cs j) = stack_size (cs j')))"

subsection \<open>Stack size only increases in @{term r}\<close>

lemma i_leq_r_i: "i \<le> r i"
proof (induction i)
  case (Suc i)
  then have 1: ?case if "r i < j" "s\<^sub>c\<^sub>s j \<le> s\<^sub>c\<^sub>s (r i)" "is_call prog (cs (local.r i))" for j
  proof -
    let ?P = "\<lambda>j'. r i < j' \<and> s\<^sub>c\<^sub>s (r i) = s\<^sub>c\<^sub>s j'"
    have "?P (LEAST j. ?P j)"
      by (rule LeastI_ex) (use stack_size_eq_call that in fastforce)
    then show ?thesis
      using that Suc unfolding s\<^sub>c\<^sub>s_def by (auto simp add: Let_def)
  qed
  moreover have "\<not> (\<forall>j'>local.r i. stack_size (cs (local.r i)) < stack_size (cs j'))"
    if "r i < j" "s\<^sub>c\<^sub>s j \<le> s\<^sub>c\<^sub>s (r i)" "is_call prog (cs (local.r i))" for j
    using that using leD unfolding s\<^sub>c\<^sub>s_def by (clarsimp) fastforce
  ultimately show ?case
    unfolding s\<^sub>c\<^sub>s_def using Suc by (auto simp add: Let_def split: if_splits)
qed (auto)

lemma r_strictly_monotone': "r i < r (Suc i)"
  apply(auto simp add: Let_def)
  using LeastI linorder_neqE_nat s\<^sub>c\<^sub>s_def stack_size_eq_call by smt

lemma r_strictly_monotone: "r i < r j" if "i < j"
  using that by (induction j) (use Suc that lift_Suc_mono_less r_strictly_monotone' in blast)+

lemma s\<^sub>c\<^sub>s_inc:
  assumes "i < j"
  shows "s\<^sub>c\<^sub>s (r i) \<le> s\<^sub>c\<^sub>s (r j)"
  using assms proof (induction i arbitrary: j)
  case 0
  then show ?case by (auto simp add: k_min_stack_size min_stack_size)
next
  case (Suc i k)
  define s where "s x = stack_size (cs (r x))" for x
  define j where "j = r i"
  let ?P = "(\<forall>j' > j. stack_size (cs j) < stack_size (cs j'))"
  have ?case if "is_call prog (cs j)" "?P"
  proof -
    have 1: "s (i + 1) = s i + 1"
    proof -
      have "s (i + 1) = stack_size (cs (j + 1))"
        using that unfolding s_def j_def by (auto simp add: Let_def)
      also have "\<dots> = stack_size (cs j) + 1"
        using inf_run[of j, symmetric] that
        by (auto split: step_splits
            simp add: is_call_def small_step.simps stack_size_def)
      finally show ?thesis
        unfolding s_def j_def s\<^sub>c\<^sub>s_def by simp
    qed
    show ?thesis
    proof -
      have "j < r k"
        unfolding j_def
        apply(rule r_strictly_monotone)
        using Suc by simp
      then have "stack_size (cs j) < stack_size (cs (r k))"
        using that by blast
      then show ?thesis
        using 1 unfolding s_def j_def s\<^sub>c\<^sub>s_def by simp
    qed
  qed
  moreover have ?case if "\<not> is_call prog (cs j)"
  proof -
    have a: "local.r (i + 1) = j + 1"
      using Suc_eq_plus1 j_def r.simps(2) that by presburger
    have b: False if "frames (cs (r i)) = fs1 # fs2 # fs3"
      "cs (Suc (r i)) = update_frames (\<lambda>_. update_pos inc_pos (small_step.update_stack fs2 n v) # fs3) (cs (r i))"
    for fs1 fs2 fs3 n v
    proof -
      have "length (frames (cs (Suc (local.r i)))) = Suc (length fs3)"
        using that by simp
      then show False
        using that Suc(1)[of "Suc i"] a Suc_eq_plus1 Suc_n_not_le_n j_def length_nth_simps(2)
          less_add_one s\<^sub>c\<^sub>s_def stack_size_def by (metis)
    qed
    then have "s (i + 1) = s i"
      using that using inf_run[of j, symmetric]
      unfolding s_def
(* TODO: write better proof *)
      by  (auto split: step_splits
          simp add: is_call_def  stack_size_def s_def Let_def j_def small_step.simps)
        (metis instruction.exhaust r_instruction.distinct, blast)
    then show ?thesis
      using Suc that unfolding s_def s\<^sub>c\<^sub>s_def by auto
  qed
  moreover have ?case if "is_call prog (cs j)" "\<not> ?P"
  proof -
    have "s (i + 1) = s i"
      using that unfolding s_def apply(auto simp add: Let_def j_def)
      unfolding j_def[symmetric]
      apply(rule LeastI_ex)
      using stack_size_eq_call
      by (metis (mono_tags, lifting) LeastI_ex nat_neq_iff s\<^sub>c\<^sub>s_def that(1))
    then show ?thesis
      using Suc that unfolding s_def s\<^sub>c\<^sub>s_def by auto
  qed
  ultimately show ?case
    by blast
qed

subsection \<open>No return statements encountered in reindexing\<close>

lemma r_no_return:
  assumes "find_statement prog (frame.pos (hd (frames (cs (r i))))) = Inr (Terminator (Ret t))"
  shows False
proof -
  have *: "r (Suc i) = Suc (r i)"
    unfolding s\<^sub>c\<^sub>s_def using assms by (auto simp add: Let_def is_call_def split: list.splits)
  have "s\<^sub>c\<^sub>s (r (Suc i)) = s\<^sub>c\<^sub>s (r i) - 1"
    unfolding * s\<^sub>c\<^sub>s_def using inf_run[of "r i", symmetric] assms
    by (auto simp del: r.simps split: step_splits
    simp add: small_step.simps stack_size_def elim!: option_to_sum.elims)
  then show False
    using s\<^sub>c\<^sub>s_inc[of i "Suc i"] unfolding s\<^sub>c\<^sub>s_def
    by (auto simp del: r.simps) (metis less_irrefl_nat s\<^sub>c\<^sub>s_def stack_never_empty)
qed

lemma drop_frames_step:
  assumes "k < stack_size cs\<^sub>1" "k < stack_size cs\<^sub>2" "step prog cs\<^sub>1 = Inr cs\<^sub>2"
  shows "step prog (drop_frames k cs\<^sub>1) = Inr (drop_frames k cs\<^sub>2)"
  using assms map_of_funs_name
  apply (auto simp add: small_step.simps stack_size_def drop_frames_def drop_tail_def split: list.splits option.splits
       action.splits named.splits terminator.splits instruction.splits prod.splits sum_bind_splits)
  apply(auto split: sum.splits)
(* TODO: write maintainable proof *)
  by  (auto simp add: small_step.simps stack_size_def drop_frames_def drop_tail_def split: step_splits)

lemma take_frames_step:
  assumes "k < stack_size cs\<^sub>1" "k < stack_size cs\<^sub>2" "step prog cs\<^sub>1 = Inr cs\<^sub>2"
  shows "take_tail k (frames cs\<^sub>1) = take_tail k (frames cs\<^sub>2)"
  using assms
  by (auto simp add: take_tail_Cons small_step.simps stack_size_def drop_frames_def drop_tail_def split: step_splits)

lemma drop_frames_step_plus:
  assumes
    "\<forall>l < n. step prog (ds l) = Inr (ds (Suc l))"
    "\<forall>l \<le> n. k < stack_size (ds l)"
  shows
    "(drop_frames k (ds 0), drop_frames k (ds n)) \<in> (step_relation prog)\<^sup>*"
using assms proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
    apply(rule rtrancl.intros(2))
     apply(rule Suc)
    using Suc apply(simp)
    using Suc apply(simp)
    unfolding step_relation_def
    apply(simp del: step.simps)
    apply(rule drop_frames_step)
    using Suc by (auto)
qed

lemma lower_frames_step:
  assumes
    "\<forall>l < n. step prog (ds l) = Inr (ds (Suc l))"
    "\<forall>l \<le> n. k < stack_size (ds l)"
  shows
    "take_tail k (frames (ds 0)) = take_tail k (frames (ds n))"
using assms proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "take_tail k (frames (ds n)) = take_tail k (frames (ds (Suc n)))"
    using Suc take_frames_step by simp
  then show ?case
    using Suc by auto
qed

lemma inf_run_step': "step' prog (cs (r i)) (Inr (cs (r (Suc i))))"
proof -
  define j where "j = r i"
  obtain f fs where f_fs: "frames (cs j) = f#fs"
    using inf_run[of j] by (auto split: list.splits)
  define p where "p = frame.pos f"
  have inf: "step prog (cs j) = (Inr (cs (Suc j)))"
    using inf_run by simp
  obtain c where c_def: "find_statement prog p = Inr c"
    using inf unfolding p_def by (auto simp add: f_fs split: sum.splits)
  let ?P = "(\<forall>j' > j. stack_size (cs j) < stack_size (cs j'))"
  consider (a) "\<not> is_call prog (cs j)"
    | (b) "is_call prog (cs j)" "?P"
    | (c) "is_call prog (cs j)" "\<not> ?P"
    by fastforce
  then show ?thesis
  proof cases
    case a
    have 1: "r (Suc i) = Suc j"
      using a j_def by (auto)
    then show ?thesis
    proof (cases "\<exists>x. c = Terminator (Ret (Some x))")
      case True
      then show ?thesis
        using r_no_return[of i] c_def unfolding p_def j_def[symmetric] f_fs
        by (auto simp del: r.simps)
    next
      case False
      show ?thesis
(* TODO: write maintainable proof *)
        using j_def f_fs 1 apply(auto simp add: step'_def split: option.splits)
        using inf apply(auto split: step_splits if_splits)
         apply(rule step_call.intros(1))
        subgoal by (auto simp add: small_step.simps small_step.call_external_function_def Let_def split: llvm_fun.splits option.splits)
        apply(subst small_step.terminate_frame')
         defer apply(simp)
        using False using c_def unfolding p_def by simp
    qed
  next
    case b
    have 1: "r (Suc i) = Suc j"
      using b j_def by (auto)
    then show ?thesis
      using  b j_def f_fs 1 apply(auto simp add: step'_def is_call_def split: option.splits sum.splits)
      using inf by (auto intro!: step_call.intros(1)
simp add: small_step.call_external_function_def small_step.simps split: step_splits)
  next
    case c
    define l where "l = (LEAST j'. j' > j \<and> stack_size (cs j) = stack_size (cs j'))"
    define c\<^sub>0 where "c\<^sub>0 = cs j"
    define c\<^sub>1 where "c\<^sub>1 = cs (j + 1)"
    define c\<^sub>n where "c\<^sub>n = cs l"
    define c\<^sub>n\<^sub>1 where "c\<^sub>n\<^sub>1 = cs (l - 1)"
    define s_s where "s_s = s\<^sub>c\<^sub>s j"
    have 1: "r (Suc i) = (LEAST j'. j' > j \<and> stack_size (cs j) = stack_size (cs j'))"
      using c j_def by (auto simp add: Let_def)
    have "j < l \<and> stack_size (cs j) = stack_size (cs l)"
      unfolding l_def
      apply(rule LeastI_ex)
      by (metis c(1) c(2) linorder_neqE_nat s\<^sub>c\<^sub>s_def stack_size_eq_call)
    then have l: "j < l" "stack_size (cs j) = stack_size (cs l)"
      by auto
    have False if a: "s\<^sub>c\<^sub>s i \<le> s\<^sub>c\<^sub>s j" "j < i" "i < l" for i
    proof (cases "s\<^sub>c\<^sub>s i = s\<^sub>c\<^sub>s j")
      case True
      have "l \<le> i"
        unfolding l_def apply(rule Least_le)
        using True that unfolding s\<^sub>c\<^sub>s_def by auto
      then show ?thesis
        using that by auto
    next
      case False
      have 1: "s\<^sub>c\<^sub>s i < s\<^sub>c\<^sub>s j"
        using that False by simp
      then obtain k where k: "j < k"  "k < i" "local.s\<^sub>c\<^sub>s j = local.s\<^sub>c\<^sub>s k"
        using stack_size_eq_call a c by blast
      then have "k < l"
        using a by simp
      moreover have "l \<le> k"
        unfolding l_def apply(rule Least_le)
        using k unfolding s\<^sub>c\<^sub>s_def by simp
      ultimately show ?thesis
        by simp
    qed
    then have 2: "s\<^sub>c\<^sub>s i > s\<^sub>c\<^sub>s j" if "j < i" "i < l" for i
      using that leI by blast
    have 21: "j < l - 1"
    proof -
      have False if "j = l - 1"
      proof -
        have 1: "step prog (cs j) = Inr (cs l)"
          using l inf_run[of j] that by (simp)
        then have "\<exists>f fs n cc. frames (cs j) = f#fs \<and> find_statement prog (pos f) = Inr (Instruction (Assignment n (R_Call cc)))"
          using c apply(auto simp add: is_call_def split: step_splits if_splits)
          by (metis r_instruction.exhaust)
        then show False
          using 1 l(2)[symmetric] c apply(auto split: step_splits if_splits
              simp add: small_step.simps is_call_def stack_size_def)
          by (metis length_Cons lessI less_irrefl_nat llvm_state.sel)
      qed
      then show ?thesis
        using l by fastforce
    qed
    have 3: "step prog c\<^sub>n\<^sub>1 = Inr c\<^sub>n"
      unfolding c\<^sub>n\<^sub>1_def c\<^sub>n_def using inf_run[of "l - 1"] l by auto
    have 31: "stack_size c\<^sub>1 = stack_size c\<^sub>0 + 1"
      using c inf_run[of j] unfolding c\<^sub>1_def c\<^sub>0_def
      apply(auto split: step_splits if_splits
          simp add: small_step.simps is_call_def)
      by (metis (no_types, lifting) "2" "21" Nat.lessE One_nat_def Suc_mono Suc_pred
       \<open>j < l \<and> stack_size (cs j) = stack_size (cs l)\<close> inf_run.s\<^sub>c\<^sub>s_def
      inf_run_axioms length_nth_simps(2) lessI less_irrefl_nat llvm_state.sel stack_size_def zero_less_Suc)+
    have 4: "stack_size c\<^sub>n\<^sub>1 = stack_size c\<^sub>n + 1"
    proof -
      have "stack_size c\<^sub>n \<in> {stack_size c\<^sub>n\<^sub>1, stack_size c\<^sub>n\<^sub>1 + 1, stack_size c\<^sub>n\<^sub>1 - 1}"
        using stack_size_dec_inc[of "l - 1"] l unfolding s\<^sub>c\<^sub>s_def c\<^sub>n_def c\<^sub>n\<^sub>1_def by auto
      moreover have "stack_size c\<^sub>n < stack_size c\<^sub>n\<^sub>1"
        using 2[of "l - 1"] 21 unfolding s\<^sub>c\<^sub>s_def c\<^sub>n_def c\<^sub>n\<^sub>1_def l by auto
      ultimately show ?thesis
        by auto
    qed
    obtain f\<^sub>n\<^sub>1 fs\<^sub>n\<^sub>1 where 5: "frames c\<^sub>n\<^sub>1 = f\<^sub>n\<^sub>1#fs\<^sub>n\<^sub>1"
      using 3 by (auto split: list.splits)
    have 45: "\<exists>t v. find_statement prog (frame.pos f\<^sub>n\<^sub>1) = Inr (Terminator (Ret (Some v)))"
      using 3 4 5 by (auto split: step_splits simp add: small_step.simps stack_size_def)
    have 55: "drop_frames s_s c\<^sub>n\<^sub>1 = update_frames (\<lambda>_.  [f\<^sub>n\<^sub>1]) c\<^sub>n\<^sub>1"
      using 4
      apply(simp add: drop_frames_def 5 stack_size_def s_s_def c\<^sub>n_def s\<^sub>c\<^sub>s_def)
      by (metis "5" drop_tail_except_first l(2) llvm_state.collapse stack_size_def update_frames.simps)
    define ds where "ds x = j + 1 + x" for x
    have 6: "(drop_frames s_s c\<^sub>1, drop_frames s_s c\<^sub>n\<^sub>1) \<in> (step_relation prog)\<^sup>*"
    proof -
      have "drop_frames s_s c\<^sub>1 = drop_frames s_s (cs (ds 0))"
        unfolding c\<^sub>1_def ds_def by simp
      moreover have "drop_frames s_s c\<^sub>n\<^sub>1 = drop_frames s_s (cs (ds (l - 2 - j)))"
      proof -
        have "l - 1 = j + 1 + (l - 2 - j)"
          using 21 by (auto)
        then show ?thesis
          unfolding c\<^sub>n\<^sub>1_def ds_def by metis
      qed
      moreover have "(drop_frames s_s (cs (ds 0)), drop_frames s_s (cs (ds (l - 2 - j)))) \<in> (step_relation prog)\<^sup>*"
        apply(rule drop_frames_step_plus)
         apply(auto simp add: ds_def simp del: step.simps)
        using inf_run apply(simp)
        unfolding s_s_def s\<^sub>c\<^sub>s_def apply(rule 2[unfolded s\<^sub>c\<^sub>s_def])
         apply(simp)
        using "21" by linarith
      ultimately show ?thesis
        unfolding c\<^sub>1_def c\<^sub>n\<^sub>1_def l_def by simp
    qed
    have "\<exists>c. step prog (drop_frames s_s c\<^sub>n\<^sub>1) = Inl (ReturnValue c)"
      using 55 45 3 5 by (auto simp add: small_step.simps split: sum_bind_splits)
    then obtain v where v: "step prog (drop_frames s_s c\<^sub>n\<^sub>1) = Inl (ReturnValue v)"
      by blast
    have "(Inr (drop_frames s_s c\<^sub>1), Inl (ReturnValue v)) \<in> (step_rel_e prog)\<^sup>*"
      apply(rule rtrancl.intros(2)[of _ "Inr (drop_frames s_s c\<^sub>n\<^sub>1)"])
      using 6  step_relation_step_rel_e_rtrancl apply(blast)
      using v unfolding step_rel_e_def by simp
    then have 601: "(Inr (drop_frames s_s c\<^sub>1), Inl (ReturnValue v)) \<in> (step_rel_e prog)\<^sup>+"
      unfolding rtrancl_eq_or_trancl by auto
    obtain f\<^sub>1 fs\<^sub>1 where f\<^sub>1: "frames c\<^sub>1 = f\<^sub>1#fs\<^sub>1"
      using inf_run[of "Suc j"] unfolding c\<^sub>1_def by (auto split: list.splits)
    obtain f\<^sub>0 fs\<^sub>0 where f\<^sub>0: "frames c\<^sub>0 = f\<^sub>0#fs\<^sub>0"
      using inf_run[of "j"] unfolding c\<^sub>0_def by (auto split: list.splits)
    obtain a fn t ps where
      find_s: "find_statement prog (frame.pos f\<^sub>0) = Inr (Instruction (Assignment a (R_Call (Call fn t ps))))"
      using c unfolding is_call_def using f\<^sub>0 unfolding c\<^sub>0_def
      by (auto split: step_splits) (metis call.exhaust)
    have 61: "update_frames (\<lambda>_. [f\<^sub>1]) c\<^sub>0 = drop_frames s_s c\<^sub>1"
    proof -
      have "update_frames (\<lambda>_. [f\<^sub>1]) c\<^sub>0 = Llvm_state [f\<^sub>1] (mem c\<^sub>0)"
        by (auto)
      also have "\<dots> = drop_frames s_s c\<^sub>1"
        unfolding drop_frames_def
        by (metis "31" Suc_eq_plus1 c\<^sub>0_d ef drop_tail_except_first f\<^sub>1 frames_simp inf_run.s\<^sub>c\<^sub>s_def
            inf_run_axioms length_Cons nat.inject s_s_def stack_size_def)
      finally show ?thesis
        by simp
    qed
    have 7: "Inr f\<^sub>1 = small_step.enter_frame prog f\<^sub>0 t ps"
      using inf_run[of j] f\<^sub>0 f\<^sub>1 find_s map_of_funs_name unfolding c\<^sub>0_def c\<^sub>1_def
      apply(auto elim!:  simp add: map_of_funs_name small_step.simps split: llvm_fun.splits option.splits sum_bind_splits)
      using map_of_funs_name apply(fastforce)
      using map_of_funs_name by (metis list.inject llvm_fun.inject(1) llvm_state.sel option.inject sum.inject(2))
    have 8: "(Inr (update_frames (\<lambda>_. [f\<^sub>1]) (cs (local.r i))), Inl (ReturnValue v)) \<in> (step_rel_e prog)\<^sup>+"
      using 61 601 unfolding c\<^sub>0_def j_def by auto
    have 85: "fs\<^sub>n\<^sub>1 = f\<^sub>0#fs\<^sub>0"
    proof -
      have "f\<^sub>0#fs\<^sub>0 = fs\<^sub>1"
        using inf_run[of j, symmetric] f\<^sub>0 f\<^sub>1 c unfolding c\<^sub>0_def c\<^sub>1_def
        by (auto split: step_splits
            simp add: small_step.simps is_call_def)
      also have "\<dots> = take_tail s_s (frames c\<^sub>1)"
        unfolding f\<^sub>1 apply(rule take_tail_except_first[symmetric])
        using 31 unfolding s_s_def s\<^sub>c\<^sub>s_def stack_size_def f\<^sub>1 c\<^sub>0_def by simp
      also have "c\<^sub>1 = cs (ds 0)"
        unfolding ds_def c\<^sub>1_def by simp
      also have "take_tail s_s (frames (cs (ds 0))) = take_tail s_s (frames (cs (ds (l - 2 - j))))"
        apply(rule lower_frames_step)
         apply(auto simp add: ds_def simp del: step.simps)
        using inf_run apply(simp)
        unfolding s_s_def s\<^sub>c\<^sub>s_def apply(rule 2[unfolded s\<^sub>c\<^sub>s_def])
         apply(simp)
        using "21" by linarith
      also have "cs (ds (l - 2 - j)) = c\<^sub>n\<^sub>1"
      proof -
        have "l - 1 = j + 1 + (l - 2 - j)"
          using 21 by (auto)
        then show ?thesis
          unfolding c\<^sub>n\<^sub>1_def ds_def by metis
      qed
      also have "take_tail s_s (frames c\<^sub>n\<^sub>1) = fs\<^sub>n\<^sub>1"
        unfolding 5 apply(rule take_tail_except_first)
        using 4 unfolding stack_size_def 5 s_s_def
        using c\<^sub>n_def l(2) s\<^sub>c\<^sub>s_def stack_size_def by force
      finally show ?thesis
        by simp
    qed
    have 9: "Inr (cs l) = small_step.update_frames_stack (cs (local.r i)) f\<^sub>0 fs\<^sub>0 a (Inr v)"
      using 3[symmetric] 5 45 85 v find_s by (fastforce simp add: 55 small_step.simps c\<^sub>n_def
          small_step.update_stack.simps split: prod.splits sum_bind_splits
          action.splits named.splits instruction.splits option.splits Option.bind_splits
          list.splits intro!: frame.expand elim!: option_to_sum.elims)
    show ?thesis
      unfolding 1 l_def[symmetric]
      using c 1 find_s f\<^sub>0 unfolding c\<^sub>0_def j_def
      apply(auto simp add: step'_def is_call_def j_def split: list.splits option.splits
          action.splits named.splits terminator.splits instruction.splits
          simp del: r.simps)
      apply(rule step_call.intros(2)[of f\<^sub>1, where c = v])
      using 7 8 9 by auto
  qed
qed

end

end