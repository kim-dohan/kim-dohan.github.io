theory Inference_Rules
  imports
    Abstract_State
    LLVM_Step
begin



section \<open>Playing with bundle and notation\<close>

bundle IA_formula_notation
begin
notation IA.implies (infix "\<Longrightarrow>\<^sub>I\<^sub>A" 41)
notation IA.satisfies (infix "\<Turnstile>\<^sub>I\<^sub>A" 40)
notation IA.eval ("\<lbrakk>(_)\<rbrakk>\<^sub>I\<^sub>A")
notation form_and (infixl "\<and>\<^sub>f" 42)
end

bundle no_IA_formula_notation
begin
no_notation IA.implies (infix "\<Longrightarrow>\<^sub>I\<^sub>A" 41)
no_notation IA.satisfies (infix "\<Turnstile>\<^sub>I\<^sub>A" 40)
no_notation IA.eval ("\<lbrakk>(_)\<rbrakk>\<^sub>I\<^sub>A")
no_notation form_and (infixl "\<and>\<^sub>f" 42)
end

unbundle IA_formula_notation


section \<open>Misc lemmas\<close>

lemma option_to_sum:
  "option_to_sum m l = Inr y \<Longrightarrow> m = Some y"
  by (auto simp add: option_to_sum_def split: option.splits)

lemma (in IA_locale) assignment_eval_int: "assignment ev \<Longrightarrow> \<exists>i. ev (lv, IA.IntT) = IA.Int i"
  by (metis IA.assignmentD IA.mem_Values_of_typeD prod.sel(2))

lemma (in IA_locale) assignment_eval_to_int:
  "assignment ev \<Longrightarrow> IA.to_int (ev (lv, IA.IntT)) = i \<Longrightarrow> ev (lv, IA.IntT) = IA.Int i"
  using assignment_eval_int[of ev lv] by auto 

lemma (in ll_mem) alloc_allocated_address_def:
  assumes "alloc m t l = Inr ((lb, ub), m')"
  shows  "bounds m' a = (if a \<in> {lb..<ub} then Some (lb, ub) else bounds m a)"
  using assms S6 S5 by (auto)

lemma vars_formula_satisfies:
  assumes "\<And>x. x \<in> vars_formula f \<Longrightarrow> v\<^sub>2 x = v\<^sub>1 x" "v\<^sub>1 \<Turnstile>\<^sub>I\<^sub>A f"
  shows "v\<^sub>2 \<Turnstile>\<^sub>I\<^sub>A f"
  using assms proof (induction f)
  case (Atom x)
  then have "\<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1 = \<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2"
    by force
  then show ?case
    using Atom by (auto)
next
  case (NegAtom x)
  then have "\<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1 = \<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2"
    by force
  then show ?case
    using NegAtom by (auto)
qed (fastforce+)


(*
TODO: replace camel case
TODO: simplify the ...Inf_represents lemmas
      you always have the two assumptions "represents cs\<^sub>1 n\<^sub>1" and "step prog cs\<^sub>1 = Inr cs\<^sub>2"
      and you always need to show
      "represents cs\<^sub>2 n\<^sub>2 \<and> ((n\<^sub>1, assig_of_state cs\<^sub>1), (n\<^sub>2, assig_of_state cs\<^sub>2)) \<in> as_step"
      the only thing that differs is the used inference rule
*)

section \<open>Abstract state represents concrete state\<close>

type_synonym 'lv abstract_state = "(LLVM_State.pos, name, 'lv, llvm_type) abstract_state"

inductive valid_var_mapping for
  c_stack :: "(name, stack_value) mapping"
  and as_stack :: "name \<rightharpoonup> (llvm_type \<times> 'lv IA.exp)"
  and ev :: "'lv \<times> IA.ty \<Rightarrow> IA.val"
  where
  "valid_var_mapping c_stack as_stack ev"
  if
  "\<And>v pv lterm t. Mapping.lookup c_stack pv = Some v
   \<Longrightarrow> as_stack pv = Some (t, lterm)
   \<Longrightarrow> IA.eval lterm ev  = IA.Int (stack_value_to_int v) \<and> t = ll_typeof v"
  "\<And>pv lterm t. as_stack pv = Some (t, lterm) \<Longrightarrow> IA.has_type lterm IA.IntT"

inductive same_stack_names
  for cs :: "(name, stack_value) mapping"
    and as
  where
    "same_stack_names cs as"
  if
    "\<And>pv. (Mapping.lookup cs pv \<noteq> None) = (as pv \<noteq> None)"

context ll_mem_funs_extra
begin

definition allocated_address where
  "allocated_address m a = (bounds m a \<noteq> None)"

inductive valid_allocs
  for allos v m
  where
    "valid_allocs allos v m"
  if
    "\<And>lb ub lb' ub' a. (lb, ub) \<in> allos
     \<Longrightarrow> v (lb, IA.IntT) = IA.Int lb'
     \<Longrightarrow> v (ub, IA.IntT) = IA.Int ub'
     \<Longrightarrow> lb' \<le> a
     \<Longrightarrow> a < ub'
     \<Longrightarrow> bounds m a = Some (lb', ub')"

lemma valid_allocs_mem_unchanged_intro:
  assumes
    "valid_allocs allos\<^sub>1 v\<^sub>1 m\<^sub>1"
    "allos\<^sub>1 = allos\<^sub>2"
    "\<forall>(lb, ub) \<in> allos\<^sub>1. v\<^sub>1 (lb, IA.IntT) = v\<^sub>2 (lb, IA.IntT) \<and> v\<^sub>1 (ub, IA.IntT) = v\<^sub>2 (ub, IA.IntT)"
    "bounds m\<^sub>2 = bounds m\<^sub>1"
  shows
    "valid_allocs allos\<^sub>2 v\<^sub>2 m\<^sub>2"
  using assms unfolding valid_allocs.simps by (auto split: prod.splits)

inductive valid_load for address ty mem where
  "valid_load address ty mem"
if
  "allocated_address mem address"
  "load mem ty address = Inr y"
  "ll_typeof y = ty"

inductive valid_load_with_value for address ty x mem where
  "valid_load_with_value address ty x mem"
if
  "allocated_address mem address"
  "load mem ty address = Inr y"
  "ll_typeof y = ty"
  "stack_value_to_int y = x"

lemma valid_load_with_value_valid_load: 
  "valid_load_with_value a ty x m \<Longrightarrow> valid_load a ty m"
  unfolding valid_load_with_value.simps valid_load.simps by auto

inductive valid_pointers for ps v m where
  "valid_pointers ps v m"
if
  "\<And>a lt x a' x'. ps a = Some (lt, x)
   \<Longrightarrow> v (a, IA.IntT) = IA.Int a'
   \<Longrightarrow> IA.eval x v = IA.Int x'
   \<Longrightarrow> valid_load_with_value a' lt x' m"
  "\<And>a lt x. ps a = Some (lt, x) \<Longrightarrow> IA.has_type x IA.IntT"

lemma (in IA_locale) has_type_IntT:
  "has_type x IA.IntT \<Longrightarrow> v \<in> vars_term x \<Longrightarrow> snd v = IntT"
proof (induction x arbitrary: v)
  case (Var x)
  then show ?case by auto
next
  case (Fun x1a x2)
  show ?case
    using Fun by (cases x1a, auto) (metis in_set_idx local.Fun(1))+
qed

inductive valid_inits for inits v m where
  "valid_inits inits v m"
if
  "\<And>a lb q t lb' q' p. (lb, q, t) \<in> inits
   \<Longrightarrow> v (lb, IA.IntT) = IA.Int lb'
   \<Longrightarrow> v (q, IA.IntT) = IA.Int q'
   \<Longrightarrow> a = lb' + int (len_of t) * p
   \<Longrightarrow> p \<ge> 0
   \<Longrightarrow> p < q'
   \<Longrightarrow> valid_load a t m"

inductive valid_mem for as m v where
  "valid_mem as m v"
if
  "valid_allocs (allocs as) v m"
  "valid_pointers (pointers as) v m"
  "valid_inits (inits as) v m"

lemma valid_pointers_mem_unchanged_intro:
  assumes
    "valid_pointers ps v\<^sub>1 m"
    "\<forall>a lt x. ps a = Some (lt, x) \<longrightarrow> v\<^sub>1 (a, IA.IntT) = v\<^sub>2 (a, IA.IntT) \<and> IA.eval x v\<^sub>1 = IA.eval x v\<^sub>2"
  shows
    "valid_pointers ps v\<^sub>2 m"
  using assms unfolding valid_pointers.simps by (auto)

inductive represents_frame for f as v where
  "represents_frame f as v"
  if
  "frame.pos f = abstract_state.pos as"
  "same_stack_names (frame.stack f) (abstract_state.stack as)"
  "IA.assignment v"
  "valid_var_mapping (frame.stack f) (abstract_state.stack as) v"
  "IA.satisfies v (kb as)"
  "valid_mem as (mem f) v"

inductive represents_state for fs as v where
  "represents_state fs as v"
if
  "frames fs \<noteq> []"
  "represents_frame (hd (frames fs)) as v"
  "length (frames fs) = 1"

lemmas represents_simps = represents_state.simps represents_frame.simps

end (* context ll_mem_funs_extra *)

inductive as_mem_unchanged where
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"
if
  "allocs as\<^sub>2 = allocs as\<^sub>1"
  "pointers as\<^sub>2 = pointers as\<^sub>1"
  "inits as\<^sub>2 = inits as\<^sub>1"

lemma img_fst_snd_triple: "(a,b,c) \<in> S \<Longrightarrow> b \<in> fst ` snd ` S"
  by blast

lemma (in ll_mem_funs_extra) valid_mem_as_mem_unchanged:
  assumes
    "as_mem_unchanged as\<^sub>1 as\<^sub>2"
    "valid_mem as\<^sub>1 (mem f) v\<^sub>1"
    "\<And>a. a \<in> all_sym_vars as\<^sub>1 \<Longrightarrow> v\<^sub>2 (a, IA.IntT) = v\<^sub>1 (a, IA.IntT)"
    "IA.assignment v\<^sub>2"
  shows
    "valid_mem as\<^sub>2 (mem f) v\<^sub>2"
proof -
  have a:  "IA.has_type x IA.IntT" if "pointers as\<^sub>2 a = Some (lt, x)" for a lt x
    using assms that unfolding as_mem_unchanged.simps valid_mem.simps valid_pointers.simps
    by auto
  have b: "valid_load_with_value a' lt x' (mem f)"
    if "pointers as\<^sub>2 a = Some (lt, x)" "v\<^sub>2 (a, IA.IntT) = IA.Int a'" "\<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = IA.Int x'" for a lt x a' x'
  proof -
    have 1: "pointers as\<^sub>1 a = Some (lt, x)" "v\<^sub>1 (a, IA.IntT) = v\<^sub>2 (a, IA.IntT)"
      using that assms by (auto simp add: all_sym_vars_def as_mem_unchanged.simps) (metis domI)
    have 2: "IA.has_type x IA.IntT"
      using that a by auto
    have 3:"(w,t) \<in> vars_term x \<Longrightarrow> t = IA.IntT" for w t
      using 2 IA.has_type_IntT by (fastforce)
    have 4: "fst ` vars_term x \<subseteq> all_sym_vars as\<^sub>1"
      using 1 unfolding all_sym_vars_def by auto (metis img_fst prod.sel(2) ranI)
    have 5: "\<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>2 = \<lbrakk>x\<rbrakk>\<^sub>I\<^sub>A v\<^sub>1"
      using assms 4 3 by (intro IA.eval_same_vars) fast
    show ?thesis
      using that 1 5 assms unfolding valid_mem.simps valid_pointers.simps by auto
  qed
  have "valid_pointers (pointers as\<^sub>2) v\<^sub>2 (mem f)"
    using a b by (intro valid_pointers.intros) auto
  then show ?thesis
  using assms unfolding all_sym_vars_def
  by (auto intro!: valid_mem.intros simp add: as_mem_unchanged.simps valid_mem.simps valid_inits.simps
     valid_allocs.simps valid_pointers.simps split: prod.splits)
       (use img_fst img_fst_snd_triple domI img_snd ranI in metis)+
qed

fun encode_int_var where
  "encode_int_var v = (Var (v, IA.IntT))"

fun encode_int_const where
  "encode_int_const i = Fun (IA.ConstF i) []"

fun encode_sig :: "IA.sig \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.formula" where
  "encode_sig s e\<^sub>1 e\<^sub>2 = Atom (Fun s [e\<^sub>1, e\<^sub>2])"

fun encode_eq :: "_ IA.exp \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.formula" where
  "encode_eq e\<^sub>1 e\<^sub>2 = encode_sig IA.EqF e\<^sub>1 e\<^sub>2"

fun encode_arit where
  "encode_arit f xs = Fun (f (length xs)) xs"

fun encode_binop :: "binop_instruction \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.exp" where
  "encode_binop Mul t\<^sub>1 t\<^sub>2 = encode_arit IA.ProdF [t\<^sub>1, t\<^sub>2]"
| "encode_binop Add t\<^sub>1 t\<^sub>2 = encode_arit IA.SumF [t\<^sub>1, t\<^sub>2]"
| "encode_binop Sub t\<^sub>1 t\<^sub>2 =
      Fun (IA.SumF 2) [t\<^sub>1, Fun (IA.ProdF 2) [Fun (IA.ConstF (-1)) [], t\<^sub>2]]"
| "encode_binop Xor t\<^sub>1 t\<^sub>2 = undefined" (* xor is not supported *)

fun encode_binop_formula :: "binop_instruction \<Rightarrow> _ \<Rightarrow>  _ IA.exp \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.formula" where
  "encode_binop_formula Xor _ _ _ = True\<^sub>f"
| "encode_binop_formula f v\<^sub>n t\<^sub>1 t\<^sub>2 = encode_eq (encode_int_var v\<^sub>n) (encode_binop f t\<^sub>1 t\<^sub>2)"

fun encode_pred :: "integerPredicate \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.exp \<Rightarrow> _ IA.formula" where
  "encode_pred LLVM_Syntax.SLT t\<^sub>1 t\<^sub>2 = encode_sig IA.LessF t\<^sub>1 t\<^sub>2"
| "encode_pred LLVM_Syntax.SGT t\<^sub>1 t\<^sub>2 = encode_sig IA.LessF t\<^sub>2 t\<^sub>1"
| "encode_pred LLVM_Syntax.EQ t\<^sub>1 t\<^sub>2 = encode_sig IA.EqF t\<^sub>1 t\<^sub>2"
| "encode_pred LLVM_Syntax.SLE t\<^sub>1 t\<^sub>2 = encode_sig IA.LeF t\<^sub>1 t\<^sub>2"
| "encode_pred LLVM_Syntax.SGE t\<^sub>1 t\<^sub>2 = encode_sig IA.LeF t\<^sub>2 t\<^sub>1"
| "encode_pred LLVM_Syntax.NE t\<^sub>1 t\<^sub>2 = NegAtom (Fun IA.EqF [t\<^sub>1, t\<^sub>2])"

fun (in ll_mem_funs_extra) encode_alloc where                   
  "encode_alloc vlb vub te\<^sub>l ll_type =
     (let len = encode_int_const (int (len_of ll_type)) in
     encode_eq (encode_int_var vub)
               (Fun (IA.SumF 2) [encode_int_var vlb, Fun (IA.ProdF 2) [te\<^sub>l, len]]))"

fun operand_value :: "'v abstract_state \<Rightarrow> operand \<Rightarrow> (llvm_type \<times> 'v IA.exp) option" where
  "operand_value as (LocalReference n) = (Abstract_State.stack as) n"
| "operand_value as (ConstantOperand (IntConstant l i)) = Some (IntType l, encode_int_const i)"

lemma operand_value_cases: "operand_value as x =
  (case x of
     LocalReference n \<Rightarrow> (Abstract_State.stack as) n
   | ConstantOperand (IntConstant l i) \<Rightarrow> Some (IntType l, encode_int_const i))"
  by (auto split: operand.splits llvm_constant.splits)

definition is_Int_Var where
  "is_Int_Var te = (case te of Var (_, IA.IntT) \<Rightarrow> True
                          | _ \<Rightarrow> False)"

definition is_Const where
  "is_Const te = (case te of Fun (IA.ConstF _) [] \<Rightarrow> True
                          | _ \<Rightarrow> False)"

inductive update_as_var for as\<^sub>1 as\<^sub>2 :: "'v abstract_state" and n t v\<^sub>n \<phi> where
  "update_as_var as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi>"
  if
  "v\<^sub>n \<notin> all_sym_vars as\<^sub>1"
  "Abstract_State.stack as\<^sub>2 = ((Abstract_State.stack as\<^sub>1)(n \<mapsto> (t, encode_int_var v\<^sub>n)))"
  "IA.implies (kb as\<^sub>1 \<and>\<^sub>f \<phi>) (kb as\<^sub>2)"

inductive update_as_term for as\<^sub>1 as\<^sub>2 :: "'v abstract_state" and n t te\<^sub>n \<phi> where
  "update_as_term as\<^sub>1 as\<^sub>2 n t te\<^sub>n \<phi>"
if
  "Abstract_State.stack as\<^sub>2 = ((Abstract_State.stack as\<^sub>1)(n \<mapsto> (t, te\<^sub>n)))"
  "IA.implies (kb as\<^sub>1) (kb as\<^sub>2)"
  "IA.implies (kb as\<^sub>1) \<phi>"

lemma operand_value_fresh:
  assumes
    "operand_value as\<^sub>1 op = Some (t, lv)" "v\<^sub>n \<notin> all_sym_vars as\<^sub>1"
  shows
    "(v\<^sub>n, tt) \<notin> vars_term lv"
proof (cases op)
  case (LocalReference n)
  then show ?thesis using assms ranI[of "abstract_state.stack as\<^sub>1"]
    by (auto  simp add: all_sym_vars_def image_def)
    (metis (mono_tags) fst_conv mem_Collect_eq snd_conv)
next
  case (ConstantOperand x2)
  then show ?thesis using assms by (cases x2, auto intro: llvm_constant.exhaust)
qed

lemma ssn_update:
  assumes
    "update_as_var as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi>"
    "same_stack_names s (Abstract_State.stack as\<^sub>1)"
    "s' = Mapping.update n x s"
  shows "same_stack_names s' (Abstract_State.stack as\<^sub>2)"
  using assms unfolding same_stack_names.simps
  by (auto simp add: lookup_update' elim: update_as_var.induct)

lemma vvm_non_update_stack:
  assumes
    "valid_var_mapping s (Abstract_State.stack as\<^sub>1) v"
    "v' = v ((v\<^sub>m, IA.IntT) := IA.Int i)"
    "v\<^sub>m \<notin> all_sym_vars as\<^sub>1"
 shows "valid_var_mapping s (Abstract_State.stack as\<^sub>1) v'"
    unfolding valid_var_mapping.simps using operand_value_fresh assms ranI[of "abstract_state.stack as\<^sub>1"]
    by (auto simp add: Mapping.lookup_update Mapping.lookup_update' valid_var_mapping.simps
         all_sym_vars_def)
     (metis IA.eval_with_fresh_var img_fst snd_conv)

lemma vvm_update:
  assumes
    "valid_var_mapping s (abstract_state.stack as\<^sub>1) v"
    "update_as_var as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi>"
    "v' = v ((v\<^sub>n, IA.IntT) := IA.Int i)"
    "s' = Mapping.update n y s"
    "ll_typeof y = t"
    "stack_value_to_int y = i"
 shows "valid_var_mapping s' (abstract_state.stack as\<^sub>2) v'"
proof -
  show ?thesis
    unfolding valid_var_mapping.simps using assms ranI[of "abstract_state.stack as\<^sub>1"]
    by(auto simp add: Mapping.lookup_update Mapping.lookup_update' valid_var_mapping.simps
        update_as_var.simps all_sym_vars_def )
    (metis IA.eval_with_fresh_var[of _ _ v] img_fst sndI)
qed

definition type_int_to_stack_value where
  "type_int_to_stack_value t i = (case t of IntType l \<Rightarrow> IntegerValue l i
                                          | PointerType t \<Rightarrow> Pointer t i)"

lemma operand_value_vvm_ssn:
  assumes op: "operand_value as op = Some (t, lvt)"
    and val: "valid_var_mapping (frame.stack f) (abstract_state.stack as) v"
    and ssn: "same_stack_names (frame.stack f) (abstract_state.stack as)"
  shows
    "IA.to_int (IA.eval lvt v) = i \<Longrightarrow> small_step.operand_value f op = Inr (type_int_to_stack_value t i)"
    "small_step.operand_value f op = Inr (type_int_to_stack_value t i) \<Longrightarrow> (IA.eval lvt v) = IA.Int i"
proof -
  have "(IA.to_int (IA.eval lvt v) = i \<longrightarrow> small_step.operand_value f op = Inr (type_int_to_stack_value t i))
 \<and> (small_step.operand_value f op = Inr (type_int_to_stack_value t i) \<longrightarrow> (IA.eval lvt v) = IA.Int i)"
  proof (cases op)
    case (ConstantOperand c)
    then show ?thesis using op
      by (cases c) (auto simp add: small_step.operand_value.simps type_int_to_stack_value_def)
  next
    case (LocalReference n)
    have 1: "IA.eval lvt v = IA.Int i"
      if "small_step.operand_value f op = Inr (type_int_to_stack_value t i)"
      using LocalReference op that val[unfolded valid_var_mapping.simps]
      by (auto simp: small_step.operand_value.simps type_int_to_stack_value_def option_to_sum_def
          split: llvm_type.splits option.splits)
    have 2: "small_step.operand_value f op = Inr (type_int_to_stack_value t i)"
      if "IA.to_int (IA.eval lvt v) = i"
    proof -
      have lvt: "abstract_state.stack as n = Some (t, lvt)"
        using LocalReference op by auto
      obtain iv where iv: "Mapping.lookup (frame.stack f) n = Some iv"
        using lvt ssn unfolding same_stack_names.simps by blast
      have val':  "Mapping.lookup (frame.stack f) n = Some iv \<Longrightarrow> abstract_state.stack as n = Some (t, lvt)
           \<Longrightarrow> \<lbrakk>lvt\<rbrakk>\<^sub>I\<^sub>A v = IA.Int (stack_value_to_int iv) \<and> t = ll_typeof iv"
        using val[unfolded valid_var_mapping.simps] by auto
      have iv': "iv = (type_int_to_stack_value t i)"
        using LocalReference iv lvt op that val'
        by (cases iv)
          (auto simp: type_int_to_stack_value_def small_step.operand_value.simps
            same_stack_names.simps)
      then show ?thesis
        using iv LocalReference by (auto simp: small_step.operand_value.simps option_to_sum_def)
    qed
    show ?thesis
      using 1 2 by blast
  qed
  then show
    "IA.to_int (IA.eval lvt v) = i \<Longrightarrow> small_step.operand_value f op = Inr (type_int_to_stack_value t i)"
    "small_step.operand_value f op = Inr (type_int_to_stack_value t i) \<Longrightarrow> (IA.eval lvt v) = IA.Int i"
    by blast+
qed

fun new_b_id_pos where
  "new_b_id_pos (fn, _, _) new_b_id = (fn, new_b_id, 0)"


section \<open>Inference Rules\<close>

inductive evalAsInf for prog as\<^sub>1 as\<^sub>2 where
  "evalAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (Binop binop o\<^sub>1 o\<^sub>2)))"
   "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
   "operand_value as\<^sub>1 o\<^sub>1 = Some (IntType l\<^sub>1, te\<^sub>1)"
   "operand_value as\<^sub>1 o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)"
   "l\<^sub>2 = l\<^sub>1"
   "0 < l\<^sub>1"
   "\<phi> = encode_binop_formula binop v\<^sub>n te\<^sub>1 te\<^sub>2"
   "update_as_var as\<^sub>1 as\<^sub>2 n (IntType l\<^sub>1) v\<^sub>n \<phi>"
   "as_mem_unchanged as\<^sub>1 as\<^sub>2"

inductive genAsInf for as\<^sub>1 as\<^sub>2 \<mu> where
  "genAsInf as\<^sub>1 as\<^sub>2 \<mu>"
if
  "abstract_state.pos as\<^sub>1 = abstract_state.pos as\<^sub>2"
  "dom (Abstract_State.stack as\<^sub>1) = dom (Abstract_State.stack as\<^sub>2)"
  "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A rename_vars \<mu> (kb as\<^sub>2)"
  "(\<forall>n t te\<^sub>2. Abstract_State.stack as\<^sub>2 n = Some (t, te\<^sub>2) \<longrightarrow>
                IA.has_type te\<^sub>2 IA.IntT
                \<and> (\<exists>te\<^sub>1. Abstract_State.stack as\<^sub>1 n = Some (t, te\<^sub>1)
                   \<and> kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2)))"
  "(\<forall>(lb, ub) \<in> allocs as\<^sub>2. (\<mu> lb, \<mu> ub) \<in> allocs as\<^sub>1)"
  "(\<forall>v t te\<^sub>2. Abstract_State.pointers as\<^sub>2 v = Some (t, te\<^sub>2) \<longrightarrow>
                IA.has_type te\<^sub>2 IA.IntT
                \<and> (\<exists>te\<^sub>1. Abstract_State.pointers as\<^sub>1 (\<mu> v) = Some (t, te\<^sub>1)
                   \<and> kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq te\<^sub>1 (rename_vars \<mu> te\<^sub>2)))"
  "(\<forall>(lb, q, t) \<in> inits as\<^sub>2. (\<mu> lb, \<mu> q, t) \<in> inits as\<^sub>1)"

inductive (in ll_mem_funs_extra) allocAsInf for prog as\<^sub>1 as\<^sub>2 where
  "allocAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (Alloca lt o\<^sub>1)))"
  "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
  "Some (IntType l\<^sub>1, te\<^sub>1) = (case o\<^sub>1 of None \<Rightarrow> Some (IntType 32, encode_int_const 1) | Some o\<^sub>1 \<Rightarrow> operand_value as\<^sub>1 o\<^sub>1)"
  "0 < l\<^sub>1"
  "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_sig IA.LessF (encode_int_const 0) te\<^sub>1"
  "vub \<notin> all_sym_vars as\<^sub>1"
  "vub \<noteq> vlb"
  "\<phi> = encode_alloc vlb vub te\<^sub>1 lt"
  "update_as_var as\<^sub>1 as\<^sub>2 n (PointerType lt) vlb \<phi>"
  "allocs as\<^sub>2 = allocs as\<^sub>1 \<union> {(vlb, vub)}"
  "pointers as\<^sub>2 = pointers as\<^sub>1"
  "inits as\<^sub>2 = inits as\<^sub>1"

inductive (in ll_mem_funs_extra) proper_store for kb allocs va t where
   "proper_store kb allocs va t"
 if
   "(lb, ub) \<in> allocs"
   "kb \<Longrightarrow>\<^sub>I\<^sub>A encode_sig IA.LeF (encode_int_var lb) va"
   "kb \<Longrightarrow>\<^sub>I\<^sub>A encode_sig IA.LeF ((Fun (IA.SumF 2) [va, encode_int_const (len_of t)])) (encode_int_var ub)"

inductive (in ll_mem_funs_extra) filter_pointers for kb pointers pt term\<^sub>a t where
   "filter_pointers kb pointers pt term\<^sub>a t"
 if
   "\<And>a t' v'. pt a = Some (t', v')
    \<Longrightarrow> pointers a = Some (t', v')
    \<and> (kb \<Longrightarrow>\<^sub>I\<^sub>A (encode_sig IA.LeF (encode_arit IA.SumF [term\<^sub>a, encode_int_const (len_of t)]) (encode_int_var a)
                \<or>\<^sub>f encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var a, encode_int_const (len_of t')]) term\<^sub>a))"

inductive (in ll_mem_funs_extra) filter_inits for kb inits\<^sub>1 inits\<^sub>2 term\<^sub>a tv where
   "filter_inits kb inits\<^sub>1 inits\<^sub>2 term\<^sub>a tv"
 if
   "\<And>lb q t. (lb,q,t) \<in> inits\<^sub>2
    \<Longrightarrow> (lb, q, t) \<in> inits\<^sub>1
      \<and> (kb \<Longrightarrow>\<^sub>I\<^sub>A (encode_sig IA.LeF (encode_arit IA.SumF [term\<^sub>a, encode_int_const (len_of tv)]) (encode_int_var lb)
              \<or>\<^sub>f encode_sig IA.LeF (encode_arit IA.SumF [encode_int_var lb, encode_arit IA.ProdF [encode_int_var q, encode_int_const (len_of t)]]) term\<^sub>a))"

inductive (in ll_mem_funs_extra) storeAsInf for prog as\<^sub>1 as\<^sub>2 where
   "storeAsInf prog as\<^sub>1 as\<^sub>2"
 if
   "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Store t ov (LocalReference na)))"
   "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
   "(Abstract_State.stack as\<^sub>1) na = Some (type\<^sub>a, term\<^sub>a)"
   "term\<^sub>a = encode_int_var v\<^sub>a"
   "operand_value as\<^sub>1 ov = Some (type\<^sub>v, term\<^sub>v)"
   "type\<^sub>a = PointerType type\<^sub>v"
   "t = type\<^sub>v"
   "proper_store (kb as\<^sub>1) (allocs as\<^sub>1) term\<^sub>a type\<^sub>v"
   "IA.implies (kb as\<^sub>1) (kb as\<^sub>2)"
   "filter_pointers (kb as\<^sub>1) (pointers as\<^sub>1) pt term\<^sub>a type\<^sub>v"
   "filter_inits (kb as\<^sub>1) (inits as\<^sub>1) (inits as\<^sub>2) term\<^sub>a type\<^sub>v"
   "pointers as\<^sub>2 = (pt(v\<^sub>a \<mapsto> (type\<^sub>v, term\<^sub>v)))"
   "Abstract_State.stack as\<^sub>2 = Abstract_State.stack as\<^sub>1"
   "allocs as\<^sub>2 = allocs as\<^sub>1"

inductive loadAsInf for prog as\<^sub>1 as\<^sub>2 where
  "loadAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (Load t\<^sub>1 (LocalReference na))))"
  "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
  "Abstract_State.stack as\<^sub>1 na = Some (PointerType t\<^sub>2, term\<^sub>p)"
  "pointers as\<^sub>1 v\<^sub>p' = Some (t\<^sub>3, term\<^sub>v)"
  "t\<^sub>2 = t\<^sub>1"
  "t\<^sub>3 = t\<^sub>1"
  "IA.implies (kb as\<^sub>1) (encode_eq term\<^sub>p (encode_int_var v\<^sub>p'))"
  "update_as_term as\<^sub>1 as\<^sub>2 n t\<^sub>1 term\<^sub>v True\<^sub>f" 
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"

inductive (in ll_mem_funs_extra) loadAsInitsInf for prog as\<^sub>1 as\<^sub>2 where
  "loadAsInitsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (Load t\<^sub>1 (LocalReference na))))"
  "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
  "Abstract_State.stack as\<^sub>1 na = Some (PointerType t\<^sub>2, term\<^sub>p)"
  "(lb,q,t) \<in> inits as\<^sub>1"
  "t\<^sub>1 = t"
  "t\<^sub>2 = t"
  "IA.implies (kb as\<^sub>1)
   (encode_eq term\<^sub>p (encode_arit IA.SumF [encode_int_var lb, encode_arit IA.ProdF [encode_int_var p, encode_int_const (len_of t)]])
    \<and>\<^sub>f encode_sig IA.LessF (encode_int_var p) (encode_int_var q) \<and>\<^sub>f encode_sig IA.LeF (encode_int_const 0) (encode_int_var p))"
  "update_as_var as\<^sub>1 as\<^sub>2 n t\<^sub>1 v\<^sub>n True\<^sub>f"
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"

inductive refineMapping for mapp\<^sub>1 mapp\<^sub>2 knowledge where
  "refineMapping mapp\<^sub>1 mapp\<^sub>2 knowledge"
if
  "\<And>n t\<^sub>1 t\<^sub>2 te\<^sub>1 te\<^sub>2. mapp\<^sub>1 n = Some (t\<^sub>1, te\<^sub>1)
    \<Longrightarrow> mapp\<^sub>2 n = Some (t\<^sub>2, te\<^sub>2)
    \<Longrightarrow> t\<^sub>2 = t\<^sub>1 \<and> IA.has_type te\<^sub>2 IA.IntT \<and> knowledge \<Longrightarrow>\<^sub>I\<^sub>A encode_eq te\<^sub>1 te\<^sub>2"

inductive refineAsInf' for as\<^sub>1 as\<^sub>2 \<phi> where
  "refineAsInf' as\<^sub>1 as\<^sub>2 \<phi>"
if
  "abstract_state.pos as\<^sub>2 = abstract_state.pos as\<^sub>1"
  "dom (abstract_state.stack as\<^sub>2) = dom (abstract_state.stack as\<^sub>1)"
  "dom (abstract_state.pointers as\<^sub>2) \<subseteq> dom (abstract_state.pointers as\<^sub>1)"
  "refineMapping (abstract_state.stack as\<^sub>1) (abstract_state.stack as\<^sub>2) (kb as\<^sub>1 \<and>\<^sub>f \<phi>)"
  "refineMapping (abstract_state.pointers as\<^sub>1) (abstract_state.pointers as\<^sub>2) (kb as\<^sub>1 \<and>\<^sub>f \<phi>)"
  "allocs as\<^sub>2 = allocs as\<^sub>1"
  "inits as\<^sub>2 = inits as\<^sub>1"
  "kb as\<^sub>1 \<and>\<^sub>f \<phi> \<Longrightarrow>\<^sub>I\<^sub>A kb as\<^sub>2"

inductive refineAsInf for as as\<^sub>t as\<^sub>f where
  "refineAsInf as as\<^sub>t as\<^sub>f"
if
  "refineAsInf' as as\<^sub>t \<phi>"
  "refineAsInf' as as\<^sub>f (\<not>\<^sub>f \<phi>)"

inductive phi_abstract' for as\<^sub>1 as\<^sub>2 x ps type_term term\<^sub>x old_b_id where
  "phi_abstract' as\<^sub>1 as\<^sub>2 x ps type_term term\<^sub>x old_b_id"
if "small_step.phi_bid old_b_id ps = Some y\<^sub>x"
  "operand_value as\<^sub>1 y\<^sub>x = Some (type_term, term\<^sub>x)"
  "abstract_state.stack as\<^sub>2 x = Some (type_term, term\<^sub>x)"

inductive phi_abstract where
  "phi_abstract as\<^sub>1 as\<^sub>2 ((x, ps)#xs) ((type_term, term\<^sub>x)#ys) old_b_id"
if "phi_abstract' as\<^sub>1 as\<^sub>2 x ps type_term term\<^sub>x old_b_id"
    "phi_abstract as\<^sub>1 as\<^sub>2 xs ys old_b_id"
  | "phi_abstract as\<^sub>1 as\<^sub>2 [] [] old_b_id"

inductive branchAsInf for prog as\<^sub>1 as\<^sub>2 where
"branchAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Terminator (Br new_b_id))"
  "abstract_state.pos as\<^sub>1 = (f_id, old_b_id, p)"
  "abstract_state.pos as\<^sub>2 = (f_id, new_b_id, length phis_stats)"
  "find_phis prog f_id new_b_id = Inr phis_stats"
  "phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id"
  "(\<forall>x \<in> dom (abstract_state.stack as\<^sub>1).
    x \<notin> (fst ` set phis_stats) \<longrightarrow> abstract_state.stack as\<^sub>2 x = abstract_state.stack as\<^sub>1 x)"
  "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A kb as\<^sub>2"
  "dom (abstract_state.stack as\<^sub>2) = dom (abstract_state.stack as\<^sub>1) \<union> fst ` set phis_stats"
  "distinct (map fst phis_stats)"
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"

(* TODO: It is probably sufficient to check if the operand_value of c is (Fun (IA.ConstF 1) []),
no need to check the equation with the knowledge base *)
inductive condBranchAsInf for prog as\<^sub>1 as\<^sub>2 where
  "condBranchAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Terminator (CondBr c b_id_true b_id_false))"
  "operand_value as\<^sub>1 c = Some (IntType 1, c')"
  "new_b_id = (if b then b_id_true else b_id_false)"
  "b \<Longrightarrow> kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq c' (Fun (IA.ConstF 1) [])"
  "\<not> b \<Longrightarrow> kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A encode_eq c' (Fun (IA.ConstF 0) [])"
  "abstract_state.pos as\<^sub>1 = (f_id, old_b_id, p)"
  "abstract_state.pos as\<^sub>2 = (f_id, new_b_id, length phis_stats)"
  "find_phis prog f_id new_b_id = Inr phis_stats"
  "phi_abstract as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id"
  "kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A kb as\<^sub>2"
  "(\<forall>x \<in> dom (abstract_state.stack as\<^sub>1).
   x \<notin> (fst ` set phis_stats) \<longrightarrow> abstract_state.stack as\<^sub>2 x = abstract_state.stack as\<^sub>1 x)"
  "dom (abstract_state.stack as\<^sub>2) = dom (abstract_state.stack as\<^sub>1) \<union> fst ` set phis_stats"
  "distinct (map fst phis_stats)"
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"


inductive icmpAsInf for prog as\<^sub>1 as\<^sub>2 where
  "icmpAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (Icmp p o\<^sub>1 o\<^sub>2)))"
  "\<phi> = encode_pred p t\<^sub>1 t\<^sub>2"
  "\<chi> = Fun (IA.ConstF (if b then 1 else 0)) []"
  "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
  "operand_value as\<^sub>1 o\<^sub>1 = Some (type\<^sub>1, t\<^sub>1)"
  "operand_value as\<^sub>1 o\<^sub>2 = Some (type\<^sub>2, t\<^sub>2)"
  "type\<^sub>2 = type\<^sub>1"
  "update_as_term as\<^sub>1 as\<^sub>2 n (IntType 1) \<chi> (if b then \<phi> else (\<not>\<^sub>f \<phi>))"
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"

inductive (in ll_mem_funs_extra) gepAsInf for prog as\<^sub>1 as\<^sub>2 where
  "gepAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (GetElementPtr o\<^sub>1 o\<^sub>2)))"
   "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
   "operand_value as\<^sub>1 o\<^sub>1 = Some (PointerType t\<^sub>1, te\<^sub>1)"
   "operand_value as\<^sub>1 o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)"
   "0 < l\<^sub>2"
   "\<phi> = encode_eq (encode_int_var v\<^sub>n)
                 (Fun (IA.SumF 2) [te\<^sub>1, (Fun (IA.ProdF 2) [te\<^sub>2, encode_int_const (len_of t\<^sub>1)])])"
   "update_as_var as\<^sub>1 as\<^sub>2 n (PointerType t\<^sub>1) v\<^sub>n \<phi>"
   "as_mem_unchanged as\<^sub>1 as\<^sub>2"


inductive ptrToIntAsInf for prog as\<^sub>1 as\<^sub>2 where
  "ptrToIntAsInf prog as\<^sub>1 as\<^sub>2"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Instruction (Assignment n (PtrToInt o\<^sub>1 t)))"
  "abstract_state.pos as\<^sub>2 = inc_pos (abstract_state.pos as\<^sub>1)"
  "operand_value as\<^sub>1 o\<^sub>1 = Some (PointerType pt\<^sub>1, te\<^sub>1)"
  "t = IntType l"
  "update_as_term as\<^sub>1 as\<^sub>2 n t te\<^sub>1 True\<^sub>f"
  "as_mem_unchanged as\<^sub>1 as\<^sub>2"

inductive returnAsInf where
  "returnAsInf prog as\<^sub>1"
if
  "find_statement prog (abstract_state.pos as\<^sub>1) = Inr (Terminator (Ret (Some op)))"
  "operand_value as\<^sub>1 op = Some (type\<^sub>1, t\<^sub>1)"


end