theory LLVM_HS

imports
  LLVM_Checker
  Proof_Checker.Container_Setup (* code setup should be last import *)
begin

code_identifier
  code_module Quasi_Order \<rightharpoonup> (Haskell) Orders
  |  code_module Orderings \<rightharpoonup> (Haskell) Orders
  |  code_module Lattices \<rightharpoonup> (Haskell) Orders
  |  code_module Unique_Factorization \<rightharpoonup> (Haskell) Arith
  |  code_module String \<rightharpoonup> (Haskell) Arith
  |  code_module Norms \<rightharpoonup> (Haskell) Arith
  |  code_module Missing_Ring \<rightharpoonup> (Haskell) Arith
  |  code_module Missing_Lemmas \<rightharpoonup> (Haskell) Arith
  |  code_module Cardinality \<rightharpoonup> (Haskell) Impl
  |  code_module Collection_Order \<rightharpoonup> (Haskell) Impl
  |  code_module Set \<rightharpoonup> (Haskell) Impl
  |  code_module RBT_ext \<rightharpoonup> (Haskell) Impl
  |  code_module RBT_Impl \<rightharpoonup> (Haskell) Impl
  |  code_module List \<rightharpoonup> (Haskell) Impl
  |  code_module RBT_Set2 \<rightharpoonup> (Haskell) Impl
  |  code_module RBT_Comparator_Impl \<rightharpoonup> (Haskell) Impl
  |  code_module Collection_Enum \<rightharpoonup> (Haskell) Impl
  |  code_module RBT_Mapping2 \<rightharpoonup> (Haskell) Impl
  |  code_module Collection_Eq \<rightharpoonup> (Haskell) Impl
  |  code_module DList_Set \<rightharpoonup> (Haskell) Impl
  |  code_module Finite_Set \<rightharpoonup> (Haskell) Impl
  |  code_module Set_Impl \<rightharpoonup> (Haskell) Impl
  |  code_module Mapping_Impl \<rightharpoonup> (Haskell) Mapping
  |  code_module Term \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Term_Impl \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Container_Setup \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Integer_Arithmetic \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Simplex \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Linear_Poly_Maps \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Abstract_Linear_Poly \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Sorted_Algebra \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Formula \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Term_More \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module LTS \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Cooperation_Program \<rightharpoonup> (Haskell) IsaFoRSetup
  |  code_module Array \<rightharpoonup> (Haskell) Impl
  |  code_module Diff_Array \<rightharpoonup> (Haskell) Impl
  |  code_module Impl_Array_Stack \<rightharpoonup> (Haskell) Impl


code_printing
  constant parse_llvm_dummy \<rightharpoonup> (Haskell) "parse'_llvm'_string _"

lemma [code_unfold del, symmetric, code_post del]:
 "x \<in> set xs \<equiv> List.member xs x"
 by(simp add: List.member_def)

lemma [code_unfold del, symmetric, code_post del]:
 "finite \<equiv> Cardinality.finite'" by(simp)

lemma [code_unfold del, symmetric, code_post del]:
 "card \<equiv> Cardinality.card'" by simp


term step_by_step'
term step1
term "showsl (Inr ())"

instantiation llvm_constant :: showl
begin
fun showsl_llvm_constant where
  "showsl_llvm_constant (IntConstant l i) = showsl STR ''Constant i'' \<circ> showsl l \<circ> showsl STR '' '' \<circ> showsl i"

definition "showsl_list (xs :: llvm_constant list) = default_showsl_list showsl xs"

instance ..
end

instantiation stuck :: showl
begin

fun showsl_stuck where
  "showsl_stuck (StaticError s) = showsl STR ''StaticError:  '' \<circ> showsl s"
|   "showsl_stuck (stuck.ExternalFunctionCall f) = showsl STR ''ExternalFunction:  '' \<circ> showsl f"
|   "showsl_stuck (ReturnValue c) = showsl STR ''ReturnValue: '' \<circ> showsl c"
|   "showsl_stuck (Program_Termination) = showsl STR ''Program_Termination''"

definition "showsl_list (xs :: stuck list) = default_showsl_list showsl xs"

instance ..
end

instantiation mapping :: (showl, showl) showl
begin

fun showsl_mapping where
  "showsl_mapping m = showsl (map (\<lambda>x. (x, Mapping.lookup m x)) (Mapping.ordered_keys m))"

definition "showsl_list (xs :: ('a, 'b) mapping list) = default_showsl_list showsl xs"
instance ..
end

instantiation frame :: showl
begin

fun showsl_frame where
  "showsl_frame (Frame p m) = showsl STR ''Frame:\<newline>Pos: '' \<circ> showsl p \<circ> showsl STR ''\<newline>Mapping'' \<circ> showsl m"

definition "showsl_list (xs :: frame list) = default_showsl_list showsl xs"

instance ..
end



instantiation llvm_state :: showl
begin
fun showsl_llvm_state where
  "showsl_llvm_state (Llvm_state s) = showsl STR ''LLVM_State:  '' \<circ> showsl s"

definition "showsl_list (xs :: llvm_state list) = default_showsl_list showsl xs"

instance ..
end

declare step_by_step'.simps [code]

definition run_prog_string where
   "run_prog_string s f = (case run_prog (parse_llvm s) f of Some s \<Rightarrow> showsl s STR '''')"

declare graph'.nodes_def [code]

export_code run_prog_string Function Basic_block Llvm_prog VoidType llvm_termination_checker Parameter llvm_seg_represents_checker llvm_lts_represents_checker in Haskell

end
