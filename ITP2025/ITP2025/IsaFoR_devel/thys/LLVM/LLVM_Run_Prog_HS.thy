theory LLVM_Run_Prog_HS

imports
  LLVM_Step
  LLVM_Parser
  (* Proof_Checker.Container_Setup (* code setup should be last import *) *)
  Containers.Containers
  Native_Word.Bits_Integer
begin

derive ccompare name llvm_constant operand
derive (no) cenum "name"
derive (eq) ceq name operand
derive (rbt) set_impl name
derive (rbt) mapping_impl name

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
  |  code_module LLVM_Step \<rightharpoonup> (Haskell) LLVM_Run_Prog_HS



code_printing
  constant parse_llvm_dummy \<rightharpoonup> (Haskell) "parse'_llvm'_string _"

lemma [code_unfold del, symmetric, code_post del]:
 "x \<in> set xs \<equiv> List.member xs x"
 by(simp add: List.member_def)

lemma [code_unfold del, symmetric, code_post del]:
 "finite \<equiv> Cardinality.finite'" by(simp)

lemma [code_unfold del, symmetric, code_post del]:
 "card \<equiv> Cardinality.card'" by simp

declare step_by_step'.simps [code]

definition run_prog_string where
   "run_prog_string n s f = showsl (run_prog (parse_llvm s) f (nat_of_integer n)) STR ''''"


export_code open run_prog_string nat_of_integer int_of_integer in Haskell
(*  file "/Users/mhaslbeck/Projects/llvm/isabelle/hs/src/isabelle_export" *)

end
