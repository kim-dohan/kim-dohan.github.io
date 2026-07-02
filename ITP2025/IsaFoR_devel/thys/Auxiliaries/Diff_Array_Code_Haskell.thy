text \<open>This file overwrites the efficient code setup for mutable arrays,
  since it does not compile with Isabelle 2016-1 and ghc 8.
  The presented code just uses the plain definitions, i.e., list access.

  WARNING: This file might destroy the code-export for other languages than Haskell.\<close>

theory Diff_Array_Code_Haskell
imports 
  Collections.Diff_Array
begin
  
code_printing code_module "Array" \<rightharpoonup> (Haskell) 
\<open>module Array where {
data Array a = Array [a];
}
\<close>    
  
code_printing type_constructor array \<rightharpoonup>
  (Haskell) "Array.Array/ _"

code_printing constant Array \<rightharpoonup> (Haskell) "Array.Array"
  
lemma [code, code del]: "new_array = new_array" by simp
declare new_array_def[code]

lemma [code, code del]: "array_length = array_length" by simp
declare array_length.simps[code]

lemma [code, code del]: "array_get = array_get" by simp
declare array_get.simps[code]

lemma [code, code del]: "array_set = array_set" by simp
declare array_set.simps[code]

lemma [code, code del]: "array_shrink = array_shrink" by simp
declare array_shrink.simps[code]
  
lemma [code, code del]: "array_grow = array_grow" by simp
declare array_grow.simps[code]
  
lemma [code_unfold]: "array_of_list = Array" unfolding array_of_list_def ..
end  
