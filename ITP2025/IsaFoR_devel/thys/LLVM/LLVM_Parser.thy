theory LLVM_Parser
imports LLVM_Syntax
begin

definition parse_llvm_dummy :: "String.literal \<Rightarrow> llvm_prog" where
  "parse_llvm_dummy x = Code.abort STR ''parse_llvm implementation missing'' undefined"

definition parse_llvm :: "String.literal \<Rightarrow> llvm_prog" where
  "parse_llvm = parse_llvm_dummy"

end
