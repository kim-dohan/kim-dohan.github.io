theory LLVM_Memory_Axioms
  imports
    LLVM_Syntax
    LLVM_State
begin

locale ll_mem_funs =
  fixes empty_mem :: "'mem"
  fixes alloc :: "'mem \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + ((int \<times> int) \<times> 'mem)"
  fixes store :: "'mem \<Rightarrow> int \<Rightarrow> llvm_type \<Rightarrow> stack_value \<Rightarrow> stuck + 'mem"
  fixes load :: "'mem \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + stack_value"
  fixes len_of :: "llvm_type \<Rightarrow> nat"

locale ll_mem_funs_extra = ll_mem_funs empty_mem 
  for empty_mem :: "'mem" +
  fixes bounds :: "'mem \<Rightarrow> int \<Rightarrow> (int \<times> int) option"

locale ll_mem = ll_mem_funs_extra _ _ _ _  +
  assumes S1: "len_of t > 0"
  assumes S2: "l > 0 \<Longrightarrow> isOK (alloc m t l)"
  assumes S3: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> ub - lb = int (len_of t) * l"
  assumes S4: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} \<Longrightarrow> load m' t' a = load m t' a"
  assumes S5: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<in> {lb..<ub} \<Longrightarrow> bounds m' a = Some (lb, ub)"
  assumes S6: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} \<Longrightarrow> bounds m' a = bounds m a"
  assumes S7: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<in> {lb..<ub} \<Longrightarrow> bounds m a = None"
  assumes S8: "bounds m a = Some (lb, ub) \<Longrightarrow> lb \<le> a \<Longrightarrow> a + len_of t \<le> ub \<Longrightarrow> (\<exists>m'. store m a t v = Inr m')"
  assumes S9: "store m a t v = Inr m' \<Longrightarrow> bounds m' = bounds m"
  assumes S10: "store m a t v = Inr m' \<Longrightarrow> a' + (len_of t') \<le> a \<or> a + (len_of t) \<le> a' \<Longrightarrow> load m' t' a' = load m t' a'"
  assumes S11: "store m a t v = Inr m' \<Longrightarrow> load m' t a = Inr v"


end