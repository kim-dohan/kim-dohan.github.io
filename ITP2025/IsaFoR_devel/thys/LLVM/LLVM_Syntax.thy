theory LLVM_Syntax
  imports
  Deriving.Compare_Order_Instances
  "HOL-Library.Mapping"
  Show.Show
  Show.Shows_Literal
  "HOL-Library.Cardinality"
begin

(* Based on Haskell package llvm-hs-pure
   <http://hackage.haskell.org/package/llvm-hs-pure-6.2.1/docs/LLVM-AST.html> *)

(* We have to watchout for collisions. What if we have "Name ''%1''"? *)
datatype name = Name String.literal | UnName nat

instantiation name :: linorder
begin

fun less_name :: "name \<Rightarrow> name \<Rightarrow> bool" where
  "less_name (Name s) (Name s') = (s < s')"
|  "less_name (Name s) (UnName n) = True"
|  "less_name (UnName n) (Name s) = False"
|  "less_name (UnName n) (UnName n') = (n < n')"

definition less_eq_name :: "name \<Rightarrow> name \<Rightarrow> bool" where
  "less_eq_name x y = (x = y \<or> less x y)"

instance
proof -
  have a: "x < x \<Longrightarrow> False" for x :: name
    by (cases x, auto)
  have b: "x < y \<Longrightarrow> y < x \<Longrightarrow> False" for x y :: name
    by (cases x; cases y; auto)
  have c: "\<not> x < z \<Longrightarrow> x < y \<Longrightarrow> y < z \<Longrightarrow> x = z" for x y z :: name
    by (cases x; cases y; cases z; auto)
  have d: "x < y \<Longrightarrow> y < x \<Longrightarrow> x = y" for x y :: name
    by (cases x; cases y; auto)
  have e: "x \<noteq> y \<Longrightarrow> \<not> x < y \<Longrightarrow> \<not> y < x \<Longrightarrow> False" for x y :: name
    by (cases x; cases y; auto)
  show "OFCLASS(name, linorder_class)"
    by (intro_classes) (auto intro: a b c d e simp add: less_eq_name_def)
qed

end

derive (linorder) compare_order name

instantiation name :: showl
begin
fun showsl_name where
  "showsl_name (Name s) = showsl_lit (STR ''Name '') \<circ> (showsl_lit s)"
| "showsl_name (UnName n) = showsl_lit (STR ''Name '') \<circ> (showsl n)"
definition "showsl_list (xs :: name list) = default_showsl_list showsl xs"
instance ..
end


datatype 'a named = Named (named_name: name) (named_instruction: 'a) | Do (named_instruction: 'a)

(* RELEVANT LEMMAS AND FUNCTION *)

(* TODO:
What would be the best way to define the type here?
* use a nat and use mod in all operations
* IntType1 "1 word", IntType2 "2 word"
* is there a mix between the two possible

The first basic block in a function is special in two ways: it is immediately executed on entrance
to the function, and it is not allowed to have predecessor basic blocks (i.e. there can not be any
branches to the entry block of a function). Because the block can have no predecessors,
it also cannot have any PHI nodes. Should we encode this with the type system or with a predicate?

Should there be a one to one correspondence between llvm-hs and the isabelle types?

Should the map of registers return llvm_constants?

Bah, this sucks.
*)


datatype llvm_type =
  IntType (integerBits : nat) \<comment> \<open>n-bit integer\<close>
  | PointerType llvm_type

datatype llvm_constant =
  IntConstant (integerBits : nat) (integerValue : int)

datatype operand =
  LocalReference name |
  ConstantOperand llvm_constant

datatype parameter =
  Parameter llvm_type (parameter_name: name)

datatype integerPredicate = SLT | SGT | EQ | SGE | SLE | NE

datatype binop_instruction = Add | Sub | Xor | Mul

datatype call = Call llvm_type name (arguments: "operand list")

(* TODO: Alloca and Store need an extra pointer type *)


datatype r_instruction =
  Binop binop_instruction (operand0: operand) (operand1: operand)
| Select operand (operand0: operand) (operand1: operand)
| Icmp integerPredicate (operand0: operand) (operand1: operand)
| R_Call call
| Alloca llvm_type "operand option"
| Load llvm_type operand
| GetElementPtr operand operand
| PtrToInt operand llvm_type

(* should probably be split into different instruction types *)
datatype instruction =
  Assignment name r_instruction
  | V_Call call
  | Store llvm_type operand operand

datatype terminator =
  Ret (return_operand: "operand option") | (*Ret None = ret void *)
  CondBr (condition: operand) (trueDest: name) (falseDest: name) |
  Br (dest: name)

type_synonym phi = "(name \<times> (operand \<times> name) list)"

datatype basic_block =
  Basic_block
   (name : name)
   (phis : "phi list")
   (instructions : "instruction list")
   (terminator : "terminator")

datatype llvm_fun =
  Function llvm_type (fun_name: name) (params: "parameter list") (hd_blocks: basic_block)
           (tl_blocks: "basic_block list")
  | ExternalFunction llvm_type (fun_name: name) (params: "parameter list")

datatype llvm_prog = Llvm_prog (funs : "llvm_fun list")

instantiation llvm_constant :: showl
begin
fun showsl_llvm_constant where
  "showsl_llvm_constant (IntConstant l i) = showsl STR ''Constant i'' \<circ> showsl l \<circ> showsl STR '' '' \<circ> showsl i"

definition "showsl_list (xs :: llvm_constant list) = default_showsl_list showsl xs"

instance ..
end

instantiation llvm_type :: showl
begin
fun showsl_llvm_type where
  "showsl_llvm_type (IntType l) = showsl STR ''i'' \<circ> showsl l"
| "showsl_llvm_type (PointerType t) = showsl t \<circ> showsl STR ''*''"

definition "showsl_list (xs :: llvm_type list) = default_showsl_list showsl xs"

instance ..
end

lemma infinite_name_UNIV:  "infinite (UNIV :: name set)"
proof -
  have "infinite (range UnName)"
    by (auto simp add: finite_image_iff linorder_injI)
  moreover have "range UnName \<subseteq> UNIV"
    by blast
  ultimately show ?thesis
    using rev_finite_subset by auto
qed

instantiation name :: card_UNIV
begin
definition "card_UNIV = Phantom(name) 0"
definition "finite_UNIV = Phantom(name) False"
instance
  by (intro_classes) (auto simp: finite_UNIV_name_def card_UNIV_name_def infinite_name_UNIV)
end


end
