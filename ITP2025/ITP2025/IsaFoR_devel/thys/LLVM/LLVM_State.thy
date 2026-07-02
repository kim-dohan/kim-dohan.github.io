theory LLVM_State
  imports LLVM_Syntax
    "HOL-Library.More_List"
    (* TODO: clean up imports *)
    "Certification_Monads.Error_Monad"
begin

section \<open>option, sum helper\<close>

fun nth_option :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_option (_#xs) (Suc n) = nth_option xs n" |
  "nth_option (x#_) 0 = Some x" |
  "nth_option [] _ = None"

lemma nth_option_nth_default: "nth_option ls n = nth_default None (map Some ls) n"
  by (induction ls n rule: nth_option.induct) (auto)

fun option_to_sum :: "'a option \<Rightarrow> 'b \<Rightarrow> 'b + 'a" where
  "option_to_sum (Some x) _ = Inr x"
| "option_to_sum None y = Inl y"


section \<open>LLVM state datatypes\<close>

type_synonym pos = "name \<times> name \<times> nat"
hide_type (open) LLVM_State.pos

datatype stack_value =
  IntegerValue (intLen: nat) (intValue: int)
  | Pointer llvm_type (intValue: int)

fun stack_value_to_int where
  "stack_value_to_int (IntegerValue n i) = i"
| "stack_value_to_int (Pointer lt a) = a"

fun ll_typeof where
  "ll_typeof (IntegerValue n _) = IntType n"
| "ll_typeof (Pointer lt _) = PointerType lt"



(* TODO: stuck is misnomer for undefined behaviour. what would be a better name? *)
datatype stuck = StaticError String.literal |
                 ExternalFunctionCall name |
                 ReturnValue stack_value |
                 Program_Termination |
                 Undefined_Behaviour

type_synonym 'a error = "stuck + 'a"

fun static_error :: "String.literal \<Rightarrow> 'a error" where
  "static_error m = error (StaticError m)"


section \<open>Abstract memory operations\<close>

(* Full state *)
type_synonym stack = "(name, stack_value) mapping"

(*
  TODO: should the constants in the memory be typed
  should I use llvm_constant for this or introduce an extra type?
*)
datatype 'mem frame = Frame (pos : LLVM_State.pos) (stack : "stack") (mem : "'mem")

fun update_stack where "update_stack f (Frame p s m) = Frame p (f s) m"
fun update_pos where "update_pos f (Frame p s m) = Frame (f p) s m"
fun update_mem where "update_mem f (Frame p s m) = Frame p s (f m)"

lemma update_frame_simps [simp]:
  "\<And>f. pos (update_pos f s) = f (pos s)"
  "\<And>f. stack (update_pos f s) = stack s"
  "\<And>f. pos (update_stack f s) = pos s"
  "\<And>f. stack (update_stack f s) = f (stack s)"
  "\<And>f. stack (update_mem f s) = stack s"
  "\<And>f. pos (update_mem f s) = pos s"
  "\<And>f. mem (update_stack f s) = mem s"
  "\<And>f. mem (update_pos f s) = mem s"
  "\<And>f. mem (update_mem f s) = f (mem s)"
  by (cases s, simp)+

datatype 'mem llvm_state = Llvm_state (frames : "'mem frame list")

lemma update_pos_cong:
  assumes "f (pos x) = g (pos y)" "stack x = stack y" "mem x = mem y"
  shows "update_pos f x = update_pos g y"
  using assms by (cases x, cases y, auto)

fun update_frames where "update_frames f (Llvm_state fs) = Llvm_state (f fs)"

lemma frames_simp[simp]: "update_frames f s = Llvm_state (f (frames s))"
  by (cases s)  simp

end