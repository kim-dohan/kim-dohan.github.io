theory LLVM_Step
  imports
    Misc_Aux
    LLVM_State
    "HOL-Library.Word"
    LLVM_Memory_Axioms
begin

type_synonym 'a error = "stuck + 'a"

definition option_to_sum :: "'a option \<Rightarrow> 'b \<Rightarrow> 'b + 'a" where
  "option_to_sum x y = (case x of (Some x) \<Rightarrow> Inr x | None \<Rightarrow> Inl y)"

fun static_error :: "String.literal \<Rightarrow> 'a error" where
  "static_error m = error (StaticError m)"

fun inc_pos where
  "inc_pos (fn, bn, n) = (fn, bn, Suc n)"

fun option_to_error :: "'a option \<Rightarrow> String.literal \<Rightarrow> 'a error" where
  "option_to_error x m = option_to_sum x (StaticError m)"

lemma option_to_error: "option_to_error x s = Inr y \<longleftrightarrow> x = Some y"
  by (auto simp add: option_to_sum_def split: option.splits)

datatype action = Instruction "instruction" | Terminator "terminator"

fun blocks :: "llvm_fun \<Rightarrow> basic_block list" where
  "blocks f = hd_blocks f # tl_blocks f"

fun find_fun :: "llvm_prog \<Rightarrow> name \<Rightarrow> llvm_fun error" where
  "find_fun prog n = (let g = (\<lambda>f. (fun_name f, f));
                          prog' = map_of (map g (funs prog)) in
                          option_to_error (prog' n) (STR ''Cannot find function''))"

fun find_block :: "llvm_fun \<Rightarrow> name \<Rightarrow> basic_block error" where
  "find_block f n = (let g = (\<lambda>b. (name b, b));
                         blocks' = map_of (map g (blocks f)) in
                         option_to_error (blocks' n) STR ''Cannot find block'')"

fun find_fun_block :: "llvm_prog \<Rightarrow> name \<Rightarrow> name \<Rightarrow> basic_block error" where
  "find_fun_block prog fn bn = do {
     f \<leftarrow> find_fun prog fn;
     find_block f bn}"

fun find_action :: "basic_block \<Rightarrow> nat \<Rightarrow> action error" where
  "find_action b n =
    (if n < length (phis b) then static_error STR ''jumping to phi node not possible'' else
      case nth_option (instructions b) (n - length (phis b)) of
        Some i \<Rightarrow> Inr (Instruction i) |
        None \<Rightarrow> Inr (Terminator (terminator b)))"

lemma find_action_terminator:
  "find_action b p = Inr (Terminator t) \<Longrightarrow> terminator b = t"
  by (auto split: option.splits if_splits)

(* TODO: find_statement should return "String.literal \<Rightarrow> String.literal + action"
  and not "action error" *)
fun find_statement :: "llvm_prog \<Rightarrow> LLVM_State.pos \<Rightarrow> action error" where
  "find_statement prog (fn, bn, p) = do {
     b \<leftarrow> find_fun_block prog fn bn;
     find_action b p}"

(* TODO: find_phis should return "String.literal \<Rightarrow> String.literal + action"
  and not "action error" *)
fun find_phis :: "llvm_prog \<Rightarrow> name \<Rightarrow> name \<Rightarrow> phi list error" where
  "find_phis prog fn bn = map_sum id phis (find_fun_block prog fn bn)"

(* XXX: We use unbounded integer arithmetic here!
   For real LLVM semantics we would need bitvector arithmetic
   TODO: proper error handling in case of non matching types *)
fun binop_llvm_constant where
  "binop_llvm_constant g (IntegerValue a n) (IntegerValue a' n') =
     (if a = a' \<and> a > 0 then return (IntegerValue a (g n n')) else
       static_error STR ''Constant have different types'')"
| "binop_llvm_constant _ _ _ = static_error STR ''ill-typed''"

(* TODO: Doesn't not yet capture all ill-typed cases *)
fun select_llvm_constant :: "stack_value \<Rightarrow> stack_value \<Rightarrow> stack_value \<Rightarrow> stack_value error" where
  "select_llvm_constant (IntegerValue a n) o1 o2 = return (if n = 1 then o1 else o2)"
| "select_llvm_constant _ _ _ = static_error STR ''ill-typed''"

declare [[syntax_ambiguity_warning = false]]

(* TODO: add option, ULT vs SLT *)
fun icmp_llvm_constant :: "integerPredicate \<Rightarrow> stack_value \<Rightarrow> stack_value \<Rightarrow> stack_value" where
  "icmp_llvm_constant EQ c1 c2 = (IntegerValue 1 (if intValue c1 = intValue c2 then 1 else 0))" |
  "icmp_llvm_constant NE c1 c2 = (IntegerValue 1 (if intValue c1 \<noteq> intValue c2 then 1 else 0))" |
  "icmp_llvm_constant SLT c1 c2 =
    (IntegerValue 1 (if intValue c1 < intValue c2 then 1 else 0))"  |
  "icmp_llvm_constant SGT c1 c2 =
     (IntegerValue 1 (if intValue c1 > intValue c2 then 1 else 0))" |
  "icmp_llvm_constant SGE c1 c2 =
    (IntegerValue 1 (if intValue c1 \<ge> intValue c2 then 1 else 0))" |
  "icmp_llvm_constant SLE c1 c2 =
    (IntegerValue 1 (if intValue c1 \<le> intValue c2 then 1 else 0))"

(* TODO: is that always a static error or can that be a also a runtime error *)
fun pointer_to_type_address where
  "pointer_to_type_address (Pointer t a) = Inr (t, a)"
| "pointer_to_type_address _ = error (StaticError STR ''Not a pointer'')"

fun get_integer where
  "get_integer (IntegerValue l i) = Inr i"
| "get_integer _ = error (StaticError STR ''Not an integer index'')"

locale small_step =
  ll_mem_funs empty_mem
  for empty_mem :: "'mem"
  +
  fixes
    lc :: llvm_prog and
    ls :: "'mem llvm_state" and
    cf :: "'mem frame" and
    fs :: "'mem frame list"
begin

definition c_pos where "c_pos = pos cf"

definition map_of_funs :: "name \<rightharpoonup> llvm_fun" where
  "map_of_funs = map_of (map (\<lambda>f. (fun_name f, f)) (funs lc))"

fun lookup_block :: "name \<Rightarrow> name \<Rightarrow> basic_block error" where
  "lookup_block f b = (case (case map_of_funs f of Some (llvm_fun.Function _ _ _ c cs) \<Rightarrow>
                         map_of (map (\<lambda>b. (basic_block.name b, b)) (c#cs)) b) of Some b \<Rightarrow> return b)"

fun operand_value :: "operand \<Rightarrow> stack_value error" where
  "operand_value (LocalReference n) = option_to_error (Mapping.lookup (stack cf) n) STR ''Could not find register''" |
  "operand_value (ConstantOperand i) = return (IntegerValue (integerBits i) (integerValue i))"

fun update_stack where
  "update_stack f' n o' = LLVM_State.update_stack (\<lambda>_. Mapping.update n o' (stack f')) f'"

fun update_frame :: "'mem frame \<Rightarrow> 'mem llvm_state error" where
  "update_frame f = return (update_frames (\<lambda>_. f#fs) ls)"

fun operand_binop where
  "operand_binop o1 o2 bo =
    do {
      let m = stack cf;
      o1 \<leftarrow> operand_value o1;
      o2 \<leftarrow> operand_value o2;
      bo o1 o2}"

fun operand_select where
  "operand_select c o1 o2 =
    do {
      let m = stack cf;
      c \<leftarrow> operand_value c;
      o1 \<leftarrow> operand_value o1;
      o2 \<leftarrow> operand_value o2;
      select_llvm_constant c o1 o2}"

fun update_frames_stack where
  "update_frames_stack n v =
    do {o' \<leftarrow> v;
        let f = update_stack cf n o';
        let (nf, nb, p) = pos cf;
        update_frame (update_pos (\<lambda>_. (nf, nb, p + 1)) f)}"

fun zip_parameters where
  "zip_parameters (x#xs) ((Parameter t n)#ps) = do {s \<leftarrow> zip_parameters xs ps; y \<leftarrow> operand_value x; return (Mapping.update n y s)}" |
  "zip_parameters [] [] = return Mapping.empty" |
  "zip_parameters _ _ = static_error STR ''Wrong number of arguments''"

(* TODO: rewrite enter_frame to not do pattern matching again *)
fun enter_frame :: "name \<Rightarrow> operand list \<Rightarrow> 'mem frame error" where
  "enter_frame n os =
    (case (map_of_funs n) of
      Some (Function _ n ps b _) \<Rightarrow> do {
         s \<leftarrow> zip_parameters os ps;
         return (Frame (n, basic_block.name b, 0) s empty_mem)}
     | Some (ExternalFunction _ fn _) \<Rightarrow> error (ExternalFunctionCall fn)
     | None \<Rightarrow> static_error STR ''Undefined function'')"

fun call_function :: "name \<Rightarrow> operand list \<Rightarrow> 'mem llvm_state error" where
  "call_function fn os =
    (case (map_of_funs fn) of
      Some (Function _ fn ps b _) \<Rightarrow> do {
         f \<leftarrow> enter_frame fn os;
         return (update_frames ((\<lambda>_. f#cf#fs)) ls)}
     | Some (ExternalFunction _ fn _) \<Rightarrow> error (ExternalFunctionCall fn)
     | None \<Rightarrow> static_error STR ''Undefined function'')"

term "alloc (frame.mem cf) t (intValue l)"

(* TODO: proper error handling, for example, when the operand is a pointer  *)
fun ss_alloc :: "name \<Rightarrow> llvm_type \<Rightarrow> operand option \<Rightarrow> 'mem frame error" where
  "ss_alloc n t o1 = do {
    l \<leftarrow> case o1 of Some o1' \<Rightarrow> operand_value o1' | None \<Rightarrow> Inr (IntegerValue 32 1);
    l \<leftarrow> case l of IntegerValue _ x \<Rightarrow> Inr x | _ \<Rightarrow> static_error STR ''Undefined function'';
    ((a,ub), mem') \<leftarrow> alloc (frame.mem cf) t l;
    let p = Pointer t a;
    return (LLVM_State.update_stack (\<lambda>s. Mapping.update n p s) ((LLVM_State.update_mem (\<lambda>_. mem') cf)))}"


(* TODO: Pointer type comparision missing *)
fun ss_store :: "llvm_type \<Rightarrow> operand \<Rightarrow> operand \<Rightarrow> stuck + 'mem"   where
  "ss_store t o1 op = do {
    v \<leftarrow> operand_value o1;
    p \<leftarrow> operand_value op;
    (_,a) \<leftarrow> pointer_to_type_address p;
    mem' \<leftarrow> store (frame.mem cf) a t v;
    return mem'}"

fun ss_load :: "name \<Rightarrow> llvm_type \<Rightarrow> operand \<Rightarrow> stuck + 'mem frame" where
  "ss_load n t op = do {
    p \<leftarrow> operand_value op;
    (_,a) \<leftarrow> pointer_to_type_address p;
    v \<leftarrow> load (frame.mem cf) t a;
    return (update_stack cf n v)}"

fun ss_gep :: "name \<Rightarrow> operand \<Rightarrow> operand \<Rightarrow> stuck + 'mem frame" where
  "ss_gep n p i = do {
    p' \<leftarrow> operand_value p;
    i' \<leftarrow> operand_value i;
    offset \<leftarrow> get_integer i';
    (t,a) \<leftarrow> pointer_to_type_address p';
    let p_new = Pointer t (a + int (len_of t) * offset);
    return (update_stack cf n p_new)}"

fun ptr_to_int :: "name \<Rightarrow> operand \<Rightarrow> llvm_type \<Rightarrow> stuck + 'mem frame" where
  "ptr_to_int n o1 t = do {
    p \<leftarrow> operand_value o1;
    (_,a) \<leftarrow> pointer_to_type_address p;
    x \<leftarrow> case t of IntType l \<Rightarrow> Inr (IntegerValue l a) | _ \<Rightarrow> static_error STR ''Ill-typed'';
    return (update_stack cf n x)}"

unbundle bit_operations_syntax

fun binop_instruction :: "binop_instruction \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "binop_instruction Add = (+)"
| "binop_instruction Sub = (-)"
| "binop_instruction Mul = (*)"
| "binop_instruction Xor = (XOR)"

(* TODO: move binop case distinction into extra function *)
fun run_instruction :: "instruction \<Rightarrow> 'mem llvm_state error" where
  "run_instruction i =
    (case i of
      Assignment n i \<Rightarrow>
        (let g = (\<lambda>o1 o2 h. update_frames_stack n (operand_binop o1 o2 h))  in
        (case i of
          Binop binop o1 o2 \<Rightarrow> g o1 o2 (binop_llvm_constant (binop_instruction binop))
        | Select c o1 o2 \<Rightarrow> update_frames_stack n (operand_select c o1 o2)
        | Icmp c o1 o2 \<Rightarrow> g o1 o2 (\<lambda>i1 i2. return (icmp_llvm_constant c i1 i2))
        | R_Call (Call t fn ps) \<Rightarrow> call_function fn ps
        | Alloca t o1 \<Rightarrow> ss_alloc n t o1 \<bind> (\<lambda>f. update_frame (update_pos inc_pos f))
        | Load t o1 \<Rightarrow> ss_load n t o1 \<bind> (\<lambda>f. update_frame (update_pos inc_pos f))
        | GetElementPtr p i \<Rightarrow> ss_gep n p i \<bind> (\<lambda>f. update_frame (update_pos inc_pos f))
        | PtrToInt o1 t \<Rightarrow> ptr_to_int n o1 t \<bind> (\<lambda>f. update_frame (update_pos inc_pos f))))
      | Store t o1 p \<Rightarrow> (ss_store t o1 p \<bind> (\<lambda>m. Inr (update_mem (\<lambda>_. m) cf))) \<bind> (\<lambda>f. update_frame (update_pos inc_pos f))
      | _ \<Rightarrow> static_error STR ''Unnamed operation not yet supported'')"

definition phi_bid where "phi_bid old_b_id ps = map_of (map prod.swap ps) old_b_id"

fun compute_phi where
  "compute_phi old_b_id xs =
     do {x \<leftarrow> option_to_error (phi_bid old_b_id xs) STR ''Previous block not found in phi expression'';
         operand_value x}"

fun compute_phis :: "name \<Rightarrow> phi list \<Rightarrow> _ error" where
  "compute_phis old_b_id ((a, ps)#as) =
     do {
       c \<leftarrow> compute_phi old_b_id ps;
       s \<leftarrow> compute_phis old_b_id as;
       return ((a,c)#s)}" |
  "compute_phis _ [] = return []"

(*
Searches for next block, computes the phis and jumps to the first line after the phis
*)
fun update_bid_frame :: "name \<Rightarrow> 'mem frame error" where
  "update_bid_frame new_b_id = do {
    let (func_id, old_b_id, _) = c_pos;
    \<phi>s \<leftarrow> (find_phis lc func_id new_b_id);
    s \<leftarrow> compute_phis old_b_id \<phi>s;
    let s' = foldr (\<lambda>(k,v). Mapping.update k v) s (stack cf);
    return (update_pos (\<lambda>_. (func_id, new_b_id, length \<phi>s)) (LLVM_State.update_stack (\<lambda>_. s') cf))
}"

fun ret_from_frame :: "action \<Rightarrow> stack_value \<Rightarrow> 'mem frame \<Rightarrow> 'mem frame list \<Rightarrow> 'mem llvm_state error" where
  "ret_from_frame i c1 f' fs' =
    (case i of
      Instruction (Assignment n (R_Call _)) \<Rightarrow> do {let f' = update_pos inc_pos (update_stack f' n c1);
                                                return (update_frames (\<lambda>_. f'#fs') ls)} |
      _ \<Rightarrow> static_error STR ''Illformed position information/program'')"

fun condBr_to_frame where
  "condBr_to_frame (IntegerValue l i) id_t id_f =
    (if l = 1 \<and> i = 1 then Inr id_t
     else if l = 1 \<and> i = 0 then Inr id_f
     else static_error STR ''condBr operand not of type i1'')"
| "condBr_to_frame _ _ _ = static_error STR ''ill-typed''"


(*
NOTE: terminate_frame is kind of a misnomer here
the frame is updated in case of breaks and only terminated in case of return
*)
definition terminate_frame :: "terminator \<Rightarrow> 'mem llvm_state error" where
  "terminate_frame t = do {
    (case t of
      (CondBr c n1 n2) \<Rightarrow>
        do { c \<leftarrow> operand_value c;
             n_id \<leftarrow> condBr_to_frame c n1 n2;
             nf \<leftarrow> update_bid_frame n_id;
             update_frame nf }
     | Br n1 \<Rightarrow> update_bid_frame n1 \<bind> update_frame
     | Ret (Some o1) \<Rightarrow> do {c \<leftarrow> operand_value o1;
                            (f', fs') \<leftarrow> (case fs of [] \<Rightarrow> error (ReturnValue c) | f'# fs' \<Rightarrow> return (f', fs'));
                            i \<leftarrow> find_statement lc (pos f');
                            ret_from_frame i c f' fs'}
     | Ret None \<Rightarrow> static_error STR ''ret void not yet supported'')}"


end (* locale small_step *)

context ll_mem_funs
begin

(* TODO: Is there a shorter way to express small_step.run_instruction load alloc store empty_mem
   without stating load alloc store again? *)
fun step :: "llvm_prog \<Rightarrow> 'mem llvm_state \<Rightarrow> 'mem llvm_state error" where
  "step lf ls = (case frames ls of
      (f#fs) \<Rightarrow>
        (case find_statement lf (pos f) of
          Inr (Terminator t)  \<Rightarrow> small_step.terminate_frame lf ls f fs t |
          Inr (Instruction i) \<Rightarrow> small_step.run_instruction alloc store load len_of empty_mem  lf ls f fs i |
          _ \<Rightarrow> static_error STR ''Can't find next instruction'') |
     [] \<Rightarrow> Inl Program_Termination)"
(* In the last case should I return an error "Non well-formed program" instead of Program_Termination *)

definition step_relation :: "llvm_prog \<Rightarrow> 'mem llvm_state rel" where
  "step_relation prog = { (bef, aft) . step prog bef = Inr aft }"

declare small_step.map_of_funs_def [code]
declare small_step.lookup_block.simps [code]
declare small_step.operand_value.simps [code]
declare small_step.update_stack.simps [code]
declare small_step.update_frame.simps [code]
declare small_step.operand_binop.simps [code]
declare small_step.operand_select.simps [code]
declare small_step.update_frames_stack.simps [code]
declare small_step.zip_parameters.simps [code]
declare small_step.call_function.simps [code]
declare small_step.run_instruction.simps [code]
declare small_step.update_bid_frame.simps [code]
declare small_step.ret_from_frame.simps [code]
declare small_step.terminate_frame_def [code]
declare small_step.phi_bid_def [code]
declare small_step.enter_frame.simps [code]


declare
  small_step.binop_instruction.simps [code]
  small_step.compute_phi.simps [code]
  small_step.compute_phis.simps [code]
  small_step.condBr_to_frame.simps [code]
  small_step.c_pos_def [code]


fun step_by_step :: "nat \<Rightarrow> llvm_prog \<Rightarrow> 'mem llvm_state \<Rightarrow> 'mem llvm_state error" where
  "step_by_step (Suc i) lc ls =
      (case step lc ls of Inr ls \<Rightarrow> step_by_step i lc ls | Inl e \<Rightarrow> Inl e)" |
  "step_by_step 0 lc ls = return ls"

partial_function (option) step_by_step' :: "llvm_prog \<Rightarrow> 'mem llvm_state \<Rightarrow> (stuck + 'mem llvm_state) option" where
  "step_by_step' lc ls =
    (case step lc ls of Inr ls \<Rightarrow> step_by_step' lc ls | Inl e \<Rightarrow> Some (Inl e))"

end (* locale ll_mem_funs' *)

locale successful_step = ll_mem_funs +
  fixes prog cs\<^sub>1 cs\<^sub>2
  assumes step_Inr: "step prog cs\<^sub>1 = Inr cs\<^sub>2"
begin

definition f\<^sub>1 where "f\<^sub>1 = hd (frames cs\<^sub>1)"
definition fs\<^sub>1 where "fs\<^sub>1 = tl (frames cs\<^sub>1)"

lemma frames_cs\<^sub>1: "frames cs\<^sub>1 = f\<^sub>1 # fs\<^sub>1"
  using step_Inr unfolding f\<^sub>1_def fs\<^sub>1_def
  by (auto split: list.splits option.splits)


lemma cs\<^sub>1: "cs\<^sub>1 = Llvm_state (f\<^sub>1 # fs\<^sub>1)"
  using frames_cs\<^sub>1 by (metis llvm_state.collapse)

sublocale small_step alloc store load len_of empty_mem prog cs\<^sub>1 f\<^sub>1 fs\<^sub>1 .

definition c_action where "c_action = projr (find_statement prog (pos f\<^sub>1))"

lemma c_action_def': "find_statement prog (pos f\<^sub>1) = Inr c_action"
  using step_Inr unfolding c_action_def c_pos_def
  by (auto simp add: frames_cs\<^sub>1 split: list.splits option.splits sum.splits)

end (* locale successful_step *)

locale successful_step' = successful_step +
  fixes f_id b_id b_pos
  assumes pos_f\<^sub>1: "pos f\<^sub>1 = (f_id, b_id, b_pos)"
begin

lemma c_pos: "c_pos = (f_id, b_id, b_pos)"
  unfolding c_pos_def pos_f\<^sub>1 by simp

definition c_fun where "c_fun = projr (find_fun prog f_id)"
definition c_block where "c_block = projr (find_block c_fun b_id)"


lemma c_fun_def': "find_fun prog f_id = Inr c_fun"
  using c_action_def' unfolding c_fun_def pos_f\<^sub>1
  by (auto intro!: option.collapse split: Option.bind_splits)

lemma c_block_def': "find_fun_block prog f_id b_id = Inr c_block"
  using c_action_def' unfolding c_fun_def c_block_def pos_f\<^sub>1
  by (auto intro!: option.collapse split: Option.bind_splits sum_bind_splits)

lemma c_block_def'': "find_block c_fun b_id = Inr c_block"
  using c_action_def' unfolding c_fun_def c_block_def pos_f\<^sub>1
  by (auto intro!: option.collapse split: Option.bind_splits sum_bind_splits)

lemma c_find_action: "find_action c_block b_pos = Inr c_action"
  using c_action_def' c_block_def' unfolding pos_f\<^sub>1
  by (auto simp del: find_fun_block.simps)

lemma c_action_Terminator:
  "c_action = Terminator t \<Longrightarrow> step prog cs\<^sub>1 = terminate_frame t"
  by (auto simp add: c_action_def' frames_cs\<^sub>1)

end (* locale successful_step' *)

(* TODO: move to map_of_funs definition or more fitting location *)
lemma map_of_funs_name:
  assumes "small_step.map_of_funs prog n = Some (Function t\<^sub>g g ps\<^sub>g b\<^sub>g bs\<^sub>g)"
  shows "n = g"
  using assms unfolding small_step.map_of_funs_def using map_of_SomeD by fastforce

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


(*
(* TODO: following code only working with proper model for ll_mem_funs' *)

definition run_prog where
  "run_prog p s n =
  (let first_block_in_main = case small_step.map_of_funs p (Name s) of Some (Function _ _ _ b _) \<Rightarrow>
   basic_block.name b in
   step_by_step n p (Llvm_state [Frame (Name s, first_block_in_main, 0) Mapping.empty empty_mem] empty_mem))"


(* TODO: move to own file or find better place *)

instantiation mapping :: (showl, showl) showl
begin

fun showsl_mapping where
  "showsl_mapping m = showsl (map (\<lambda>x. (x, Mapping.lookup m x)) (Mapping.ordered_keys m))"

definition "showsl_list (xs :: ('a, 'b) mapping list) = default_showsl_list showsl xs"
instance ..
end

instantiation stack_value :: showl
begin
fun showsl_stack_value where
  "showsl_stack_value (IntegerValue l i) = showsl STR ''i'' \<circ> showsl l \<circ> showsl STR '' '' \<circ> showsl i"
| "showsl_stack_value (Pointer t a os) = showsl t \<circ> showsl STR '' '' \<circ> showsl a \<circ> showsl STR ''+'' \<circ> showsl os"

definition "showsl_list (xs :: stack_value list) = default_showsl_list showsl xs"

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

instantiation frame :: showl
begin

(* Weird error messages *)
fun showsl_frame where
  "showsl_frame (Frame p s m) = showsl STR ''Frame:\<newline>Pos: '' \<circ> showsl p \<circ> showsl STR ''\<newline>Stack'' \<circ> showsl s
                                \<circ> showsl STR ''\<newline>Heap:'' \<circ> showsl m"

definition "showsl_list (xs :: frame list) = default_showsl_list showsl xs"

instance ..
end



instantiation llvm_state :: showl 
begin

fun showsl_llvm_state where
  "showsl_llvm_state (Llvm_state s m) = showsl STR ''LLVM_State: '' \<circ> showsl s \<circ>
                                        showsl STR ''\<newline>Global Heap: '' \<circ> showsl m"

definition "showsl_list (xs :: llvm_state list) = default_showsl_list showsl xs"

instance ..
end

*)

end
