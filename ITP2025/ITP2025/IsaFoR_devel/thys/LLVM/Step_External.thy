theory Step_External
imports LLVM_Step
begin

context small_step
begin

inductive assign_unknown_value for n s' where
  "assign_unknown_value n s'"
if "s' = update_frames_stack n (Inr c)"

definition call_external_function :: "name \<Rightarrow> operand list \<Rightarrow> name \<Rightarrow> llvm_state error \<Rightarrow> bool" where
  "call_external_function fn os n s' =
    (case (map_of_funs fn) of
      Some (ExternalFunction _ fn ps) \<Rightarrow>
        (case (zip_parameters os ps) of Inr _ \<Rightarrow> assign_unknown_value n s'
                                      | Inl es \<Rightarrow> (s' = Inl es))
     | _ \<Rightarrow> s' = call_function fn os)"

end (* context small_step *)

end