theory Ordered_Algebra_Impl
  imports
    Ordered_Algebra
    Auxx.Map_Of
    Certification_Monads.Check_Monad 
    Auxx.Map_Choice
    Show.Shows_Literal
    First_Order_Rewriting.Term_Impl
begin

text \<open>Checking well-formedness:\<close>

type_synonym ('f, 'g) encoder_inter = "(('f \<times> nat) \<times> ('g, nat) term) list"

locale ordered_algebra_impl = ord_algebra where I=I for I :: "'f \<Rightarrow> _" +
  fixes less_eq_term_checker :: "('f,'v) term \<Rightarrow> _"
  assumes "isOK(less_eq_term_checker s t) \<Longrightarrow> s \<le>\<^sub>\<A> t"

locale encoding_impl =
  fixes alist :: "('f :: showl, 'g :: showl) encoder_inter"
    and default_fun :: "nat \<Rightarrow> 'g"
begin

definition "E = curry (fun_of_map_fun (map_of alist) (\<lambda>(f, n). Fun (default_fun n) (map Var [0..<n])))"

sublocale pre_encoding E.

definition "check_encoding \<equiv>
  check_allm (\<lambda>((f,n),t).
    check (vars_term t \<subseteq> {..<n})
    (showsl_lit (STR ''interpretation of '') \<circ> showsl f \<circ> showsl_lit (STR '' arity '') \<circ> showsl n \<circ> showsl_lit (STR '' has extra parameter''))
  ) alist"

lemma check_encoding:
  assumes ok: "isOK check_encoding" shows "encoding E"
  apply (unfold_locales)
  apply (unfold atomize_imp curry_def)
  using ok by (auto simp: check_encoding_def o_def E_def split:option.split elim!:ballE dest:map_of_SomeD)

definition showsl_encoding :: "showsl"
  where
    "showsl_encoding = showsl_sep
      (\<lambda>((f, n), e). showsl f \<circ>
        showsl_list_gen showsl_nat_var (STR '' = '') (STR ''('') (STR '','') (STR '') = '') [0..<n] \<circ>
        showsl_nat_term e)
      showsl_nl
      alist"

end

declare encoding_impl.showsl_encoding_def [code]

declare encoding_impl.E_def [code]
declare encoding_impl.check_encoding_def [code]

end
