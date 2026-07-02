(*
Author:  Akihisa Yamada (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Multi_Algebra_Impl
  imports 
    Multi_Algebra 
    Ord.Ordered_Algebra_Impl
begin

locale multi_encoding_impl  =
  fixes alist :: "(('f :: showl \<times> nat) \<times> ('g, nat \<times> nat) term list) list"
    and dim :: nat
    and default_const :: "'g"
begin

definition "E f n k \<equiv>
  case map_of alist (f,n) of Some ts \<Rightarrow>
    if k < dim then ts ! k else Fun default_const []
  | None \<Rightarrow> Fun default_const []"

sublocale pre_multi_encoding E.

definition "check_encoding \<equiv>
  check_allm (\<lambda>((f,n), ts).
  let finfo = showsl_lit (STR ''interpretation of '') \<circ> showsl f \<circ> showsl_lit (STR '' arity '') \<circ> showsl n in
  do {
    check (length ts = dim) (finfo \<circ> showsl_lit (STR '' has dimension '') \<circ> showsl (length ts));
    check_allm (\<lambda>t.
      check_allm (\<lambda>(i,j).
        check (i < n \<and> j < dim) (finfo \<circ> showsl_lit (STR '' has extra parameter '') \<circ> showsl (i,j))
      ) (vars_term_list t)
    ) ts
  }) alist"

lemma check_encoding:
  assumes ok: "isOK check_encoding" shows "multi_encoding E dim"
proof (unfold_locales)
  fix i j f n k
  assume 1: "(i,j) \<in> vars_term (E f n k)"
  show "i < n" "j < dim"
  proof (atomize(full), cases "map_of alist (f,n)")
    case None then show "i < n \<and> j < dim" using 1 by (auto simp: E_def)
  next
    case (Some ts)
    show "i < n \<and> j < dim"
    proof (cases "k < dim")
      case True
      with Some have 2: "E f n k = ts ! k" and 3: "((f,n),ts) \<in> set alist" by (auto simp: E_def map_of_SomeD)
      from ok True 1 show ?thesis
        by (auto simp: 2 check_encoding_def dest!:bspec[OF _ 3] nth_mem[of k] bspec[of "set ts"])
    next
      case False
      with 1 Some show ?thesis by (auto simp: E_def)
    qed
  qed
qed

end

declare multi_encoding_impl.check_encoding_def [code]

end
