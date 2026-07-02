(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Multihole_Context_Impl
  imports 
    First_Order_Rewriting.Multihole_Context
    Show.Shows_Literal
begin

fun add_funas_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
where
  "add_funas_mctxt (MFun f Cs) fs = (f, length Cs) # foldr add_funas_mctxt Cs fs" |
  "add_funas_mctxt _ fs = fs"

lemma add_funas_mctxt_funas_mctxt_list_conv [simp]:
  "add_funas_mctxt t fs = funas_mctxt_list t @ fs"
proof (induct t arbitrary: fs)
  case (MFun f Cs)
  then show ?case by (induct Cs) (simp_all)
qed simp_all

lemma add_funas_mctxt_funas_term_list_abs_conv [simp]:
  "add_funas_mctxt = (@) \<circ> funas_mctxt_list"
  by (intro ext) simp

lemma [code]:
  "funas_mctxt_list C = add_funas_mctxt C []"
  by simp_all

text \<open>
  Potentially more efficient operations for multihole contexts. Currently unused.
\<close>

(*pro: no undefined cases*)
fun add_terms :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list"
where
  "add_terms MHole [] = (MHole, [])" |
  "add_terms MHole (t#ts) = (mctxt_of_term t, ts)" |
  "add_terms (MVar x) ts = (MVar x, ts)" |
  "add_terms (MFun f Cs) ts = apfst (MFun f) (fold_map add_terms Cs ts)"

lemma add_term_cap_till_uncap_till_append [simp]:
  "add_terms (cap_till P t) (uncap_till P t @ us) = (mctxt_of_term t, us)"
  by (induct t arbitrary: us) (simp_all add: fold_map_map_conv)

lemmas add_term_cap_till_uncap_till [simp] =
  add_term_cap_till_uncap_till_append [of _ _ "[]", simplified]

definition apply_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term"
where
  "apply_mctxt C ts = term_of_mctxt (fst (add_terms C ts))"

lemma apply_mctxt_simps [simp]:
  "apply_mctxt MHole [t] = t"
  "apply_mctxt (MVar x) ts = Var x"
  "apply_mctxt (MFun f Cs) ts = Fun f (map term_of_mctxt (fst (fold_map add_terms Cs ts)))"
  by  (simp_all add: apply_mctxt_def)

lemma apply_mctxt_cap_till_uncap_till [simp]:
  "apply_mctxt (cap_till P t) (uncap_till P t) = t"
  by (simp add: apply_mctxt_def)

lemma [termination_simp]:
  "sum_list (map num_holes Cs) = Suc 0 \<Longrightarrow>
    size (hd (dropWhile (\<lambda>C. num_holes C = 0) Cs)) < Suc (size_list size Cs)"
  by (induct Cs) auto

fun ctxt_of_mctxt :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) ctxt"
where
  "ctxt_of_mctxt MHole = \<box>" |
  "ctxt_of_mctxt (MFun f Cs) =
    (if num_holes (MFun f Cs) = 1 then
      (let
        ss = takeWhile (\<lambda>C. num_holes C = 0) Cs;
        ts = dropWhile (\<lambda>C. num_holes C = 0) Cs;
        C = hd ts;
        us = tl ts
      in More f (map term_of_mctxt ss) (ctxt_of_mctxt C) (map term_of_mctxt ss))
    else \<box>)"

instantiation mctxt :: (showl, showl) showl
begin
fun showsl_mctxt where
  "showsl_mctxt MHole = showsl_lit (STR ''[]'')" |
  "showsl_mctxt (MVar x) = showsl x" |
  "showsl_mctxt (MFun f Cs) =
    (showsl f \<circ> showsl_list_gen id (STR '''') (STR ''('') (STR '', '') (STR '')'') (map showsl_mctxt Cs))"
definition "showsl_list (xs :: ('a,'b)mctxt list) = default_showsl_list showsl xs"
instance ..
end

end

