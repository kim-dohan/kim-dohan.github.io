(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Transfer Rules for Multihole Contexts\<close>

theory Multihole_Context_Transfer
  imports First_Order_Rewriting.Multihole_Context
begin

text \<open>Transfer-relation between multihole contexts and terms.\<close>
definition [iff]: "rel_term_mctxt t C \<longleftrightarrow> num_holes C = 0 \<and> t = term_of_mctxt C"
definition [iff]: "rel_mctxt_term C t \<longleftrightarrow> C = mctxt_of_term t"

lemma Domainp_rel_mctxt_term [transfer_domain_rule]:
  "Domainp rel_mctxt_term = (\<lambda>C. num_holes C = 0)"
  unfolding rel_mctxt_term_def [abs_def] Domainp_iff [abs_def]
  by (rule ext) (auto, metis mctxt_of_term_term_of_mctxt_id)

lemma Domainp_rel_term_mctxt [transfer_domain_rule]:
  "Domainp rel_term_mctxt = (\<lambda>t. True)"
  unfolding rel_term_mctxt_def [abs_def] Domainp_iff [abs_def]
  by (rule ext) (metis num_holes_mctxt_of_term term_of_mctxt_mctxt_of_term_id)

context
  includes lifting_syntax
begin

lemma bi_unique_rel_mctxt_term [transfer_rule]:
  "bi_unique rel_mctxt_term"
  by (simp add: bi_unique_def) (metis term_of_mctxt_mctxt_of_term_id)

lemma bi_unique_rel_term_mctxt [transfer_rule]:
  "bi_unique rel_term_mctxt"
  by (simp add: bi_unique_def) (metis mctxt_of_term_term_of_mctxt_id)

lemma right_total_rel_mctxt_term [transfer_rule]:
  "right_total rel_mctxt_term"
  by (simp add: right_total_def)

lemma left_total_rel_term_mctxt [transfer_rule]:
  "left_total rel_term_mctxt"
  by (simp add: left_total_def) (metis num_holes_mctxt_of_term term_of_mctxt_mctxt_of_term_id)

lemma Var_transfer [transfer_rule]:
  "((=) ===> rel_term_mctxt) Var MVar"
  by (auto simp: rel_fun_def)

lemma Fun_transfer [transfer_rule]:
  "((=) ===> (list_all2 rel_term_mctxt ===> rel_term_mctxt)) Fun MFun"
proof (intro rel_funI)
  fix f g :: 'f and ts and Cs :: "('f, 'v) mctxt list"
  assume "list_all2 rel_term_mctxt ts Cs" and "f = g"
  then show "rel_term_mctxt (Fun f ts) (MFun g Cs)"
    by (induct ts Cs) simp_all
qed

lemma num_holes_transfer [transfer_rule]:
  "(rel_mctxt_term ===> (=)) num_holes (\<lambda>_. 0)"
 by (simp add: rel_fun_def)

lemma term_of_mctxt_transfer [transfer_rule]:
  "(rel_mctxt_term ===> rel_term_mctxt) term_of_mctxt mctxt_of_term"
  by (simp add: rel_fun_def)

lemma mctxt_of_term_transfer [transfer_rule]:
  "(rel_term_mctxt ===> rel_mctxt_term) mctxt_of_term term_of_mctxt"
  by (simp add: rel_fun_def)

end

end

