(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>Multiset-Extension of Subterm Relation\<close>

theory Subterm_Multiset
imports
  Weighted_Path_Order.Multiset_Extension2
  First_Order_Terms.Term_More
begin

abbreviation suptmulex ("{\<rhd>\<^sub>#}")
where
  "{\<rhd>\<^sub>#} \<equiv> s_mul_ext Id {\<rhd>}"

abbreviation suptmulexeq ("{\<unrhd>\<^sub>#}")
where
  "{\<unrhd>\<^sub>#} \<equiv> ns_mul_ext Id {\<rhd>}"

abbreviation suptmulex_pred (infix "\<rhd>\<^sub>#" 55)
where
  "s \<rhd>\<^sub># t \<equiv> (s, t) \<in> s_mul_ext Id {\<rhd>}"

abbreviation suptmulexeq_pred (infix "\<unrhd>\<^sub>#" 55)
where
  "s \<unrhd>\<^sub># t \<equiv> (s, t) \<in> ns_mul_ext Id {\<rhd>}"

lemma suptmulexeq_refl [simp]:
  "T \<unrhd>\<^sub># T"
  by (auto simp: locally_refl_def ns_mul_ext_refl_local)


lemma args_in_suptmulex:
  "{#Fun f ts#} \<rhd>\<^sub># mset ts"
by (intro all_s_s_mul_ext) (auto simp: in_multiset_in_set)

lemma args_in_suptmulexeq:
  "{#Fun f ts#} \<unrhd>\<^sub># mset ts"
using args_in_suptmulex [of f ts] by (auto simp: ns_mul_ext_Id_eq)

lemma suptmulex_trans:
  assumes "A \<rhd>\<^sub># B" and "B \<rhd>\<^sub># C"
  shows "A \<rhd>\<^sub># C"
by (rule s_mul_ext_trans [OF _ _ _ _ _ assms])
   (auto simp: trans_def refl_on_def compatible_l_def compatible_r_def dest: supt_trans)

lemma suptmulexeq_trans:
  assumes "A \<unrhd>\<^sub># B" and "B \<unrhd>\<^sub># C"
  shows "A \<unrhd>\<^sub># C"
using assms by (auto simp: ns_mul_ext_Id_eq dest: suptmulex_trans)

lemma supt_order_pair: "order_pair {\<rhd>} Id"
by (standard) (auto simp: refl_on_def trans_def dest: supt_trans)

lemma SN_suptmulex:
  "SN {\<rhd>\<^sub>#}"
proof -
  { fix M :: "('f, 'v) term multiset"
    have "SN_on {\<rhd>\<^sub>#} {M}"
      using SN_supt by (intro SN_s_mul_ext_strong [OF supt_order_pair]) (auto simp: SN_defs) }
  then show ?thesis by (auto simp: SN_defs)
qed

lemma suptmulex_not_refl:
  "(M, M) \<notin> {\<rhd>\<^sub>#}"
using refl_not_SN [of M "{\<rhd>\<^sub>#}"] and SN_suptmulex by blast

lemma suptmulex_eq:
  "{\<rhd>\<^sub>#} = {\<unrhd>\<^sub>#} - Id"
unfolding ns_mul_ext_Id_eq by (auto simp: suptmulex_not_refl)

lemma mult_subt_converse: "(mult {\<lhd>})\<inverse> = {\<rhd>\<^sub>#}"
using mult_s_mul_ext_conv [OF trans_supt] .

lemma trans_subt: "trans {\<lhd>}"
by (simp add: trans_supt)

end
