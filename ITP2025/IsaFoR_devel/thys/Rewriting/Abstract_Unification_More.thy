(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Abstract Unification\<close>

theory Abstract_Unification_More
  imports First_Order_Terms.Abstract_Unification
begin

definition vars_mset_less :: "(('f, 'v) equation multiset \<times> ('f, 'v) equation multiset) set"
where
  "vars_mset_less = {(x, y). vars_mset x \<subset> vars_mset y}"

lemma UNIF_vars_mset_leq:
  assumes "UNIF ss E E'"
  shows "vars_mset E' \<subseteq> vars_mset E"
  using assms by (induct) (auto dest: UNIF1_vars_mset_leq)

lemma finite_compose:
  assumes "\<forall>\<sigma>\<in>set ss. finite (subst_domain \<sigma>)"
  shows "finite (subst_domain (compose ss))"
  using assms by (induct ss) (auto simp: subst_domain_subst_compose)

lemma UNIF1_finite_subst_domain:
  assumes "UNIF1 \<sigma> E E'"
  shows "finite (subst_domain \<sigma>)"
  using assms by (cases) auto

lemma UNIF_finite_subst_domain:
  assumes "UNIF ss E E'"
  shows "\<forall>\<sigma>\<in>set ss. finite (subst_domain \<sigma>)"
  using assms by (induct) (auto intro: UNIF1_finite_subst_domain)

text \<open>The inference rules generate substitutions with finite domain.\<close>
lemma UNIF_finite_subst_domain_compose:
  assumes "UNIF ss E E'"
  shows "finite (subst_domain (compose ss))"
  using UNIF_finite_subst_domain [OF assms] and finite_compose by blast

lemma UNIF_subst_domain_Int:
  assumes "UNIF ss E E'"
  shows "subst_domain (compose ss) \<inter> vars_mset E' = {}"
  using assms
  by (induct)
     (auto dest!: UNIF1_subst_domain_Int UNIF_vars_mset_leq simp: subst_domain_subst_compose)

end
