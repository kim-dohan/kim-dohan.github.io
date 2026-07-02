(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Dependency_Graph
imports
  Icap
  TRS.Tcap
  Innermost_Usable_Rules
begin

definition
  DG :: "bool \<Rightarrow> bool \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> (('f, 'v)rule \<times> ('f,'v)rule) set"
where
  "DG nfs m P Q R \<equiv> {((s,t), (u,v)). (s, t) \<in> P
    \<and> (u, v) \<in> P \<and> (\<exists>\<sigma> \<tau>. (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*
    \<and> s \<cdot> \<sigma> \<in> NF_terms Q \<and> u \<cdot> \<tau> \<in> NF_terms Q
    \<and> NF_subst nfs (s,t) \<sigma> Q \<and> NF_subst nfs (u,v) \<tau> Q
    \<and> (m \<longrightarrow> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}))}"

lemma DG_I: assumes "(s, t) \<in> P" "(u,v) \<in> P"
   "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*"
   "s \<cdot> \<sigma> \<in> NF_terms Q"
   "u \<cdot> \<tau> \<in> NF_terms Q"
   "NF_subst nfs (s,t) \<sigma> Q" "NF_subst nfs (u,v) \<tau> Q"
   "m \<Longrightarrow> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
 shows "((s,t),(u,v)) \<in> DG nfs m P Q R"
unfolding DG_def using assms by blast

definition
  IEDG ::
    "('f, string) trs \<Rightarrow> ('f, string) terms \<Rightarrow> ('f, string) trs \<Rightarrow> (('f, string) rule \<times> ('f, string) rule) set"
where
  "IEDG P Q R = {((s, t), (u, v)). \<exists> \<mu>. mgu_class (icap_mv R Q {s} t) u = Some \<mu> \<and> {mv_xvar s \<cdot> \<mu>, mv_yvar u \<cdot> \<mu>} \<subseteq> NF_terms Q}"

lemma IEDG: "DG nfs m P Q R \<subseteq> IEDG P Q R"
proof -
  {
    fix s t u v
    assume "((s,t),(u,v)) \<in> DG nfs m P Q R"
    from this[unfolded DG_def] obtain \<sigma> \<tau> where 
      steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*"
      and s: "s \<cdot> \<sigma> \<in> NF_terms Q" and u: "u \<cdot> \<tau> \<in> NF_terms Q"
      by auto
    from s have S: "{s} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q" by auto
    from icap_mv_mgu[OF steps S]
    obtain \<mu> \<delta> where mgu: "mgu_class (icap_mv R Q {s} t) u = Some \<mu>"
     and \<sigma>: "\<And> s. s \<cdot> \<sigma> = map_vars_term x_var s \<cdot> \<mu> \<cdot> \<delta>"
     and \<tau>: "\<And> s. s \<cdot> \<tau> = map_vars_term y_var s \<cdot> \<mu> \<cdot> \<delta>" by blast    
    from NF_instance[OF s[unfolded \<sigma>]] NF_instance[OF u[unfolded \<tau>]] mgu
    have "((s,t),(u,v)) \<in> IEDG P Q R"
      unfolding IEDG_def by auto
  }
  then show ?thesis by auto
qed

end

