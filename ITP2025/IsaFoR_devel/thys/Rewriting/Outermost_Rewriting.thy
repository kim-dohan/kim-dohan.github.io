(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Outermost_Rewriting
imports
  First_Order_Rewriting.Trs
  Context_Substitution
  "HOL-Library.Monad_Syntax"
begin

definition ostep_cond_single :: "('f,'v)term \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "ostep_cond_single l p t \<equiv> \<forall> q. q <\<^sub>p p \<longrightarrow> \<not> (\<exists> \<sigma>. t |_ q = l \<cdot> \<sigma>)"

definition ostep_cond :: "('f,'v)terms \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "ostep_cond Q p t \<equiv> \<forall> l \<in> Q. ostep_cond_single l p t"

definition ostep_p :: "('f,'v)terms \<Rightarrow> ('f,'v)trs \<Rightarrow> pos \<Rightarrow> ('f,'v)trs" 
  where "ostep_p Q R p \<equiv> {(s,t). (\<exists> lr \<sigma>. (s,t) \<in> rstep_r_p_s R lr p \<sigma>) \<and> ostep_cond Q p s}"

definition ostep :: "('f,'v)terms \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs"
  where "ostep Q R \<equiv> {(s,t). \<exists> p. (s,t) \<in> ostep_p Q R p}"

lemmas ostep_defs = ostep_def ostep_p_def

lemma ostep_pI: "(s,t) \<in> rstep_r_p_s R lr p \<sigma> \<Longrightarrow> ostep_cond Q p s \<Longrightarrow> (s,t) \<in> ostep_p Q R p" 
  unfolding ostep_defs by blast

lemma ostep_pE[elim]: "(s,t) \<in> ostep_p Q R p \<Longrightarrow> \<lbrakk>\<And> \<sigma> lr. (s,t) \<in> rstep_r_p_s R lr p \<sigma> \<Longrightarrow> ostep_cond Q p s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding ostep_defs by blast

lemma ostep_mono: assumes R: "R \<subseteq> R'" 
  shows "ostep Q R \<subseteq> ostep Q R'"
  unfolding ostep_defs rstep_r_p_s_def Let_def using R by blast

end

