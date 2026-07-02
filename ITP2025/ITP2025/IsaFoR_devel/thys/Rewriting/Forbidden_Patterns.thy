(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013, 2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Forbidden_Patterns
imports
  First_Order_Rewriting.Trs
  "HOL-Library.Monad_Syntax"
  Show.Shows_Literal
begin

datatype location = H | A | B | R

type_synonym ('f,'v)forb_pattern = "('f,'v)ctxt \<times> ('f,'v)term \<times> location"
type_synonym ('f,'v)forb_patterns = "('f,'v)forb_pattern set"

definition fpstep_cond_single :: "('f,'v) forb_pattern \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
where "fpstep_cond_single pt p t \<equiv> case pt of (C,u,loc) \<Rightarrow>
  \<not>(\<exists> C' \<sigma>. t = C'\<langle>C\<langle>u\<rangle> \<cdot> \<sigma> \<rangle>  \<and> 
   ((loc = H \<and> p = (hole_pos C') @ (hole_pos C)) \<or> 
    (loc = A \<and> p <\<^sub>p (hole_pos C') @ (hole_pos C)) \<or> 
    (loc = B \<and> hole_pos C' @ hole_pos C <\<^sub>p p) \<or> 
    (loc = R \<and> right_of_pos p (hole_pos C'))))"

definition fpstep_cond :: "('f,'v) forb_patterns \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
where "fpstep_cond Pi p t \<equiv> \<forall> pt \<in> Pi. fpstep_cond_single pt p t"

definition fpstep_r_p_s :: 
 "('f,'v) forb_patterns \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) subst \<Rightarrow> 
  ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
 where "fpstep_r_p_s Pi rs lr p \<sigma> s t \<equiv> (s, t) \<in> rstep_r_p_s rs lr p \<sigma> \<and> fpstep_cond Pi p s"

definition fpstep_p :: "('f,'v) forb_patterns \<Rightarrow> ('f,'v)trs \<Rightarrow> pos \<Rightarrow> ('f,'v)trs"
where "fpstep_p Pi rs p = {(s,t) | s t.(\<exists> lr \<sigma>. (s,t) \<in> rstep_r_p_s rs lr p \<sigma> \<and> fpstep_cond Pi p s)}"

definition fpstep :: "('f,'v) forb_patterns \<Rightarrow> ('f,'v)trs  \<Rightarrow> ('f,'v)trs"
where "fpstep Pi rs = {(s,t). \<exists> p. (s,t) \<in>  fpstep_p Pi rs p}"

lemmas fpstep_defs = fpstep_def fpstep_p_def

lemma fpstep_mono: "r \<subseteq> r' \<Longrightarrow> fpstep p r \<subseteq> fpstep p r'"
  unfolding fpstep_defs rstep_r_p_s_def Let_def by blast

lemma fpstep_pI: "(s,t) \<in> rstep_r_p_s rs lr p \<sigma> \<Longrightarrow> fpstep_cond Pi p s \<Longrightarrow> (s,t) \<in> fpstep_p Pi rs p" 
  unfolding fpstep_defs by blast

lemma fpstep_pE[elim]: "(s,t) \<in> fpstep_p Pi rs p \<Longrightarrow> 
 \<lbrakk>\<And> \<sigma> lr. (s,t) \<in> rstep_r_p_s rs lr p \<sigma> \<Longrightarrow> fpstep_cond Pi p s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding fpstep_defs by blast

instantiation location :: showl
begin

fun showsl_location where
  "showsl_location A = (showsl_lit (STR ''above''))"
| "showsl_location B = (showsl_lit (STR ''below''))"
| "showsl_location H = (showsl_lit (STR ''here''))"
| "showsl_location R = (showsl_lit (STR ''right''))"
definition "showsl_list (xs :: location list) = default_showsl_list showsl xs"
instance ..
end

hide_const (open) A B H R

end

