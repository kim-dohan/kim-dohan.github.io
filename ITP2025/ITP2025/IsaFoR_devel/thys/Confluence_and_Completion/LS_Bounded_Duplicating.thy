(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Main result for bounded duplicating systems\<close>

theory LS_Bounded_Duplicating
  imports 
    LS_Common
begin

fun map_funs_mctxt :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> ('g, 'v) mctxt" where
  "map_funs_mctxt _ MHole = MHole"
| "map_funs_mctxt _ (MVar x) = MVar x"
| "map_funs_mctxt f (MFun g Cs) = MFun (f g) (map (map_funs_mctxt f) Cs)"

locale weakly_layered_induct_bounded_duplicating = weakly_layered_induct \<F> \<LL> \<R> rk
  for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" and \<R> :: "('f, 'v) trs" and
      rk :: nat +
  fixes R :: "('f, 'v) term rel" and label :: "('f, 'v) term \<Rightarrow> ('f option, 'v) term"
  assumes bd: "bounded_duplicating \<R>"
  defines "label \<equiv> \<lambda>s. fill_holes (map_funs_mctxt Some (max_top s)) (map (\<lambda>t. Fun None [map_funs_term Some s]) (aliens s))"
  defines "R \<equiv> {(s, t) | s t. (label t, label s) \<in> (relto (rstep {(Fun None [Var undefined], Var undefined)}) (rstep (map_funs_trs Some \<R>)))\<^sup>+ }"
begin

lemma wfR:
  "wf R"
  using wf_inv_image[OF wf_trancl[OF bd[unfolded bounded_duplicating_def SN_rel_on_def SN_iff_wf]]]
  unfolding R_def trancl_converse converse_inv_image[symmetric] by (auto simp: converse_def)

lemma transR:
  "trans R"
  using trans_inv_image[OF trans_trancl[of "_\<inverse>"]]
  unfolding R_def trancl_converse converse_inv_image[symmetric] by (auto simp: converse_def)

lemma short_short_peak:
  assumes "(s, t) \<in> short_step_s s0" "(s, u) \<in> short_step_s s1"
  shows "(t, u) \<in> ((\<Union>i\<in>under R s0. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O (short_step_s s1)\<^sup>= O
    ((\<Union>i\<in>under R s0 \<union> under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O
    ((short_step_s s0)\<inverse>)\<^sup>= O ((\<Union>i\<in>under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>*"
  oops

(*
sublocale weakly_layered_induct_dd
  by (unfold_locales) (fact wfR transR short_short_peak)+
*)

end

(*
sublocale weakly_layered \<subseteq> weakly_layered_cr_bd
proof (standard, unfold rstep_eq_rstep', intro CR_main_lemma[where R = "\<lambda>_. {}"], goal_cases _ step)
  case (step rk)
  then interpret weakly_layered_induct_bounded_duplicating \<F> \<LL> \<R> rk "{}" by (unfold_locales) simp_all
  show ?case by unfold_locales
qed simp_all

lemmas (in weakly_layered) CR_bd = CR_bd

text \<open>{cite \<open>Theorem 4.3\<close> FMZvO15}\<close>
thm weakly_layered.CR_bd
*)

end
