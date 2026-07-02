(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Layer systems definitions and main results\<close>

theory LS_Prelude
  imports LS_Extras
begin

text \<open>
  This formalization is based on the layer framework by Felgenhauer et al.\ {cite FMZvO15}.
  In this file we formalize the layer system definitions and the main results as locales.
  This way, the applications of layer systems are decoupled from the proofs of the main theorems.
\<close>

subsection \<open>Definitions\<close>

text \<open>Layer systems {cite \<open>Definition 3.3\<close> FMZvO15}.\<close>

locale layer_system_sig =
  fixes \<F> :: "'f sig" and \<LL> :: "('f, 'v) mctxt set"
begin

definition \<T> where "\<T> = { t :: ('f,'v) term. funas_term t \<subseteq> \<F> }"
definition \<C> where "\<C> = { C :: ('f,'v) mctxt. funas_mctxt C \<subseteq> \<F> }"

text \<open>Tops and max-top {cite \<open>Definition 3.1\<close> FMZvO15}.\<close>

definition topsC :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt set" where
  "topsC C = { L \<in> \<LL>. L \<le> C }"

abbreviation tops where
  "tops t \<equiv> topsC (mctxt_of_term t)"

definition max_topC :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt" where
  "max_topC C = (THE M. M \<in> topsC C \<and> (\<forall>L \<in> topsC C. L \<le> M))"

abbreviation max_top where
  "max_top t \<equiv> max_topC (mctxt_of_term t)"

abbreviation aliensC where
  "aliensC C \<equiv> unfill_holes_mctxt (max_topC C) C"

abbreviation aliens where
  "aliens t \<equiv> unfill_holes (max_top t) t"

end (* layer_system_sig *)

locale layer_system = layer_system_sig \<F> \<LL> for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" +
  assumes \<LL>_sig: "\<LL> \<subseteq> \<C>"
  and L\<^sub>1: "funas_term t \<subseteq> \<F> \<Longrightarrow> \<exists>L \<in> \<LL>. L \<noteq> MHole \<and> L \<le> mctxt_of_term t"
  and L\<^sub>2: "p \<in> poss_mctxt C \<Longrightarrow> mreplace_at C p (MVar x) \<in> \<LL> \<longleftrightarrow> mreplace_at C p MHole \<in> \<LL>"
  and L\<^sub>3: "L \<in> \<LL> \<Longrightarrow> N \<in> \<LL> \<Longrightarrow> p \<in> fun_poss_mctxt L \<Longrightarrow> (subm_at L p, N) \<in> comp_mctxt \<Longrightarrow>
    mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>"

text \<open>Weakly layered TRSs {cite \<open>Definition 3.3\<close> FMZvO15}.\<close>

locale weakly_layered = layer_system \<F> \<LL> for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" +
  fixes \<R> :: "('f, 'v) trs"
  assumes trs: "wf_trs \<R>" and \<R>_sig: "funas_trs \<R> \<subseteq> \<F>"
  and W: "s \<in> \<T> \<Longrightarrow> t \<in> \<T> \<Longrightarrow> p \<in> fun_poss_mctxt (max_top s) \<Longrightarrow> (s, t) \<in> rstep_r_p_s' \<R> r p \<sigma> \<Longrightarrow>
    \<exists>D \<tau>. D \<in> \<LL> \<and> (mctxt_term_conv (max_top s), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> r p \<tau>"

text \<open>Layered TRSs {cite \<open>Definition 3.3\<close> FMZvO15}.\<close>

locale layered = layer_system \<F> \<LL> for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" +
  fixes \<R> :: "('f, 'v) trs"
  assumes trs: "wf_trs \<R>" and \<R>_sig: "funas_trs \<R> \<subseteq> \<F>"
  and C\<^sub>1: "s \<in> \<T> \<Longrightarrow> t \<in> \<T> \<Longrightarrow> p \<in> fun_poss_mctxt (max_top s) \<Longrightarrow> (s, t) \<in> rstep_r_p_s' \<R> r p \<sigma> \<Longrightarrow>
    \<exists>\<tau>. (mctxt_term_conv (max_top s), mctxt_term_conv (max_top t)) \<in> rstep_r_p_s' \<R> r p \<tau> \<or>
        (mctxt_term_conv (max_top s), mctxt_term_conv MHole) \<in> rstep_r_p_s' \<R> r p \<tau>"
  and C\<^sub>2: "L \<in> \<LL> \<Longrightarrow> N \<in> \<LL> \<Longrightarrow> L \<le> N \<Longrightarrow> p \<in> hole_poss L \<Longrightarrow> mreplace_at L p (subm_at N p) \<in> \<LL>"

text \<open>
  Layered TRSs are also weakly layered, i.e., @{locale layered} is a sublocale of
  @{locale weakly_layered}. However, (W) is omitted from the Isabelle definition of layered TRSs,
  making this statement non-trivial, because we have to show that (C1) implies (W). We do this in
  @{file "LS_Basics.thy"}.
\<close>

subsection \<open>Claims\<close>

text \<open>Confluence of weakly layered, left-linear TRSs {cite \<open>Theorem 4.1\<close> FMZvO15}.\<close>

locale weakly_layered_cr_ll = weakly_layered +
  assumes CR_ll: "left_linear_trs \<R> \<Longrightarrow>
    CR_on (rstep \<R>) { t. mctxt_of_term t \<in> \<LL> } \<Longrightarrow> CR_on (rstep \<R>) \<T>"

text \<open>
  Proving {cite \<open>Theorem 4.1\<close> FMZvO15} amounts to showing that @{locale weakly_layered_cr_ll}
  is a sublocale of @{locale weakly_layered}. This will be done in @{file "LS_Left_Linear.thy"}.
\<close>

text \<open>
  Confluence of weakly layered, bounded duplicating TRSs {cite \<open>Theorem 4.3\<close> FMZvO15}.
\<close>

locale weakly_layered_cr_bd = weakly_layered +
  assumes CR_bd: "bounded_duplicating \<R> \<Longrightarrow>
    CR_on (rstep \<R>) { t. mctxt_of_term t \<in> \<LL> } \<Longrightarrow> CR_on (rstep \<R>) \<T>"
begin

text \<open>Confluence of weakly layered, non-duplicating TRSs {cite \<open>Lemma 4.4\<close> FMZvO15}.\<close>

lemmas CR_nd = CR_bd[OF non_duplicating_imp_bounded_duplicating]

end (* weakly_layered_bd *)

text \<open>
  We have to show that @{locale weakly_layered_cr_bd} is a sublocale of @{locale weakly_layered}.
  This is still open (but see @{file "LS_Bounded_Duplicating.thy"}).
\<close>

text \<open>Confluence of layered TRSs {cite \<open>Theorem 4.4\<close> FMZvO15}.\<close>

locale layered_cr = layered +
  assumes CR: "CR_on (rstep \<R>) { t. mctxt_of_term t \<in> \<LL> } \<Longrightarrow> CR_on (rstep \<R>) \<T>"

text \<open>
  We show that @{locale layered_cr} is a sublocale of @{locale layered} in @{file "LS_General.thy"}.
\<close>

end (* LS_Prelude *)
