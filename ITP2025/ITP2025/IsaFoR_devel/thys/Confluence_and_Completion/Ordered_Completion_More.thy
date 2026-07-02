(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Ordered_Completion_More
  imports Ordered_Completion
begin

(*
lemma litsim_oKB:
  assumes vf: "variant_free_trs E\<^sub>1" "variant_free_trs R\<^sub>1" "variant_free_trs E\<^sub>2" "variant_free_trs R\<^sub>2"
    and litsim: "E\<^sub>1 \<doteq> E\<^sub>2" "R\<^sub>1 \<doteq> R\<^sub>2"
    and step: "(E\<^sub>1, R\<^sub>1) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E\<^sub>1', R\<^sub>1')"
  shows "\<exists>E\<^sub>2' R\<^sub>2'. variant_free_trs E\<^sub>2' \<and> variant_free_trs R\<^sub>2' \<and>
    E\<^sub>1' \<doteq> E\<^sub>2' \<and> R\<^sub>1' \<doteq> R\<^sub>2' \<and> oKB\<^sup>*\<^sup>* (E\<^sub>2, R\<^sub>2) (E\<^sub>2', R\<^sub>2')"
    (is "\<exists>E\<^sub>2' R\<^sub>2'. ?P E\<^sub>2' R\<^sub>2'")
  using step
proof (cases)
  case (deduce s t u)
  show ?thesis
  proof (cases "\<exists>\<pi>. (\<pi> \<bullet> t, \<pi> \<bullet> u) \<in> E\<^sub>2")
    case True
    with deduce have "?P E\<^sub>2 R\<^sub>2" using litsim and vf by (auto simp: litsim_insert' eqvt)
    then show ?thesis by blast
  next
    case False
    then have "?P (E\<^sub>2 \<union> {(t, u)}) R\<^sub>2"
      using oKB.deduce [of s t R\<^sub>2 E\<^sub>2 u] and litsim and vf
        and litsim_rstep_eq [of "R\<^sub>1 \<union> E\<^sub>1\<^sup>\<leftrightarrow>" "R\<^sub>2 \<union> E\<^sub>2\<^sup>\<leftrightarrow>"] and deduce
      by (auto simp: litsim_insert [where p = 0] litsim_union litsim_symcl variant_free_trs_insert)
    then show ?thesis by blast
  qed
next
  case (orientl s t)
  from \<open>(s, t) \<in> E\<^sub>1\<close> and litsim obtain \<pi> where *: "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> E\<^sub>2"
    by (auto simp: subsumable_trs.litsim_def subsumeseq_trs_def eqvt)
  have gr: "\<pi> \<bullet> s \<succ> \<pi> \<bullet> t" using \<open>s \<succ> t\<close> and subst [of s t "sop \<pi>"] by simp

  consider \<pi>' where "(\<pi>' \<bullet> s, \<pi>' \<bullet> t) \<in> R\<^sub>2" | "\<forall>\<pi>'. (\<pi>' \<bullet> \<pi> \<bullet> s, \<pi>' \<bullet> \<pi> \<bullet> t) \<notin> R\<^sub>2"
    by (metis term_pt.permute_plus)
  then show ?thesis
  proof (cases)
    case 1
    from oKB.orientl [OF gr *]
    have oKB: "(E\<^sub>2, R\<^sub>2) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E\<^sub>2 - {(\<pi> \<bullet> s, \<pi> \<bullet> t)}, R\<^sub>2 \<union> {(\<pi> \<bullet> s, \<pi> \<bullet> t)})" (is "_ \<turnstile>\<^sub>o\<^sub>K\<^sub>B (?E, ?R)") .
    show ?thesis
    proof (cases "(\<pi>' \<bullet> s, \<pi>' \<bullet> t) = (\<pi> \<bullet> s, \<pi> \<bullet> t)")
      case True
      then show ?thesis sorr y
    next
      case False
      with 1 have "((\<pi> + -\<pi>') \<bullet> \<pi>' \<bullet> s, (\<pi> + -\<pi>') \<bullet> \<pi>' \<bullet> t) \<in> ?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)}" by auto
      from rstep_rule [OF this, unfolded rstep_permute_iff [where p = "\<pi> + -\<pi>'"]]
      have "(\<pi>' \<bullet> s, \<pi>' \<bullet> t) \<in> rstep (?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)})" .
      then have step: "(\<pi>' \<bullet> s, \<pi>' \<bullet> t) \<in> ostep ?E (?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)})" by (auto simp: ostep_def)
      have "(\<pi>' \<bullet> s, \<pi>' \<bullet> t) \<in> ?R" using 1 by simp
      from oKB.collapse [OF step this]
      have "(?E, ?R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (?E \<union> {(\<pi>' \<bullet> t, \<pi>' \<bullet> t)}, ?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)})" .
      note a = oKB [THEN r_into_rtranclp [where r = oKB], THEN rtranclp.rtrancl_into_rtrancl, OF this]
      note b = oKB.delete [of "\<pi>' \<bullet> t" "?E \<union> {(\<pi>' \<bullet> t, \<pi>' \<bullet> t)}" "?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)}"]
      from a [THEN rtranclp.rtrancl_into_rtrancl, OF b]
      have "oKB\<^sup>*\<^sup>* (E\<^sub>2, R\<^sub>2) (?E, ?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)})"
        by (metis Diff_insert_absorb Un_insert_right a insertI1 insert_absorb sup_bot.right_neutral)
      moreover have "E\<^sub>1' \<doteq> ?E" and "R\<^sub>1' \<doteq> ?R - {(\<pi>' \<bullet> s, \<pi>' \<bullet> t)}"
        using litsim and vf
        apply (auto simp: orientl)
        apply (simp add: "*" litsim_diff1 local.orientl(4) rule_pt.permute_prod.simps)
      then show ?thesis

          thm r_into_rtranclp [where r = oKB]
          apply (auto dest!: r_into_rtranclp [where r = oKB])
      from oKB.compose [OF _ this]
      then show ?thesis sorr y
    qed
  next
    case 2
    moreover note gr
    ultimately have "?P (E\<^sub>2 - {(\<pi> \<bullet> s, \<pi> \<bullet> t)}) (R\<^sub>2 \<union> {(\<pi> \<bullet> s, \<pi> \<bullet> t)})"
      using oKB.orientl [of "\<pi> \<bullet> s" "\<pi> \<bullet> t" E\<^sub>2 R\<^sub>2] and litsim and vf and * and orientl
      by (simp add: eqvt litsim_insert [where p = \<pi>] variant_free_trs_diff r_into_rtranclp variant_free_trs_insert litsim_diff1)
    then show ?thesis by blast
  qed
next
  case (orientr t s)
  then show ?thesis sorr y
next
  case (delete s)
  then show ?thesis sorr y
next
  case (compose t u s)
  then show ?thesis sorr y
next
  case (simplifyl s u t)
  then show ?thesis sorr y
next
  case (simplifyr t u s)
  then show ?thesis sorr y
next
  case (collapse t u s)
  then show ?thesis sorr y
qed
*)


section \<open>Some abstract results\<close>

type_synonym
  ('a, 'b) okb_run = "nat \<times> (nat \<Rightarrow>('a, 'b) equations \<times> ('a, 'b) trs)"

context ordered_completion
begin
definition okb_run :: "('a, 'b) equations \<Rightarrow> ('a, 'b) okb_run \<Rightarrow> bool"
  where "okb_run E crun \<equiv>
    (case crun of (n, ERi) \<Rightarrow> (\<forall> i < n. (ERi i \<turnstile>\<^sub>o\<^sub>K\<^sub>B ERi (Suc i))) \<and> ERi 0 = (E, {}))"
end

locale ordered_completion_run = ordered_completion less + gtotal_reduction_order less
  for less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"  (infix "\<succ>" 50) +
  fixes E :: "nat \<Rightarrow> ('a, 'b) equations"
    and R :: "nat \<Rightarrow> ('a, 'b) trs"
    and E0 :: "('a, 'b) equations"
    and n :: nat
  assumes frun: "okb_run E0 (n, \<lambda> i. (E i, R i))"
begin

definition rule_birth :: "('a, 'b) rule \<Rightarrow> nat"
  where "rule_birth lr \<equiv> LEAST i. i \<le> n \<and> lr \<in> R (n - i)"

definition eq_birth :: "('a, 'b) rule \<Rightarrow> nat"
  where "eq_birth lr \<equiv> LEAST i. i \<le> n \<and> lr \<in> R (n - i) \<or> (snd lr, fst lr) \<in> R (n - i)"

datatype step = Eq | Rule_lr | Rule_rl | Eq_gt_lr | Eq_gt_rl

  (* drop option in second component even though term is irrelevant for equation step *)
type_synonym
  ('f, 'v) cost_tuple = "('f, 'v) term list \<times> ('f, 'v) term \<times> nat \<times> bool"

fun c :: "('a, 'b) term \<Rightarrow> ('a, 'b) rule \<times> pos \<times> step \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) cost_tuple"
  where
    "c s (lr, _, Eq) t = ([s, t], s, 0, False)" |
    "c s (lr, p, Rule_lr) t = ([s], s |_ p, rule_birth lr, False)" |
    "c s (lr, p, Rule_rl) t = ([t], s |_ p, rule_birth lr, False)" |
    "c s (lr, p, Eq_gt_lr) t = ([s], s |_ p, rule_birth lr, True)" |
    "c s (lr, p, Eq_gt_rl) t = ([t], s |_ p, rule_birth lr, True)"

type_synonym
  ('f, 'v) okb_conversion = "(('f, 'v) term list) \<times> ((('f, 'v) rule \<times> pos \<times> step) list)"

fun cost :: "('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) cost_tuple list"
  where "cost (ts, steps) = map (\<lambda> i. c (ts!i) (steps!i) (ts!(Suc i))) [0 ..< length steps]"

definition C where
  "C \<equiv> lex_two
    {(ys,xs). mulex (\<lambda>x y. y \<succ> x) (mset xs) (mset ys)}
    ({(ys,xs). mulex (\<lambda>x y. y \<succ> x) (mset xs) (mset ys)}\<^sup>=)
    (lex_two {(s,t :: ('a, 'b) term). s \<succ> t}
             ({(s,t :: ('a, 'b) term). s \<succ> t}\<^sup>=)
             (lex_two {(a,b :: nat). a > b}
                      ({(a,b :: nat). a > b}\<^sup>=)
                      {(a,b :: bool) . a \<and> \<not> b}))"

definition gt_cost :: "('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) okb_conversion \<Rightarrow> bool"  (infix "\<ggreater>" 55) where
  "gt_cost conv conv' \<equiv> (mset (cost conv'), mset (cost conv)) \<in> mult (C\<inverse>)"

abbreviation ge_cost (infix "\<greatersim>" 55) where "ge_cost conv conv' \<equiv> conv = conv' \<or> gt_cost conv conv'"

lemma trans_SN_C: "trans C \<and> SN C"
proof-
  let ?s1 = "{(ys,xs). mulex (\<lambda>x y. y \<succ> x) (mset xs) (mset ys)}"
  let ?s2 = "{(s,t :: ('a, 'b) term). s \<succ> t}"
  let ?s3 = "{(a,b :: nat). a > b}"
  let ?s4 = "{(a,b :: bool) . a \<and> \<not> b}"
  let ?ls3 = "lex_two ?s3 (?s3\<^sup>=) ?s4"
  let ?ls2 = "lex_two ?s2 (?s2\<^sup>=) ?ls3"
  let ?ls1 = "lex_two ?s1 (?s1\<^sup>=) ?ls2"
  { fix a b c
    from lex_two_compat[of "?s3\<^sup>=" ?s3 "?s4\<^sup>=" ?s4, of a b c] have
      "(a,b) \<in> ?ls3 \<Longrightarrow> (b,c) \<in> ?ls3 \<Longrightarrow> (a,c) \<in> ?ls3" by fastforce
  } note compat3 = this
  have c:"?s3\<^sup>= O ?s3 \<subseteq> ?s3" by auto
  have t:"SN {(a, b). a \<and> \<not> b}" using SN_inv_image[OF SN_nat_gt, of "\<lambda>b. if b then 1 else 0"]
    by (metis (no_types, lifting) SN_onI mem_Collect_eq split_conv)
  from lex_two[OF c SN_nat_gt t] have sn3:"SN ?ls3" by blast
  from trans have c0:"{\<succ>}\<^sup>= O {\<succ>} \<subseteq> {\<succ>}" by fast
  from trans have c1:"{\<succ>} O {\<succ>}\<^sup>= \<subseteq> {\<succ>}" by fast
  from trans have c2:"{\<succ>} O {\<succ>} \<subseteq> {\<succ>}" by fast
  from trans have c3:"{\<succ>}\<^sup>= O {\<succ>}\<^sup>= \<subseteq> {\<succ>}\<^sup>=" by fast
  from compat3 have c4:"?ls3\<^sup>= O ?ls3 \<subseteq> ?ls3" by blast
  { fix a b c
    have "(a,b) \<in> ?ls2 \<Longrightarrow> (a,b) \<in> (?ls2)\<^sup>=" by blast
    with lex_two_compat[of "?s2\<^sup>=" ?s2, OF c0 c1 c2 c3 c4, of a b c] have
      "(a,b) \<in> ?ls2 \<Longrightarrow> (b,c) \<in> ?ls2 \<Longrightarrow> (a,c) \<in> ?ls2" by fastforce
  } note compat2 = this
  then have c4:"?ls2\<^sup>= O ?ls2 \<subseteq> ?ls2" by blast
  from lex_two[OF c0 SN_less sn3] have sn2:"SN ?ls2" by blast
  have c0:"?s1\<^sup>= O ?s1 \<subseteq> ?s1" using mulex_on_trans[of "\<lambda>x y. y \<succ> x" UNIV] by blast
  have c1:"?s1 O ?s1\<^sup>= \<subseteq> ?s1" using mulex_on_trans[of "\<lambda>x y. y \<succ> x" UNIV] by blast
  have c2:"?s1 O ?s1 \<subseteq> ?s1" using mulex_on_trans[of "\<lambda>x y. y \<succ> x" UNIV] by blast
  have c3:"?s1\<^sup>= O ?s1\<^sup>= \<subseteq> ?s1\<^sup>=" using mulex_on_trans[of "\<lambda>x y. y \<succ> x" UNIV] by blast
  { fix a b c
    from compat2 have "?ls2\<^sup>= O ?ls2 \<subseteq> ?ls2" by blast
    from lex_two_compat[of "?s1\<^sup>=" ?s1, OF c0 c1 c2 c3 this, of a b c] have
      "(a,b) \<in> ?ls1 \<Longrightarrow> (b,c) \<in> ?ls1 \<Longrightarrow> (a,c) \<in> ?ls1" by fastforce
  } note compat1 = this
  then have "trans C" unfolding trans_def C_def by argo
  have s1:"?s1\<inverse> = {(xs,ys). mulex (\<lambda>x y. y \<succ> x) (mset xs) (mset ys)}" by fast
  from SN_less have "wf {(x, y). y \<succ> x}" unfolding SN_iff_wf by (simp add: wf_eq_minimal)
  from wfp_on_mulex_on_multisets[of "\<lambda> x y. y \<succ> x" UNIV, unfolded wfp_on_UNIV wfp_def, OF this]
  have x:"wf {(x, y). mulex (\<lambda>x y. y \<succ> x) x y}" unfolding multisets_UNIV wfp_on_UNIV wfp_def by auto
  then have "wf (?s1\<inverse>)" using wf_inv_image[OF x, of "\<lambda>x. mset x"] unfolding inv_image_def s1 by simp
  then have "SN (?s1)" unfolding SN_iff_wf converse_def mem_Collect_eq split using conversep_eq
    by (simp add: wf_eq_minimal)
  from lex_two[OF c0 this sn2] have "SN C" unfolding C_def by simp
  with \<open>trans C\<close> show ?thesis by simp
qed

lemma SN_C: "SN C" using trans_SN_C by simp

lemma trans_C: "trans (C\<inverse>)" using trans_SN_C by simp

lemma irrefl_C: "irrefl (C\<inverse>)"
  using wf_acyclic[OF SN_C[ unfolded SN_iff_wf]] acyclic_irrefl trancl_id[OF trans_C]
  by metis

lemma irrefl_on_C: "irrefl_on A (C\<inverse>)" 
  using irrefl_C unfolding irrefl_on_def by auto

lemma eq_to_rule_step: assumes "mset ts = {#s,t#}" shows "((ts, p\<^sub>1, step\<^sub>1),([s], p\<^sub>2, step\<^sub>2)) \<in> C"
proof-
  let ?s1 = "{(ys,xs). mulex (\<lambda>x y. y \<succ> x) (mset xs) (mset ys)}"
  have trans:"?s1 O ?s1 \<subseteq> ?s1" using mulex_on_trans[of "\<lambda>x y. y \<succ> x" UNIV] by blast
  from mulex_on_self_add_singleton_right[of "t" UNIV "{#s#}"]
  have "mulex (\<lambda>x y. y \<succ> x) (mset [s]) (mset ts)" unfolding assms using mset.simps
    by (simp add: add_mset_commute)
  then have "(ts, [s]) \<in> ?s1" by blast
  then show ?thesis unfolding C_def by force
qed

definition R_all where "R_all \<equiv> \<Union> {R i | i. i \<le> n}"
definition E_all where "E_all \<equiv> \<Union> {E i | i. i \<le> n}"

abbreviation "in_E_all" where "in_E_all lr \<equiv> lr \<in> E_all \<or> (snd lr, fst lr) \<in> E_all"
abbreviation "in_E" where "in_E lr EE \<equiv> lr \<in> EE \<or> (snd lr, fst lr) \<in> EE"

fun valid_step :: "('a, 'b) term \<Rightarrow> ('a, 'b) rule \<times> pos \<times> step \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where "valid_step s (lr, p, Eq) t = (in_E_all lr \<and> (s, t) \<in> rstep_pos {lr} p)"
  | "valid_step s (lr, p, Rule_lr) t = (lr \<in> R_all \<and> p \<in> poss s \<and> (s, t) \<in> rstep_pos {lr} p)"
  | "valid_step s (lr, p, Rule_rl) t = (lr \<in> R_all \<and> p \<in> poss t \<and> (t, s) \<in> rstep_pos {lr} p)"
  | "valid_step s (lr, p, Eq_gt_lr) t = (in_E_all lr \<and> s |_ p \<succ> t |_ p \<and> (s, t) \<in> rstep_pos {lr} p)"
  | "valid_step s (lr, p, Eq_gt_rl) t = (in_E_all lr \<and> t |_ p \<succ> s |_ p \<and> (t, s) \<in> rstep_pos {(snd lr, fst lr)} p)"

definition conversion :: "('a, 'b) term \<Rightarrow> ('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where "conversion s conv t \<equiv>
    case conv of (ts, steps) \<Rightarrow>
    length ts = Suc (length steps) \<and>
    s = ts!0 \<and> t = ts!(length steps) \<and> (\<forall> i < length steps. valid_step (ts!i) (steps!i) (ts!(Suc i)))"

definition ground_conversion :: "('a, 'b) term \<Rightarrow> ('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where "ground_conversion s conv t \<equiv>
    conversion s conv t \<and> (case conv of (ts, steps) \<Rightarrow> (\<forall>i \<le> length steps. ground (ts!i)))"

lemma okb_step:
  "i < n \<Longrightarrow> (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
  using frun[unfolded okb_run_def split] by auto

abbreviation kind where "kind step \<equiv> snd (snd step)"

definition peak where "peak s P t \<equiv>
     (case P of (_, steps) \<Rightarrow> length steps = 2 \<and>
     kind (steps ! 0) \<in> { Eq_gt_rl, Rule_rl} \<and> kind (steps ! 1) \<in> { Eq_gt_lr, Rule_lr })"

definition fair where "fair \<equiv>
  (\<forall> s P t. peak s P t \<and>  ground_conversion s P t \<longrightarrow> (\<exists> Q. ground_conversion s Q t \<and> P \<ggreater> Q))"


definition rewrite_conversion
  where "rewrite_conversion P \<equiv>
    case P of (_, steps) \<Rightarrow>
    (\<exists> m \<le> length steps. (\<forall> i < m. kind (steps ! i) = Rule_lr \<or> kind (steps ! i) = Eq_gt_lr) \<and>
              (\<forall> i. m \<le> i \<longrightarrow> i < length steps \<longrightarrow> kind (steps ! i) = Rule_rl \<or> kind (steps ! i) = Eq_gt_rl))"

    (* proof concatenation *)
definition conv_concat :: "('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) okb_conversion \<Rightarrow> ('a, 'b) okb_conversion" (infix "\<circle>" 55) where
  "conv_concat P Q \<equiv> case P of (ts\<^sub>p, steps\<^sub>p) \<Rightarrow> case Q of (ts\<^sub>q, steps\<^sub>q) \<Rightarrow>
   (butlast ts\<^sub>p @ ts\<^sub>q, steps\<^sub>p @ steps\<^sub>q)"

lemma concat_empty_end: "ts \<noteq> [] \<Longrightarrow> (ts, steps) \<circle> ([last ts], []) = (ts, steps)"
  unfolding conv_concat_def split using append_butlast_last_id by blast

lemma empty_conv: "conversion s (ts, steps) t \<Longrightarrow> steps = [] \<Longrightarrow> s = t"
  unfolding conversion_def split by auto

lemma empty_conv2: "conversion s ([s], []) s"
  unfolding conversion_def split by auto

lemma empty_concat:
  assumes "steps = []" and "conversion s (ts, steps) t"
  shows "(ts, steps) \<circle> Q = Q"
proof-
  obtain ts\<^sub>q steps\<^sub>q where Q:"Q = (ts\<^sub>q, steps\<^sub>q)" by (cases Q, auto)
  from assms have "length ts = 1" unfolding conversion_def split by simp
  then have "length (butlast ts) = 0" using length_butlast by auto
  with assms(1) have "(ts, steps) \<circle> Q = (ts\<^sub>q, steps\<^sub>q)" unfolding conv_concat_def Q split by blast
  then show ?thesis unfolding Q by auto
qed

lemma concat_empty:
  assumes "conversion t (ts, steps) t'" and "steps = []" and "conversion s Q t"
  shows "conversion s (Q \<circle> (ts, steps)) t"
proof-
  obtain ts\<^sub>q steps\<^sub>q where Q:"Q = (ts\<^sub>q, steps\<^sub>q)" by (cases Q, auto)
  note assms = assms[unfolded conversion_def Q split]
  from assms have ts0:"ts!0 = t" by auto
  from assms have tsk:"ts\<^sub>q!(length steps\<^sub>q) = t" by auto
  from assms have l:"length ts = 1" unfolding conversion_def split by simp
  from l assms(1) have ts:"ts = [t]" unfolding conversion_def split assms(2)
    by (metis length_0_conv length_Suc_conv nth_Cons_0)
  from assms have last:"length ts\<^sub>q = Suc (length steps\<^sub>q)" "ts\<^sub>q ! length steps\<^sub>q = t" by auto
  from length_greater_0_conv[of ts\<^sub>q] last(1) have not_nil:"ts\<^sub>q \<noteq> []" by simp
  then have bl:"butlast ts\<^sub>q @ ts = ts\<^sub>q"
    using append_butlast_last_id last_conv_nth[OF not_nil]
    unfolding ts last(1) diff_Suc_1 last(2) by auto
  from assms(3) show ?thesis unfolding conv_concat_def conversion_def split Q assms(2) bl by force
qed

lemma concat_extend:
  assumes "conversion s (ts, steps) t" and "valid_step t step u"
  shows "conversion  s (ts @ [u], steps @ [step]) u"
  using assms unfolding conversion_def split using less_Suc_eq
  by (simp add: nth_append)

lemma concat_assoc: "ts\<^sub>q \<noteq> [] \<Longrightarrow> (P \<circle> (ts\<^sub>q, steps\<^sub>q)) \<circle> S = P \<circle> ((ts\<^sub>q, steps\<^sub>q) \<circle> S)"
proof-
  assume tsq:"ts\<^sub>q \<noteq> []"
  obtain ts\<^sub>p steps\<^sub>p where P:"P = (ts\<^sub>p, steps\<^sub>p)" by (cases P, auto)
  obtain ts\<^sub>s steps\<^sub>s where S:"S = (ts\<^sub>s, steps\<^sub>s)" by (cases S, auto)
  from tsq show ?thesis unfolding conv_concat_def P S split
    by (simp add: butlast_append)
qed

lemma concat:
  assumes Pconv: "conversion s (P :: ('a, 'b) okb_conversion) t" and Qconv:"conversion t Q u"
  shows "conversion s (P \<circle> Q) u"
proof-
  obtain ts\<^sub>p steps\<^sub>p where P:"P = (ts\<^sub>p, steps\<^sub>p)" by (cases P, auto)
  obtain ts\<^sub>q steps\<^sub>q where Q:"Q = (ts\<^sub>q, steps\<^sub>q)" by (cases Q, auto)
  note assms = assms[unfolded P Q conversion_def split]
  show ?thesis proof(cases steps\<^sub>p)
    case Nil
    from empty_conv[OF Pconv[unfolded P] Nil] empty_concat[OF Nil Pconv[unfolded P]] Qconv
    show ?thesis unfolding P by auto
  next
    case (Cons step steps)
    from assms have 1:"length (butlast ts\<^sub>p @ ts\<^sub>q) = Suc (length (steps\<^sub>p @ steps\<^sub>q))" by auto
    from assms have tsp:"ts\<^sub>p \<noteq> []" by force
    from assms have s:"s = ts\<^sub>p ! 0" by fast
    from assms have l_tsp:"length ts\<^sub>p = Suc (length steps\<^sub>p)" by fast
    let ?ts = "butlast ts\<^sub>p @ ts\<^sub>q"
    let ?steps = "steps\<^sub>p @ steps\<^sub>q"
    from s nth_butlast[of 0 ts\<^sub>p, unfolded length_butlast l_tsp Cons] have "butlast ts\<^sub>p ! 0 = s" by auto
    then have 2:"s = ?ts ! 0"
      unfolding nth_append length_butlast[of ts\<^sub>p] l_tsp Cons diff_Suc_1 by simp
    from assms have tt:"ts\<^sub>q ! 0 = ts\<^sub>p ! (length steps\<^sub>p)" by fast
    from assms have u:"u = ts\<^sub>q ! length steps\<^sub>q" by simp
    from assms have l_tsq:"length ts\<^sub>q = Suc (length steps\<^sub>q)" by fast
    with u tsp 1 have 3:"u = ?ts ! length ?steps" by (simp add:nth_append Cons)
    { fix i
      assume i:"i < length ?steps"
      from assms have tsq:"ts\<^sub>q \<noteq> []" by force
      from l_tsp have l_tsp:"length (butlast ts\<^sub>p) = length steps\<^sub>p" using length_butlast by auto
      from assms have val:"\<And>i. i<length steps\<^sub>p \<Longrightarrow> valid_step (ts\<^sub>p ! i) (steps\<^sub>p ! i) (ts\<^sub>p ! Suc i)"
        "\<And>i. i<length steps\<^sub>q \<Longrightarrow> valid_step (ts\<^sub>q ! i) (steps\<^sub>q ! i) (ts\<^sub>q ! Suc i)" by auto
      have "valid_step (?ts ! i) (?steps ! i) (?ts ! Suc i)" proof(cases "i < length steps\<^sub>p")
        case True
        with nth_append have st:"?steps ! i = steps\<^sub>p ! i" by metis
        from i True l_tsp nth_butlast have bl1:"?ts ! i = ts\<^sub>p ! i" unfolding nth_append by metis
        from i True l_tsp nth_butlast have bl2:"?ts ! (Suc i) = ts\<^sub>p ! (Suc i)" unfolding nth_append
          by (metis Suc_lessI cancel_comm_monoid_add_class.diff_cancel tt)
        from val(1)[OF True] show ?thesis unfolding bl1 bl2 st by simp
      next
        case False
        with i have ii:"i - length steps\<^sub>p < length steps\<^sub>q" by simp
        with False nth_butlast have nth:"?ts ! i = ts\<^sub>q ! (i - length steps\<^sub>p)" unfolding nth_append l_tsp by argo
        from ii False have nth':"?steps ! i = steps\<^sub>q ! (i - length steps\<^sub>p)" unfolding nth_append by argo
        from val(2)[OF ii] tt show ?thesis unfolding nth nth' unfolding nth_append
          using False Suc_diff_le l_tsp by auto
      qed
    }
    with 1 2 3 show ?thesis unfolding P Q conv_concat_def conversion_def split by simp
  qed
qed

lemma gconcat:
  assumes Pconv: "ground_conversion s (P :: ('a, 'b) okb_conversion) t" and Qconv:"ground_conversion t Q u"
  shows "ground_conversion s (P \<circle> Q) u"
proof-
  obtain ts\<^sub>p steps\<^sub>p where P:"P = (ts\<^sub>p, steps\<^sub>p)" by (cases P, auto)
  obtain ts\<^sub>q steps\<^sub>q where Q:"Q = (ts\<^sub>q, steps\<^sub>q)" by (cases Q, auto)
  note convs = Pconv[unfolded ground_conversion_def] Qconv [unfolded ground_conversion_def]
  from convs concat have PQ:"conversion s (P \<circle> Q) u" by auto
  note convs = convs[unfolded P Q conversion_def split]
  { fix i
    assume i:"i\<le>length (steps\<^sub>p @ steps\<^sub>q)"
    from PQ[unfolded P Q conv_concat_def split conversion_def] have
      "length (butlast ts\<^sub>p @ ts\<^sub>q) = Suc (length (steps\<^sub>p @ steps\<^sub>q))" by simp
    with i have i:"i<length (butlast ts\<^sub>p @ ts\<^sub>q)" by simp
    from convs have l:"length (butlast ts\<^sub>p) = length steps\<^sub>p" by auto
    { assume i:"i < length (butlast ts\<^sub>p)"
      from i l convs[unfolded P Q split_beta] have "ground ((butlast ts\<^sub>p @ ts\<^sub>q) ! i)"
        unfolding nth_append length_butlast nth_butlast[OF i] snd_conv by force
    } note in_P = this
    { assume ii:"i > length (butlast ts\<^sub>p)"
      with less_iff_Suc_add obtain j where j:"i = Suc(length steps\<^sub>p + j)" unfolding l by blast
      from convs have ll:"length ts\<^sub>q = Suc (length steps\<^sub>q)" by auto
      from i have "j < length steps\<^sub>q" unfolding length_append j l ll nat_add_left_cancel_less by auto
      with ii convs[unfolded P Q split_beta snd_conv] j have "ground ((butlast ts\<^sub>p @ ts\<^sub>q) ! i)"
        unfolding nth_append l by force
    } note in_Q = this

    from convs(2) have "ground ((butlast ts\<^sub>p @ ts\<^sub>q) ! (length (butlast ts\<^sub>p)))" unfolding nth_append l by simp
    with in_P in_Q have "ground ((butlast ts\<^sub>p @ ts\<^sub>q) ! i)" by fastforce
  }
  with PQ show ?thesis unfolding ground_conversion_def conv_concat_def P Q split by auto
qed

lemma conversion_last:
  assumes P: "conversion s (ts\<^sub>p, steps\<^sub>p) t"
  shows "ts\<^sub>p ! (length steps\<^sub>p) = t"
  using assms unfolding conversion_def split by simp

lemma cost_concat:
  assumes P:"conversion t\<^sub>1 P t\<^sub>2" and Q:"conversion t\<^sub>2 Q t\<^sub>3"
  shows "mset (cost (P \<circle> Q)) = mset (cost P) + mset (cost Q)"

proof-
  obtain ts\<^sub>p steps\<^sub>p where P:"P = (ts\<^sub>p, steps\<^sub>p)" by (cases P, auto)
  obtain ts\<^sub>q steps\<^sub>q where Q:"Q = (ts\<^sub>q, steps\<^sub>q)" by (cases Q, auto)
  note assms = assms[unfolded P Q conversion_def split]
  then have l:"length (butlast ts\<^sub>p) = length steps\<^sub>p" using length_butlast by auto
  let ?ts = "butlast ts\<^sub>p @ ts\<^sub>q"
  let ?steps = "steps\<^sub>p @ steps\<^sub>q"
  from assms have ttq:"ts\<^sub>q ! 0 = ts\<^sub>p ! (length steps\<^sub>p)" by fast
  with assms have ttp:"ts\<^sub>p ! (length steps\<^sub>p) = ?ts ! (length steps\<^sub>p)" unfolding nth_append nth_butlast by force
  then have tsp:"\<And>i. i \<le> length steps\<^sub>p \<Longrightarrow>?ts ! i = ts\<^sub>p ! i" unfolding nth_append by (metis antisym_conv1 l nth_butlast)
  { fix i assume "i < length steps\<^sub>p"
    with tsp nth_append[of steps\<^sub>p steps\<^sub>q] have
      "c (?ts ! i) (?steps ! i) (?ts ! Suc i) = c (ts\<^sub>p ! i) (steps\<^sub>p ! i) (ts\<^sub>p ! Suc i)" by force
  }
  then have p:"map (\<lambda>i. c (ts\<^sub>p ! i) (steps\<^sub>p ! i) (ts\<^sub>p ! Suc i)) [0..<length steps\<^sub>p] =
           map (\<lambda>i. c (?ts ! i) (?steps ! i) (?ts ! Suc i)) [0..<length steps\<^sub>p]" by fastforce
  let ?q = "\<lambda>i. i + length steps\<^sub>p"
  { fix i assume i:"i < length steps\<^sub>q"
    have "?ts ! (length steps\<^sub>p + i) = ts\<^sub>q ! i" unfolding nth_append l by fastforce
    with i l have "c (?ts ! (?q i)) (?steps ! (?q i)) (?ts ! Suc (?q i)) = c (ts\<^sub>q ! i) (steps\<^sub>q ! i) (ts\<^sub>q ! Suc i)"
      unfolding nth_append by force
  }
  then have q:"map (\<lambda>i. c (ts\<^sub>q ! i) (steps\<^sub>q ! i) (ts\<^sub>q ! Suc i)) [0..<length steps\<^sub>q] =
           map (\<lambda>i. c (?ts ! (?q i)) (?steps ! (?q i)) (?ts ! Suc (?q i))) [0..<length steps\<^sub>q]" by fastforce
  show ?thesis unfolding conv_concat_def P Q split cost.simps
      length_append map_upt_add mset_append[symmetric] p q by blast
qed

lemma gt_concat:
  assumes R1: "conversion t\<^sub>0 R\<^sub>1 t\<^sub>1" and P:"conversion t\<^sub>1 P t\<^sub>2" and Q:"conversion t\<^sub>1 Q t\<^sub>2" and
    R2: "conversion t\<^sub>2 R\<^sub>2 t\<^sub>3" and gt:"P \<ggreater> Q"
  shows "((R\<^sub>1 \<circle> P) \<circle> R\<^sub>2) \<ggreater> ((R\<^sub>1 \<circle> Q) \<circle> R\<^sub>2)"
proof-
  from concat R1 P have RP:"conversion t\<^sub>0 (R\<^sub>1 \<circle> P) t\<^sub>2" by auto
  from concat R1 Q have RQ:"conversion t\<^sub>0 (R\<^sub>1 \<circle> Q) t\<^sub>2" by auto
  let ?pcost = "mset (cost R\<^sub>1) + mset (cost P) + mset (cost R\<^sub>2)"
  let ?qcost = "mset (cost R\<^sub>1) + mset (cost Q) + mset (cost R\<^sub>2)"
  from cost_concat R1 P RP R2 have cp:"mset (cost ((R\<^sub>1 \<circle> P) \<circle> R\<^sub>2)) = ?pcost" by simp
  from cost_concat R1 Q RQ R2 have cq:"mset (cost ((R\<^sub>1 \<circle> Q) \<circle> R\<^sub>2)) = ?qcost" by simp
  from gt mult_cancel[OF trans_C irrefl_on_C] show ?thesis unfolding gt_cost_def cp cq
    by (metis add.commute)
qed

lemma gt_concat1:
  assumes R1: "conversion t\<^sub>0 R\<^sub>1 t\<^sub>1" and P:"conversion t\<^sub>1 P t\<^sub>2" and Q:"conversion t\<^sub>1 Q t\<^sub>2" and gt:"P \<ggreater> Q"
  shows "(R\<^sub>1 \<circle> P) \<ggreater> (R\<^sub>1 \<circle> Q)"
proof-
  from concat R1 P have RP:"conversion t\<^sub>0 (R\<^sub>1 \<circle> P) t\<^sub>2" by auto
  from concat R1 Q have RQ:"conversion t\<^sub>0 (R\<^sub>1 \<circle> Q) t\<^sub>2" by auto
  let ?pcost = "mset (cost R\<^sub>1) + mset (cost P)"
  let ?qcost = "mset (cost R\<^sub>1) + mset (cost Q)"
  from cost_concat R1 P RP have cp:"mset (cost (R\<^sub>1 \<circle> P)) = ?pcost" by simp
  from cost_concat R1 Q RQ have cq:"mset (cost (R\<^sub>1 \<circle> Q)) = ?qcost" by simp
  from gt mult_cancel[OF trans_C irrefl_on_C] show ?thesis unfolding gt_cost_def cp cq
    by (metis add.commute)
qed

lemma gt_concat2:
  assumes R1: "conversion t\<^sub>0 R\<^sub>1 t\<^sub>1" and P:"conversion t\<^sub>1 (ts, steps) t\<^sub>1" and R2: "conversion t\<^sub>1 R\<^sub>2 t\<^sub>2"
    and steps:"steps \<noteq> []"
  shows "((R\<^sub>1 \<circle> (ts, steps)) \<circle> R\<^sub>2) \<ggreater> (R\<^sub>1 \<circle> R\<^sub>2)"
proof-
  from concat R1 P have RP:"conversion t\<^sub>0 (R\<^sub>1 \<circle> (ts, steps)) t\<^sub>1" by auto
  from concat R1 R2 have RR:"conversion t\<^sub>0 (R\<^sub>1 \<circle> R\<^sub>2) t\<^sub>2" by auto
  let ?cost = "mset (cost R\<^sub>1) + mset (cost (ts, steps)) + mset (cost R\<^sub>2)"
  from cost_concat R1 P RP R2 have
    cp:"mset (cost ((R\<^sub>1 \<circle> (ts, steps)) \<circle> R\<^sub>2)) = ?cost" by simp
  from cost_concat R1 RR R2 have cq:"mset (cost (R\<^sub>1 \<circle> R\<^sub>2)) = mset (cost R\<^sub>1) + mset (cost R\<^sub>2)" by simp
  from steps have c:"mset (cost (ts, steps)) \<noteq> {#}" unfolding cost.simps using c.simps mset_zero_iff_right
    by (cases "cost (ts, steps)", auto)
  note mc = mult_cancel[OF trans_C irrefl_on_C]
  note x = mc[of "{#}" "mset (cost R\<^sub>1)" "mset (cost (ts, steps))", symmetric]
  from non_empty_empty_mult[OF c] x show ?thesis
    unfolding gt_cost_def cp cq mc using x by (simp add: union_commute)
qed

lemma conv_prefix:
  assumes conv: "conversion s (ts, steps) t" and i:"i \<le> length steps"
  shows "conversion s (take (Suc i) ts, take i steps) (ts ! i)"
proof-
  note assms = assms[unfolded conversion_def split]
  then have l:"length ts = Suc (length steps)" by simp
  from i l have 1:"length (take (Suc i) ts) = Suc (length (take i steps))" by simp
  from assms i have 2:"s = take (Suc i) ts ! 0" by simp
  from l nth_take have last:"take (Suc i) ts ! length (take i steps) = ts ! length (take i steps)" by force
  from i have min:"min (length steps) i = i" by auto
  from l nth_take[of i "Suc i"] have 3:"ts ! i = take (Suc i) ts ! length (take i steps)"
    unfolding last length_take min by simp
  show ?thesis using assms 1 2 3 unfolding conversion_def split using length_take nth_take by fastforce
qed

lemma gconv_prefix:
  assumes conv: "ground_conversion s (ts, steps) t" and i:"i \<le> length steps"
  shows "ground_conversion s (take (Suc i) ts, take i steps) (ts ! i)"
  using assms conv_prefix unfolding ground_conversion_def split by auto

lemma conv_suffix:
  assumes conv: "conversion s (ts, steps) t" and i:"i \<le> length steps"
  shows "conversion (ts ! i) (drop i ts, drop i steps) t"
proof-
  note assms = assms[unfolded conversion_def split]
  then have l:"length ts = Suc (length steps)" by simp
  from i l have 1:"length (drop i ts) = Suc (length (drop i steps))" by force
  from i l have 2:"ts ! i = drop i ts ! 0" by simp
  from i 1 l have 3:"t = drop i ts ! length (drop i steps)" by (simp add: assms(1))
  show ?thesis using assms unfolding conversion_def split 1 2 3 by fastforce
qed

lemma gconv_suffix:
  assumes conv: "ground_conversion s (ts, steps) t" and i:"i \<le> length steps"
  shows "ground_conversion (ts ! i) (drop i ts, drop i steps) t"
proof-
  note assms = assms[unfolded ground_conversion_def split]
  from assms conv_suffix have conv:"conversion (ts ! i) (drop i ts, drop i steps) t" by auto
  from assms have l:"length ts = Suc (length steps)" unfolding conversion_def split by auto
  with assms have all_l:"\<forall>i<length ts. ground (ts ! i)" unfolding conversion_def split by simp
  { fix j
    assume j:"j \<le> length (drop i steps)"
    with i l have ij:"i + j < length ts" unfolding length_drop by simp
    with all_l nth_drop have "ground (drop i ts ! j)" by force
  }
  with conv show ?thesis unfolding ground_conversion_def split by blast
qed

lemma conv_extract_subproof:
  assumes conv: "conversion s (ts, steps) t" and j:"j < i" and i:"i \<le> length steps"
  defines "P\<^sub>1 \<equiv> (take (Suc j) ts, take j steps)"
  defines "P\<^sub>2 \<equiv> (drop i ts, drop i steps)"
  defines "Q \<equiv> (take (Suc i - j) (drop j ts), take (i - j) (drop j steps))"
  shows "conversion s P\<^sub>1 (ts ! j) \<and> conversion (ts ! j) Q (ts ! i) \<and>
         conversion (ts ! i) P\<^sub>2 t \<and> (ts, steps) = ((P\<^sub>1 \<circle> Q) \<circle> P\<^sub>2)"
proof-
  from conv_prefix conv i j have P1:"conversion s P\<^sub>1 (ts ! j)" unfolding P\<^sub>1_def by force
  from conv_suffix conv i have P2:"conversion (ts ! i) P\<^sub>2 t" unfolding P\<^sub>2_def by force
  from i j have ij:"i - j \<le> length (drop j steps)" unfolding length_drop by fastforce
  from conv[unfolded conversion_def split] have l:"length ts = Suc (length steps)" by simp
  from ij i j l have tsi:"drop j ts ! (i - j) = ts ! i" by force
  from conv_suffix conv i j have R:"conversion (ts ! j) (drop j ts, drop j steps) t" by force
  from j Suc_diff_le conv_prefix[OF this ij] tsi have Q:"conversion (ts ! j) Q (ts ! i)"
    unfolding Q_def tsi by fastforce
      (* equality of step sequence*)
  from j min.strict_order_iff have 1:"take j (take i steps) = take j steps" unfolding take_take by metis
  from append_take_drop_id[of j "take i steps"] i j
  have a:"take j steps @ take (i - j) (drop j steps) = take i steps" unfolding 1 drop_take by blast
  with append_take_drop_id have
    steps:"(take j steps @ take (i - j) (drop j steps)) @ drop i steps = steps" by force
      (* equality of term sequence*)
  from i l have ll:"Suc i \<le> length ts" by auto
  from i j l have lj:"Suc j \<le> length ts" by auto
  from j have min:"min j (Suc i) = j" by auto
  from j append_take_drop_id[of j "take (Suc i) ts", unfolded drop_take take_take] butlast_take[OF lj]
  have a:"butlast (take (Suc j) ts) @ take (Suc i - j) (drop j ts) = take (Suc i) ts"
    unfolding min by auto
  from butlast_take[OF ll] have b:"butlast (take (Suc i) ts) = take i ts" by auto
  with a have "butlast (butlast (take (Suc j) ts) @ take (Suc i - j) (drop j ts)) = take i ts" by auto
  with append_take_drop_id have
    ts:"butlast (butlast (take (Suc j) ts) @ take (Suc i - j) (drop j ts)) @ drop i ts = ts" by auto
      (* combine *)
  with steps ts have "(ts, steps) = ((P\<^sub>1 \<circle> Q) \<circle> P\<^sub>2)"
    unfolding conv_concat_def Q_def P\<^sub>1_def P\<^sub>2_def split by simp
  with P1 P2 Q show ?thesis unfolding P\<^sub>1_def P\<^sub>2_def by auto
qed

  (* TODO derive from conv_extract_subproof *)
lemma conv_extract_step:
  assumes conv: "conversion s (ts, steps) t" and i:"i < length steps"
  defines "Q \<equiv> ([ts ! i, ts ! Suc i], [steps ! i])"
  defines "P\<^sub>1 \<equiv> (take (Suc i) ts, take i steps)"
  defines "P\<^sub>2 \<equiv> (drop (Suc i) ts, drop (Suc i) steps)"
  shows "conversion s P\<^sub>1 (ts ! i) \<and> conversion (ts ! i) Q (ts ! (Suc i)) \<and>
         conversion (ts ! (Suc i)) P\<^sub>2 t \<and> (ts, steps) = ((P\<^sub>1 \<circle> Q) \<circle> P\<^sub>2)"
proof-
  from conv have l:"length ts = Suc (length steps)" unfolding conversion_def by auto
  let ?qts = "take 2 (drop i ts)" and ?qsteps = "take (Suc 0) (drop i steps)"
  from l i Cons_nth_drop_Suc[of _ ts] take_Suc_Cons take_0
  have ts:"?qts = [ts ! i, ts ! Suc i]" unfolding numeral_2_eq_2 by (metis Suc_mono less_SucI)
  from Cons_nth_drop_Suc[OF i] take_Suc_Cons[of 0]
  have steps:"?qsteps = [steps ! i]" unfolding take_0 by metis
  with ts have Q:"(?qts, ?qsteps) = Q" unfolding Q_def by force
  from i have "Suc i \<le> length steps" by auto
  from i l conv_extract_subproof[OF conv lessI this] Q show ?thesis
    unfolding P\<^sub>1_def Q_def P\<^sub>2_def by simp
qed

  (* a non-rewrite proof which does not contain equation steps contains a peak *)
lemma non_rewrite_proof_has_peak:
  assumes nrew: "\<not> rewrite_conversion (ts, steps)"
    and no_Eq:"\<nexists>i. i < length steps \<and> kind (steps ! i) = Eq"
  shows"\<exists>j. Suc j < length steps \<and>
         (kind (steps ! j) = Rule_rl \<or> kind (steps ! j) = Eq_gt_rl) \<and>
         (kind (steps ! (Suc j)) = Rule_lr \<or> kind (steps ! (Suc j)) = Eq_gt_lr)"
proof-
  let ?lr = "\<lambda>i. kind (steps ! i) = Rule_lr \<or> kind (steps ! i) = Eq_gt_lr"
  let ?rl = "\<lambda>i. kind (steps ! i) = Rule_rl \<or> kind (steps ! i) = Eq_gt_rl"
  let ?k = "length steps"
  from nrew[unfolded rewrite_conversion_def split]
  have all:"\<forall> m \<le> ?k. (\<exists> i<m. \<not>(?lr i)) \<or> (\<exists> i\<ge>m. i < ?k \<and> \<not>(?rl i))" by auto
  { assume "\<forall>m < ?k. ?lr m"
    then have "rewrite_conversion (ts, steps)" unfolding rewrite_conversion_def split by auto
    with nrew have False by auto
  }
  then obtain mm where "mm < ?k \<and> \<not>?lr mm" by auto
  with no_Eq have mm:"mm < ?k \<and> ?rl mm" by (cases "kind (steps ! mm)", auto)
  then have nonempty:"{m. m < ?k \<and> ?rl m} \<noteq> {}" by auto
  have fin:"finite {m. m < ?k \<and> ?rl m}" by auto
  define m where "m \<equiv> Min {m. m < ?k \<and> ?rl m}"
  with Min_in[OF fin nonempty] have mk:"m < ?k" and rl_m:"?rl m" unfolding m_def by auto
  with all have i:"(\<exists> i<m. \<not>(?lr i)) \<or> (\<exists> i\<ge>m. i < ?k \<and> \<not>(?rl i))" by auto
  { assume "\<exists> i<m. \<not>(?lr i)"
    then obtain i where i:"i < m" "\<not>(?lr i)" by auto
    with no_Eq mk have "?rl i" by (cases "kind (steps ! i)", auto)
    with i mk have "i \<in> {m. m < ?k \<and> ?rl m}" by auto
    from i m_def Min_le[OF fin this] have False by linarith
  }
  with i obtain ii where ii:"ii \<ge> m" "ii < ?k" "\<not>(?rl ii)" by auto
  with no_Eq mk have "?lr ii" by (cases "kind (steps ! ii)", auto)
  with ii have nonempty:"{i. i \<ge> m \<and> i < ?k \<and> ?lr i} \<noteq> {}" by auto
  have fin:"finite {i. i \<ge> m \<and> i < ?k \<and> ?lr i}" by auto
  define i where "i \<equiv> Min {i. i \<ge> m \<and> i < ?k \<and> ?lr i}"
  with Min_in[OF fin nonempty] have i:"i \<ge> m" "i < ?k" "\<not>(?rl i)" unfolding m_def by auto
  with no_Eq mk have lr_i:"?lr i" by (cases "kind (steps ! i)", auto)
  with rl_m i have im:"i > m" by force
  from less_imp_Suc_add[OF this] obtain j where j:"i = Suc j" by blast
  with im have "m \<le> j" by auto
  with j im Min_le[OF fin] i(2) have "\<not>?lr j" unfolding i_def by force
  with no_Eq i(2) have "?rl j" unfolding j by (cases "kind (steps ! j)", auto)
  with lr_i i(2) show ?thesis unfolding j by auto
qed

lemma proof_simplification:
  assumes gconv: "ground_conversion s P t"
    and nrew: "\<not> rewrite_conversion P"
    and fair:"fair"
  shows "\<exists> Q. ground_conversion s Q t \<and> P \<ggreater> Q"
proof -
  obtain ts steps where P:"P = (ts, steps)" by (cases P, auto)
  from gconv[unfolded P ground_conversion_def split] have
    conv:"conversion s (ts, steps) t" and ground:"\<forall>i\<le>length steps. ground (ts ! i)" by auto
  let ?lr = "\<lambda>i. kind (steps ! i) = Rule_lr \<or> kind (steps ! i) = Eq_gt_lr"
  let ?rl = "\<lambda>i. kind (steps ! i) = Rule_rl \<or> kind (steps ! i) = Eq_gt_rl"
  let ?k = "length steps"
  from nrew[unfolded P rewrite_conversion_def split] have k_gt_0:"?k > 0" by (cases ?k, auto)
  then obtain k' where k':"?k = Suc k'" by (cases ?k, auto)
  show ?thesis proof(cases "\<exists>i < ?k. kind (steps ! i) = Eq")
    (* there is an equation step, which can be replaced by an ordered rewrite step *)
    case True
    then obtain i where i:"i < ?k" "kind (steps ! i) = Eq" by auto
    let ?P1 = "(take (Suc i) ts, take i steps)"
    let ?P2 = "(drop (Suc i) ts, drop (Suc i) steps)"
    from conv_extract_step[OF conv i(1)] have
      P1:"conversion s ?P1 (ts ! i)" and
      Q1:"conversion (ts ! i) ([ts ! i, ts ! Suc i], [steps ! i]) (ts ! Suc i)" (is "conversion _ ?Q1 _") and
      P2:"conversion (ts ! Suc i) ?P2 t" and
      split:"(ts, steps) = (?P1 \<circle> ([ts ! i, ts ! Suc i], [steps ! i])) \<circle> ?P2" (is "_ = ?orig_conv") by auto
    from i(2) obtain rl p where step:"steps ! i = (rl,p,Eq)" by (cases "steps ! i", auto)
    let ?u = "ts ! i"
    let ?v = "ts ! (Suc i)"
    from Q1[unfolded conversion_def split_beta] have valid:"valid_step ?u (rl,p,Eq) ?v" unfolding step by auto
    from P1 ground i have P1g:"ground_conversion s ?P1 (ts ! i)" unfolding ground_conversion_def split by force
    from gconv_suffix[OF gconv[unfolded P]] i(1) have P2g:"ground_conversion (ts ! Suc i) ?P2 t" by force
        (* the equation step is between two ground terms *)
    let ?up = "(ts ! i) |_ p"
    let ?vp = "(ts ! (Suc i)) |_ p"
    have fg:"\<And>t. fground UNIV t = ground t" unfolding fground_def by auto
    obtain l r where rl:"rl = (l,r)" by force
    with valid[unfolded valid_step.simps] have rstep:"(?u,?v) \<in> rstep_pos {(l,r)} p" by auto
    with rstep_rev have rev_rstep:"(?v,?u) \<in> rstep_pos {(r,l)} p" by fast
    from ground i have g:"ground ?u" "ground ?v" by auto
    from rstep[unfolded rstep_pos.simps] ctxt_supt_id have pu:"p \<in> poss ?u" by auto
    from rev_rstep[unfolded rstep_pos.simps] have pv:"p \<in> poss ?v" by auto
    from g ctxt_supt_id[OF pu] ground_ctxt_apply have gup:"ground ?up" by metis
    from g ctxt_supt_id[OF pv] ground_ctxt_apply have gvp:"ground ?vp" by metis
    from fgtotal[unfolded fg, OF gup gvp] have uv:"?up = ?vp \<or> ?up \<succ> ?vp \<or> ?vp \<succ> ?up" by auto
    show ?thesis proof(cases "?vp = ?up")
      (* there is an equation step u = u *)
      case True
      from rstep[unfolded rstep_pos.simps] obtain \<sigma> where v:"?v = (ctxt_of_pos_term p ?u)\<langle>r \<cdot> \<sigma>\<rangle>" by blast
      with replace_at_subt_at[OF pv] replace_at_subt_at[OF pu] ctxt_supt_id[OF pv]
        True ctxt_supt_id[OF pu] have True:"?v = ?u" by force
      with P1 P2 concat have Q1Q2:"conversion s (?P1 \<circle> ?P2) t" by auto
      with gconcat[OF P1g P2g[unfolded True]] have conv:"ground_conversion s (?P1 \<circle> ?P2) t" by auto
      from gt_concat2[OF P1] Q1 P2 True have "?orig_conv \<ggreater> (?P1 \<circle> ?P2)" by simp
      with conv P[unfolded split] show ?thesis unfolding True by fast
    next
      (* there is an equation step u = v between two different terms *)
      case False
      with uv have uv:"?up \<succ> ?vp \<or> ?vp \<succ> ?up" by auto
      let ?step = "(rl, p, if ?up \<succ> ?vp then Eq_gt_lr else Eq_gt_rl)"
      let ?Q2 = "([ts ! i, ts ! Suc i], [?step])"
      from uv valid rev_rstep have "valid_step ?u ?step ?v" unfolding valid_step.simps rl
        using valid_step.simps by force
      with Q1 have Q2':"conversion (ts ! i) ?Q2 (ts ! Suc i)"
        unfolding conversion_def split_beta fst_conv snd_conv using i(2) valid_step.simps by force
      with g have Q2:"ground_conversion (ts ! i) ?Q2 (ts ! Suc i)"
        unfolding ground_conversion_def split_beta fst_conv snd_conv list.size
        using le_SucE by fastforce
      have st:"mset [?u,?v] = {# ?u,?v #}" by auto
      have ts:"mset [?u,?v] = {# ?v,?u #}" by auto
      define c1 where "c1 = c ?u (rl, p, Eq) ?v"
      define c2 where "c2 = c ?u ?step ?v"
      from uv eq_to_rule_step[OF st] eq_to_rule_step[OF ts]
      have "(c1, c2) \<in> C" unfolding c.simps gt_cost_def c1_def c2_def by (cases "?up \<succ> ?vp", auto)
      with mult1_singleton [of "{#c1#}" c2 C]
      have "(mset [c2], mset [c1]) \<in> mult (C\<inverse>)"
        unfolding mset.simps mult_def by blast
      then have gt:"?Q1 \<ggreater> ?Q2"
        unfolding gt_cost_def step cost.simps c1_def c2_def by auto
      from P1g P2g Q2 gconcat have conv:"ground_conversion s ((?P1 \<circle> ?Q2) \<circle> ?P2) t" by blast
      from gt_concat[OF P1 Q1 Q2' P2 gt] have "((?P1 \<circle> ?Q1) \<circle> ?P2) \<ggreater> ((?P1 \<circle> ?Q2) \<circle> ?P2)" by simp
      with conv show ?thesis unfolding P split by fast
    qed
  next
    (* there is no equation step in the conversion *)
    case False
      (* the conversion must have at least two steps, otherwise it would be a rewrite conversion *)
    { assume 0:"k' = 0"
      from False have lr_rl:"?lr 0 \<or> ?rl 0" unfolding k' by (cases "kind (steps ! 0)", auto)
      { assume "?lr 0"
        then have "rewrite_conversion (ts, steps)" unfolding rewrite_conversion_def split k' 0 by blast
      } note lr = this
      { assume "?rl 0"
        then have "rewrite_conversion (ts, steps)" unfolding rewrite_conversion_def split k' 0 by blast
      }
      with lr lr_rl have "rewrite_conversion (ts, steps)" by auto
      with nrew have False unfolding P by auto
    }
    then have k_gt_1:"k' > 0" by auto
        (* get a peak *)
    from non_rewrite_proof_has_peak[OF nrew[unfolded P] False]
    obtain m where m:"Suc m < ?k" "?rl m" "?lr (Suc m)" unfolding P by auto
    let ?P1 = "(take (Suc m) ts, take m steps)"
    let ?P2 = "(drop (Suc (Suc m)) ts, drop (Suc (Suc m)) steps)"
    let ?Q1 = "(take (Suc (Suc (Suc m)) - m) (drop m ts), take (Suc (Suc m) - m) (drop m steps))"
    let ?u = "ts ! m" and ?v = "ts ! Suc (Suc m)" and ?w = "ts ! Suc m"
    from conv_extract_subproof[OF conv,of m "Suc (Suc m)" ] m(1) have
      P1:"conversion s ?P1 ?u" and
      Q1:"conversion ?u ?Q1 ?v" and
      P2:"conversion ?v ?P2 t" and
      split:"(ts, steps) = (?P1 \<circle> ?Q1) \<circle> ?P2" (is "_ = ?orig_conv") by auto
    from m have km:"?k - m \<ge> 2" unfolding k' by auto
    with m have peak:"peak ?u ?Q1 ?v" unfolding peak_def split_beta by force
        (* by fairness, there exists a smaller proof *)
    from conv have l:"length ts = Suc (length steps)" unfolding conversion_def by auto
    from ground m(1) have g:"ground ?u \<and> ground ?w \<and> ground ?v" unfolding ground_conversion_def l by force
    with km nth_drop have "\<forall>i. i \<le> 2 \<longrightarrow> ground (drop m ts ! i)" using ground l by auto
    with Q1 have gQ1:"ground_conversion ?u ?Q1 ?v" unfolding ground_conversion_def split_beta by simp
    with fair peak obtain Q2 where Q2:"ground_conversion ?u Q2 ?v" "?Q1 \<ggreater> Q2" unfolding fair_def by blast
    from P1 ground m have P1g:"ground_conversion s ?P1 ?u" unfolding ground_conversion_def split by force
    from gconv_suffix[OF gconv[unfolded P]] m(1) have P2g:"ground_conversion ?v ?P2 t" by force
    from gconcat P1g Q2(1) P2g have Q2g:"ground_conversion s ((?P1 \<circle> Q2) \<circle> ?P2) t" by blast
    from gt_concat[OF P1 Q1 _ P2 Q2(2)] Q2(1)[unfolded ground_conversion_def]
    have "P \<ggreater> ((?P1 \<circle> Q2) \<circle> ?P2)" unfolding P split by fast
    with Q2g show ?thesis by fast
  qed
qed

definition step_from
  where "step_from step ER \<equiv>
    (case ER of (E,R) \<Rightarrow>
    (case step of
      (lr, _, Eq) \<Rightarrow> lr \<in> E \<or> (snd lr, fst lr) \<in> E
    | (lr, _, Rule_lr) \<Rightarrow> lr \<in> R
    | (lr, _, Rule_rl) \<Rightarrow> lr \<in> R
    | (lr, _, Eq_gt_lr) \<Rightarrow> lr \<in> E \<or> (snd lr, fst lr) \<in> E
    | (lr, _, Eq_gt_rl) \<Rightarrow> lr \<in> E \<or> (snd lr, fst lr) \<in> E))"

definition steps_from :: "('a, 'b) okb_conversion \<Rightarrow> (('a,'b) trs \<times> ('a,'b) trs) \<Rightarrow> bool"
  where
    "steps_from conv ER = (case conv of (ts, steps) \<Rightarrow>
      (\<forall>i<length steps. step_from (steps ! i) ER))"

lemma steps_from_Cons:
  "steps_from (xs, step # steps) (E\<^sub>1, R\<^sub>1) \<longleftrightarrow>
    step_from step (E\<^sub>1, R\<^sub>1) \<and> steps_from (ys, steps) (E\<^sub>1, R\<^sub>1)"
    (is "?L = ?R")
proof
  show "?L \<Longrightarrow> ?R" unfolding steps_from_def split nth_Cons by auto
next
  assume R: "?R"
  show "?L"
  proof (unfold steps_from_def split, intro allI impI)
    fix i
    assume "i < length (step # steps)"
    with R show "step_from ((step # steps) ! i) (E\<^sub>1, R\<^sub>1)"
      unfolding nth_Cons steps_from_def split length_Cons by (cases i) (auto)
  qed
qed

lemma steps_from_subset:
  assumes "E\<^sub>1 \<subseteq> E\<^sub>2"
    and " R\<^sub>1 \<subseteq> R\<^sub>2"
    and "steps_from P (E\<^sub>1, R\<^sub>1)"
  shows "steps_from P (E\<^sub>2, R\<^sub>2)"
proof-
  obtain ts steps where P: "P = (ts, steps)" by force
  { fix i
    assume i: "i < length steps"
    with nth_mem [OF this] obtain rl p kind where step: "steps ! i = (rl, p, kind)"
      using prod_cases3 by blast
    from i assms(3) have "step_from (steps ! i) (E\<^sub>1, R\<^sub>1)" unfolding steps_from_def P split by auto
    with assms(1) assms(2) have "step_from (steps ! i) (E\<^sub>2, R\<^sub>2)" unfolding step_from_def split step
      by (cases kind) (auto)
  }
  then show ?thesis unfolding P steps_from_def split by auto
qed
end
end
