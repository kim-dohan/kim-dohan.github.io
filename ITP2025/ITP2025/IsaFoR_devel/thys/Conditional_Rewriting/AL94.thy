(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

(* AL94 (doi:10.1007/3-540-58216-9_40) *)
text \<open>A formalization of the main results from AL94\<close>
theory AL94
  imports
    Conditional_Critical_Pairs
    Quasi_Decreasingness
    First_Order_Terms.Abstract_Matching
begin

section \<open>Contextual Rewriting\<close>

text \<open>skol replaces a variable `Var x` by a constant `Fun x []` if x is in set V\<close>
fun skol :: "'v set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f + 'v, 'v) term"
where
  "skol V (Var x) = (if x \<in> V then Fun (Inr x) [] else Var x)"
| "skol V (Fun f ts) = Fun (Inl f) (map (skol V) ts)"

fun skol_ctxt :: "'v set \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f + 'v, 'v) ctxt"
where
  "skol_ctxt V Hole = Hole"
| "skol_ctxt V (More f us D vs) = More (Inl f) (map (skol V) us) (skol_ctxt V D) (map (skol V) vs)"

fun deskol :: "('f + 'v, 'v) term \<Rightarrow> ('f ,'v) term"
where
  "deskol (Var x) = Var x"
| "deskol (Fun (Inr x) ts) = Var x"
| "deskol (Fun (Inl f) ts) = Fun f (map deskol ts)"

lemma deskol_skol [simp]:
  "deskol (skol V t) = t"
by (induct rule: skol.induct) (auto simp: map_idI)

definition skol_trs :: "('f, 'v) trs \<Rightarrow> ('f + 'v, 'v) trs"
where
  "skol_trs C = (\<lambda>(l, r). (skol (vars_trs C) l, skol (vars_trs C) r)) ` C"

text \<open>contextual rewrite step. Two terms `s` and `t` are in `ctxt_step R C` if they are in relation
R or there is an rstep in `skol_trs C` from `skol (vars_trs C) s` to
`skol (vars_trs C) t`.\<close>
inductive_set ctxt_step :: "('f, 'v) ctrs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel" for R C
where
  "(skol (vars_trs C) s, skol (vars_trs C) t) \<in> cstep (map_funs_ctrs Inl R \<union> trs2ctrs (skol_trs C)) \<Longrightarrow>
    (s, t) \<in> ctxt_step R C"

lemma skol_inj [dest]:
  "skol V s = skol V t \<Longrightarrow> s = t"
by (metis deskol_skol)

lemma ground_skol_mono:
  assumes "ground (skol V t)"
    and "V \<subseteq> U"
  shows "ground (skol U t)"
using assms
by (induct t rule: skol.induct) (auto split: if_splits)

lemma ground_skol_vars_term:
  "ground (skol (vars_term t) t)"
using ground_skol_mono by (induct t, auto) blast

lemma in_skol_trs_ground:
  assumes "(l, r) \<in> skol_trs C"
  shows "ground l \<and> ground r"
proof -
  from assms obtain s t where s: "skol (vars_trs C) s = l" and t: "skol (vars_trs C) t = r"
    and rule: "(s, t) \<in> C"
    by (auto simp: skol_trs_def)
  have "ground (skol (vars_term s) s)" and "ground (skol (vars_term t) t)"
    using ground_skol_vars_term by auto
  moreover have "vars_term t \<subseteq> vars_trs C" and "vars_term s \<subseteq> vars_trs C" using rule
    by (auto simp: vars_trs_def vars_rule_def)
  ultimately show ?thesis using ground_skol_mono using s t by blast
qed

text \<open>Apply a substitution only to skolemized variables.\<close>
fun ins :: "('f, 'v) subst \<Rightarrow> ('f + 'v, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "ins \<sigma> (Var x) = Var x"
| "ins \<sigma> (Fun (Inr x) ts) = \<sigma> x"
| "ins \<sigma> (Fun (Inl f) ts) = Fun f (map (ins \<sigma>) ts)"

lemma ins_skol [simp]:
  "vars_term t \<subseteq> V \<Longrightarrow> ins \<sigma> (skol V t) = t \<cdot> \<sigma>"
by (induct t) auto

lemma ins_map_funs_term_subst_apply [simp]:
  "ins \<sigma> (map_funs_term Inl t \<cdot> \<tau>) = t \<cdot> (ins \<sigma> \<circ> \<tau>)"
by (induct t) simp_all

lemma cstep_n_imp_ins_csteps:
  assumes "(s, t) \<in> cstep_n (map_funs_ctrs Inl R \<union> trs2ctrs (skol_trs C)) n" (is "_ \<in> cstep_n ?A n")
    and "\<forall>(u, v) \<in> C. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "(ins \<sigma> s, ins \<sigma> t) \<in> (cstep R)\<^sup>*"
using assms(1)
proof (induct n arbitrary: s t)
  case (Suc n)
  then obtain l r cs D \<tau> where "((l, r), cs) \<in> ?A"
    and *: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep_n ?A n)\<^sup>*"
    and s: "s = D\<langle>l \<cdot> \<tau>\<rangle>" and t: "t = D\<langle>r \<cdot> \<tau>\<rangle>" by (blast elim: cstep_n_SucE)
  moreover
  { assume "((l, r), cs) \<in> trs2ctrs (skol_trs C)"
    then have [simp]: "cs = []" and rule: "(l, r) \<in> skol_trs C" by (auto simp: trs2ctrs_def)
    then have [simp]: "l \<cdot> \<tau> = l" "r \<cdot> \<tau> = r"
      by (auto dest!: in_skol_trs_ground simp: ground_subst_apply)
    have "s = D\<langle>l\<rangle>" and "t = D\<langle>r\<rangle>" by (auto simp: s t)
    have C: "(deskol l, deskol r) \<in> C"
      and l: "l = skol (vars_trs C) (deskol l)"
      and r: "r = skol (vars_trs C) (deskol r)"
      and *: "vars_term (deskol l) \<subseteq> vars_trs C" "vars_term (deskol r) \<subseteq> vars_trs C"
      using rule by (auto simp: skol_trs_def vars_defs)
    have "(ins \<sigma> (D\<langle>l\<rangle>), ins \<sigma> (D\<langle>r\<rangle>)) \<in> (cstep R)\<^sup>*"
      apply (induct D)
      apply (simp)
      apply (subst l)
      apply (subst r)
      unfolding ins_skol [OF *(1), of \<sigma>] ins_skol [OF *(2), of \<sigma>]
      using C and assms(2) apply blast
      apply simp
      apply (case_tac x1)
      apply auto
      subgoal for us E vs g
        using csteps_ctxt [of "ins \<sigma> E\<langle>l\<rangle>" "ins \<sigma> E\<langle>r\<rangle>" R "More g (map (ins \<sigma>) us) \<box> (map (ins \<sigma>) vs)"]
        by auto
      done
    then have ?case by (auto simp: s t) }
  moreover
  { assume "((l, r), cs) \<in> map_funs_ctrs Inl R"
    then obtain l' and r' and cs' where rule': "((l', r'), cs') \<in> R"
      and [simp]: "l = map_funs_term Inl l'" "r = map_funs_term Inl r'"
      and cs: "cs = map (map_funs_rule Inl) cs'" by (auto simp: map_funs_crule_def)
    from Suc(1) and * have "\<forall>(u, v) \<in> set cs. (ins \<sigma> (u \<cdot> \<tau>), ins \<sigma> (v \<cdot> \<tau>)) \<in> (cstep R)\<^sup>*"
      using rtrancl_map [where f = "ins \<sigma>" and r = "cstep_n ?A n" and s = "(cstep R)\<^sup>*"] by auto
    then have ?case
      apply (simp add: s t)
      apply (induct D)
      using cstepI [OF rule', where C = \<box> and \<sigma> = "ins \<sigma> \<circ> \<tau>"]
      apply (force simp: cs)
      apply auto
      apply (case_tac x1)
      apply auto
      subgoal for us E vs g
        using csteps_ctxt [of "ins \<sigma> E\<langle>map_funs_term Inl l' \<cdot> \<tau>\<rangle>" "ins \<sigma> E\<langle>map_funs_term Inl r' \<cdot> \<tau>\<rangle>" R "More g (map (ins \<sigma>) us) \<box> (map (ins \<sigma>) vs)"]
        by auto
      done }
  ultimately show ?case by blast
qed simp

lemma skol_UNIV:
  "skol UNIV t = skol V t \<cdot> (\<lambda>x. Fun (Inr x) [])"
by (induct t) simp_all

lemma ins_skol_UNIV [simp]:
  "ins \<sigma> (skol UNIV s) = s \<cdot> \<sigma>"
by (induct s) simp_all

lemma ctxt_step_csteps:
  assumes "(s, t) \<in> ctxt_step R C"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> C. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
proof -
  obtain n where "(skol (vars_trs C) s, skol (vars_trs C) t) \<in> cstep_n (map_funs_ctrs Inl R \<union> trs2ctrs (skol_trs C)) n" (is "_ \<in> cstep_n ?A n")
    using assms by (force elim: ctxt_step.cases simp: cstep_iff)
  then have "(skol UNIV s, skol UNIV t) \<in> cstep_n ?A n"
    unfolding skol_UNIV [of _ "vars_trs C"] using cstep_n_subst by blast
  from cstep_n_imp_ins_csteps [OF this, of \<sigma>, OF assms(2)] show ?thesis by simp
qed

text \<open>Lemma 4.2 from AL94\<close>
lemma ctxt_steps_csteps:
  assumes "(s, t) \<in> (ctxt_step R C)\<^sup>*"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> C. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
using assms(1)
proof (induct rule: rtrancl_induct)
  case (step u v)
  from ctxt_step_csteps [OF step(2) assms(2)] have "(u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" .
  then show ?case using step(1,3) by auto
qed (auto)

text \<open>Definition 4.1 from AL94\<close>
definition strongly_deterministic :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "strongly_deterministic R \<longleftrightarrow> (\<forall> ((l, r), cs) \<in> R. \<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. strongly_irreducible R t\<^sub>i)"

text \<open>Definition 4.1 from AL94\<close>
definition sdtrs :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "sdtrs R \<longleftrightarrow> strongly_deterministic R \<and> wf_ctrs R"

definition all_CPs_joinable
where
  "all_CPs_joinable R = (\<forall>s t cs. ((s, t), cs) \<in> CCP R \<longrightarrow>
    (\<forall>\<sigma>. conds_sat R cs \<sigma> \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>\<down>))"

text \<open>Definition 4.4 from AL94\<close>
definition unfeasible :: "_"
where
  "unfeasible R S r r' p \<longleftrightarrow>
  (let \<sigma> = the (mgu (clhs r |_ p) (clhs r')); C = set (subst_list \<sigma> (snd r @ snd r')) in
    \<exists> t\<^sub>0 t\<^sub>1 t\<^sub>2.
      (\<forall>\<tau>. (\<forall>(u, v)\<in>C. (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*) \<longrightarrow> (clhs r \<cdot> \<sigma> \<cdot> \<tau>, t\<^sub>0 \<cdot> \<tau>) \<in> S) \<and>
      (t\<^sub>0, t\<^sub>1) \<in> (ctxt_step R C)\<^sup>* \<and>
      (t\<^sub>0, t\<^sub>2) \<in> (ctxt_step R C)\<^sup>* \<and>
      \<not> unifiable {(t\<^sub>1, t\<^sub>2)} \<and>
      strongly_irreducible R t\<^sub>1 \<and>
      strongly_irreducible R t\<^sub>2
  )"

text \<open>Definition 4.4 from AL94\<close>
definition context_joinable :: "_"
where
  "context_joinable R r r' p \<longleftrightarrow>
  (let \<sigma> = the (mgu (clhs r |_ p) (clhs r'));
    s = crhs r \<cdot> \<sigma>; t = replace_at (clhs r) p (crhs r') \<cdot> \<sigma>;
    C = set (subst_list \<sigma> (snd r @ snd r')) in
    \<exists> t\<^sub>0. (s, t\<^sub>0) \<in> (ctxt_step R C)\<^sup>* \<and> (t, t\<^sub>0) \<in> (ctxt_step R C)\<^sup>*
  )"

lemma unfeasible_supt_trancl:
  assumes "unfeasible R S r r' p"
  shows "unfeasible R ((S \<union> {\<rhd>})\<^sup>+) r r' p"
using assms by (auto simp: unfeasible_def Let_def)

definition "infeasible R r r' p \<longleftrightarrow>
  (let \<mu> = the (mgu (clhs r |_ p) (clhs r'));
    C = set (subst_list \<mu> (snd r @ snd r')) in
    (\<not> (\<exists>\<tau>. (\<forall>(u, v) \<in> C. (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)))
  )"

definition all_overlaps_nice
where
  "all_overlaps_nice R S = (\<forall> r r' p. overlap R r r' p \<longrightarrow>
    unfeasible R S r r' p \<or>
    context_joinable R r r' p \<or>
    infeasible R r r' p \<or>
    (p = [] \<and> (\<exists>\<pi>. \<pi> \<bullet> r = r'))
  )"

text \<open>easy direction of Theorem 4.1 from AL94 (no need for strong determinism nor quasi-reductivity)\<close>
lemma CR_imp_all_CPs_joinable:
  assumes "CR (cstep R)"
  shows "all_CPs_joinable R"
unfolding all_CPs_joinable_def
proof (intro allI impI)
  fix s t cs \<sigma>
  assume "((s, t), cs) \<in> CCP R" and csat: "conds_sat R cs \<sigma>"
  then obtain \<rho>\<^sub>1 \<rho>\<^sub>2 p \<mu> where s: "s = crhs \<rho>\<^sub>1 \<cdot> \<mu>"
    and t: "t = (ctxt_of_pos_term p (clhs \<rho>\<^sub>1))\<langle>crhs \<rho>\<^sub>2\<rangle> \<cdot> \<mu>"
    and cs: "cs = subst_list \<mu> (conds \<rho>\<^sub>1 @ conds \<rho>\<^sub>2)"
    and o: "overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p"
    and \<mu>: "mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<mu>" by (auto dest: CCP_E)

  let ?s = "replace_at (clhs \<rho>\<^sub>1) p (clhs \<rho>\<^sub>2)"
  let ?t = "replace_at (clhs \<rho>\<^sub>1) p (crhs \<rho>\<^sub>2)"

  from o have p: "p \<in> poss (clhs \<rho>\<^sub>1)" by (auto simp: overlap_def intro: fun_poss_imp_poss)
  from csat have "conds_sat R (conds \<rho>\<^sub>1 @ conds \<rho>\<^sub>2) (\<mu> \<circ>\<^sub>s \<sigma>)"
    (is "conds_sat _ _ ?\<tau>") unfolding cs using conds_sat_subst_list by blast
  then have "conds_sat R (conds \<rho>\<^sub>1) ?\<tau>" and "conds_sat R (conds \<rho>\<^sub>2) ?\<tau>"
    using conds_sat_append by blast+
  moreover obtain q q' where "q \<bullet> \<rho>\<^sub>1 \<in> R" and "q' \<bullet> \<rho>\<^sub>2 \<in> R" using o by (auto simp: overlap_def)
  ultimately have "(clhs \<rho>\<^sub>2 \<cdot> ?\<tau>, crhs \<rho>\<^sub>2 \<cdot> ?\<tau>) \<in> cstep R" and 2: "(clhs \<rho>\<^sub>1 \<cdot> ?\<tau>, crhs \<rho>\<^sub>1 \<cdot> ?\<tau>) \<in> cstep R"
    using variant_conds_sat_cstep by fast+
  then have "(?s \<cdot> ?\<tau>, ?t \<cdot> ?\<tau>) \<in> (cstep R)\<^sup>*" by (auto simp: cstep_ctxt)
  then have "(clhs \<rho>\<^sub>1 \<cdot> ?\<tau>, ?t \<cdot> ?\<tau>) \<in> (cstep R)\<^sup>*" using mgu_sound [OF \<mu>] replace_at_ident [of p "clhs \<rho>\<^sub>1 \<cdot> ?\<tau>"]
    by (auto simp: cstep_ctxt is_imgu_def ctxt_of_pos_term_subst p)
  with 2 have "(crhs \<rho>\<^sub>1 \<cdot> ?\<tau>, ?t \<cdot> ?\<tau>) \<in> (cstep R)\<^sup>\<down>" using assms [unfolded CR_on_def] by blast
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>\<down>" unfolding s t by auto
qed

text \<open>Corresponds to one half of Corollary 3.1 (or 3.3 as it is referred to later) from AL94\<close>
lemma quasi_reductive_order_conds_sat:
  assumes qr: "quasi_reductive_order R S"
    and rule: "((l, r), cs) \<in> R"
    and cs: "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "\<forall>i < length cs. (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> (S \<union> {\<rhd>})\<^sup>+"
proof -
  from quasi_reductive_order_csteps [OF qr] have "(cstep R)\<^sup>* \<subseteq> S\<^sup>=" .
  moreover from qr [unfolded quasi_reductive_order_def]
    have *: "\<forall>l r cs \<sigma>. ((l, r), cs) \<in> R \<longrightarrow>
    (\<forall>i < length cs. (\<forall>j <i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S\<^sup>=) \<longrightarrow>
    (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> (S \<union> {\<rhd>})\<^sup>+)" by blast
  ultimately have "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S\<^sup>=" using cs by blast
  then have "\<forall>i < length cs. \<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S\<^sup>=" by force
  with * rule show ?thesis by auto
qed

text \<open>This is where all the technical details of Theorems 4.1 and 4.2 from AL94 are handled.\<close>
lemma aux_lemma:
  fixes l\<^sub>1 :: "('f, 'v :: infinite) term"
  assumes qro: "quasi_decreasing_order R S"
    and allCPs: "all_CPs_joinable R \<or> all_overlaps_nice R S"
    and SDTRS: "sdtrs R"
    and r1: "((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" (is "?\<rho>\<^sub>1 \<in> _")
    and cs1: "\<forall>(s, t) \<in> set cs\<^sub>1. (s \<cdot> \<sigma>\<^sub>1, t \<cdot> \<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*"
    and C: "t = C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
    and C': "t\<^sub>1 = C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
    and r2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R" (is "?\<rho>\<^sub>2 \<in> _")
    and cs2: "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*"
    and D: "t = D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
    and D': "t\<^sub>2 = D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
    and q: "hole_pos C = q"
    and p: "hole_pos D = p"
    and GE: "q \<le>\<^sub>p p"
    and IH: "\<And>y t' t''. (y, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse> \<Longrightarrow> (y, t') \<in> (cstep R)\<^sup>*
      \<Longrightarrow> (y, t'') \<in> (cstep R)\<^sup>* \<Longrightarrow> (t', t'') \<in> (cstep R)\<^sup>\<down>"
  shows "(t\<^sub>1, t\<^sub>2) \<in> (cstep R)\<^sup>\<down>"
proof -
  have tq': "t |_q = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using C q by fastforce
  have s1: "(l\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> cstep R" and s2: "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> cstep R"
    by (auto intro: cstepI [OF r1 cs1, of _ \<box>] cstepI [OF r2 cs2, of _ \<box>])
  from GE have r: "p = q @ pos_diff p q" (is "_ = _ @ ?r") by simp
  consider (ST) "t \<rhd> t |_q" | (EQ) "t = t |_q" using C hole_pos_poss q subt_at_imp_supteq by blast
  then show ?thesis
  proof (cases)
    case (ST)
    from GE ST have st: "t |_q \<unrhd> t |_p" using D hole_pos_poss less_eq_pos_imp_supt_eq p by blast 
    have *: "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = replace_at (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) ?r (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
    proof -
      have "hole_pos (D |_c q) = pos_diff p q" using r hole_pos_subt_at_ctxt p by blast
      then show ?thesis by (metis D r tq' ctxt_of_pos_term_hole_pos p subt_at_subt_at_ctxt)
    qed
    have "(t |_q, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" using ST by blast
    moreover have "(t |_q, r\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*" unfolding tq' using s1 by blast
    moreover have "(t |_q, replace_at (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) ?r (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) \<in> (cstep R)\<^sup>*" (is "(_, ?t2) \<in> _")
      unfolding tq' by (metis * csteps_ctxt r_into_rtrancl s2)
    ultimately have j: "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, ?t2) \<in> (cstep R)\<^sup>\<down>" using IH by simp
    then obtain s where "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, s) \<in> (cstep R)\<^sup>*" and "(?t2, s) \<in> (cstep R)\<^sup>*" by blast
    then have "(replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1), replace_at t q s) \<in> (cstep R)\<^sup>*"
      and "(replace_at t q ?t2, replace_at t q s) \<in> (cstep R)\<^sup>*" by (simp add: csteps_ctxt)+
    moreover have "t\<^sub>1 = replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using C C' q by auto
    moreover have "t\<^sub>2 = replace_at t q ?t2" using r
      by (metis C D D' ctxt_ctxt ctxt_of_pos_term_append ctxt_of_pos_term_hole_pos hole_pos_poss p q tq')
    ultimately show ?thesis by blast
  next
    case (EQ)
    have t: "t = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using EQ tq' by simp
    have tp': "t |_ p = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using D p by fastforce
    consider (\<alpha>) "p \<in> fun_poss l\<^sub>1" | (\<beta>) "p \<notin> fun_poss l\<^sub>1" by auto
    then show ?thesis
    proof (cases)
      case (\<alpha>)
      from vars_crule_disjoint obtain \<pi> where \<pi>: "vars_crule (\<pi> \<bullet> ?\<rho>\<^sub>1) \<inter> vars_crule ?\<rho>\<^sub>2 = {}" ..

      define l r cs \<sigma> where "l \<equiv> \<pi> \<bullet> l\<^sub>1" and "r \<equiv> \<pi> \<bullet> r\<^sub>1" and "cs \<equiv> \<pi> \<bullet> cs\<^sub>1" and "\<sigma> \<equiv> sop (-\<pi>) \<circ>\<^sub>s \<sigma>\<^sub>1"
      note rename = l_def r_def cs_def \<sigma>_def
      
      have *: "-\<pi> \<bullet> ((l, r), cs) \<in> R" (is "-\<pi> \<bullet> ?\<rho> \<in> R") and "0 \<bullet> ?\<rho>\<^sub>2 \<in> R"
        using r1 r2 by (simp_all add: eqvt rename o_def)
      then have rule_variants: "\<exists>\<pi>. \<pi> \<bullet> ?\<rho> \<in> R" "\<exists>\<pi>. \<pi> \<bullet> ?\<rho>\<^sub>2 \<in> R" by blast+
      have disj: "vars_crule ?\<rho> \<inter> vars_crule ?\<rho>\<^sub>2 = {}" using \<pi> by (auto simp: eqvt rename)
      from cs1 have cs: "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
        by (auto simp: rename rule_pt.permute_prod.simps) blast
        
      from \<alpha> have fun_poss: "p \<in> fun_poss (clhs ?\<rho>)" by (simp add: rename)
      then have poss: "p \<in> poss l" by (auto dest: fun_poss_imp_poss)
      with vars_term_subt_at [OF this] and disj
        have "vars_term (l |_ p) \<inter> vars_term l\<^sub>2 = {}" and "(l |_ p) \<cdot> \<sigma> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
        apply (auto simp: eqvt vars_crule_def vars_rule_def rename) using EQ tp' tq' by auto
      from vars_term_disjoint_imp_unifier [OF this] obtain \<tau> where mgu: "mgu (l |_ p) l\<^sub>2 = Some \<tau>"
        using mgu_complete by (auto simp: unifiers_def)
      consider (improp) "p = [] \<and> (\<exists>\<pi>. \<pi> \<bullet> ?\<rho> = ?\<rho>\<^sub>2)" | (proper) "\<not> p = [] \<or> \<not> (\<exists>\<pi>. \<pi> \<bullet> ?\<rho> = ?\<rho>\<^sub>2)" by blast
      then show ?thesis
      proof (cases)
        case (improp)
        then have t': "t = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" and t: "t = l \<cdot> \<sigma>" "t = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using t \<open>l |_ p \<cdot> \<sigma> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> tp' by auto
        obtain \<pi>' where "\<pi>' \<bullet> ?\<rho> = ?\<rho>\<^sub>2" using improp by auto
        then have "(\<pi>' + \<pi>) \<bullet> ?\<rho>\<^sub>1 = ?\<rho>\<^sub>2" (is "?\<pi> \<bullet> ((_, _), _) = _") using rename by (auto simp: eqvt)
        then have "l\<^sub>2 = ?\<pi> \<bullet> l\<^sub>1" "r\<^sub>2 = ?\<pi> \<bullet> r\<^sub>1" "cs\<^sub>2 = ?\<pi> \<bullet> cs\<^sub>1" by (auto simp: eqvt)
        then have ren'': "l\<^sub>1 = -?\<pi> \<bullet> l\<^sub>2" "r\<^sub>1 = -?\<pi> \<bullet> r\<^sub>2" "r\<^sub>1 = -?\<pi> \<bullet> r\<^sub>2"
          by (auto) (metis term_pt.permute_minus_cancel(2) term_pt.permute_plus)+
        then have ren_cs: "cs\<^sub>1 = -?\<pi> \<bullet> cs\<^sub>2" using \<open>cs\<^sub>2 = ?\<pi> \<bullet> cs\<^sub>1\<close> rules_pt.permute_flip by blast
        have l2subst: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = l\<^sub>2 \<cdot> sop (-?\<pi>) \<circ>\<^sub>s \<sigma>\<^sub>1" (is "_ = _ \<cdot> ?\<sigma>\<^sub>1")
          using t t' ren'' by (auto simp: eqvt)
        from this [symmetric] have substl: "\<forall>x \<in> vars_term l\<^sub>2. ?\<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
          using term_subst_eq_rev by blast
  
        have "t = l\<^sub>2 \<cdot> ?\<sigma>\<^sub>1" using l2subst t(2) by blast
        have "t\<^sub>1 = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" by (metis C C' EQ intp_actxt.simps(1) ctxt_supt supt_neqD tq')
        then have t1: "t\<^sub>1 = r\<^sub>2 \<cdot> ?\<sigma>\<^sub>1" using ren'' by simp
        have t2: "t\<^sub>2 = r\<^sub>2 \<cdot> \<sigma>\<^sub>2" using improp by (metis D' p subt_at.simps(1) subt_at_hole_pos)

        obtain \<sigma>\<^sub>1' where norm_\<sigma>\<^sub>1': "normalized R \<sigma>\<^sub>1'" and \<sigma>\<^sub>1': "\<forall>x. (?\<sigma>\<^sub>1 x, \<sigma>\<^sub>1' x) \<in> (cstep R)\<^sup>*"
          and \<sigma>\<^sub>1'_def: "\<sigma>\<^sub>1' = (\<lambda>x. some_NF (cstep R) (?\<sigma>\<^sub>1 x))"
          using quasi_decreasing_obtains_normalized_subst [OF qro] by auto
        obtain \<sigma>\<^sub>2' where norm_\<sigma>\<^sub>2': "normalized R \<sigma>\<^sub>2'" and \<sigma>\<^sub>2': "\<forall>x. (\<sigma>\<^sub>2 x, \<sigma>\<^sub>2' x) \<in> (cstep R)\<^sup>*"
          and \<sigma>\<^sub>2'_def: "\<sigma>\<^sub>2' = (\<lambda>x. some_NF (cstep R) (\<sigma>\<^sub>2 x))"
          using quasi_decreasing_obtains_normalized_subst [OF qro] by auto
        
        have cs2'': "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> ?\<sigma>\<^sub>1, t \<cdot> ?\<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*"
          using cs1 [unfolded ren_cs] by (auto simp: eqvt)

        { fix x
  
          let ?det = "\<lambda>x. \<forall>i < length x. vars_term (fst (x ! i)) \<subseteq> vars_term l\<^sub>2 \<union> \<Union>(vars_term ` rhss (set (take i x)))"

          assume "x \<in> evars_crule ?\<rho>\<^sub>2"
          moreover from quasi_decreasing_order_conds_sat [OF qro r2 cs2'']
            have "\<forall>i < length cs\<^sub>2. (fst (cs\<^sub>2 ! i) \<cdot> ?\<sigma>\<^sub>1, l\<^sub>2 \<cdot> ?\<sigma>\<^sub>1) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" by auto
          moreover from quasi_decreasing_order_conds_sat [OF qro r2 cs2]
            have "\<forall>i < length cs\<^sub>2. (fst (cs\<^sub>2 ! i) \<cdot> \<sigma>\<^sub>2, l\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" by auto
          moreover from SDTRS [unfolded sdtrs_def strongly_deterministic_def] r2
            have "\<forall>(u, v) \<in> set cs\<^sub>2. strongly_irreducible R v" by fast
          moreover from SDTRS [unfolded sdtrs_def wf_ctrs_def dctrs_def X_vars_def] r2
            have "?det cs\<^sub>2" by fastforce
          ultimately have "\<sigma>\<^sub>1' x = \<sigma>\<^sub>2' x" using cs2 cs2''
          proof (induct cs\<^sub>2 arbitrary: x rule: List.rev_induct)
            case Nil
            then show ?case by (auto simp: evars_crule_def vars_trs_def)
          next
            case (snoc d ds)
            then have "\<forall>i < length ds. (fst (ds ! i) \<cdot> ?\<sigma>\<^sub>1, l\<^sub>2 \<cdot> ?\<sigma>\<^sub>1) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>"
              unfolding nth_append by (simp split: if_splits add: o_def)
            moreover have "\<forall>i < length ds. (fst (ds ! i) \<cdot> \<sigma>\<^sub>2, l\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>"
              using snoc unfolding nth_append by (simp split: if_splits add: o_def)
            moreover have "\<forall>(u, v) \<in> set ds. strongly_irreducible R v" using snoc by auto
            moreover have "?det ds"
              using snoc unfolding take_append nth_append by (auto split: if_splits)
            moreover have "\<forall>(s,t) \<in> set ds. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*"
              using snoc by fastforce
            moreover have "\<forall>(s,t) \<in> set ds. (s \<cdot> ?\<sigma>\<^sub>1, t \<cdot> ?\<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*"
              using snoc by fastforce
            ultimately have IH': "\<And>y. y\<in> evars_crule ((l\<^sub>2, r\<^sub>2), ds) \<Longrightarrow> \<sigma>\<^sub>1' y = \<sigma>\<^sub>2' y"
              using snoc by blast
            consider (DS) "x \<in> evars_crule ((l\<^sub>2, r\<^sub>2), ds)"
              | (U) u where "x \<in> vars_term u" "u = fst d"
              | (V) v where "x \<in> vars_term v" "v = snd d"
              using snoc by (auto simp: evars_crule_def vars_trs_def vars_rule_def)
            then show ?case
            proof (cases)
              case (U)
              then have "x \<in> vars_term l\<^sub>2 \<union> \<Union>(vars_term ` rhss (set (take (length ds) (ds @ [d]))))"
                using snoc(6) by fastforce
              then have "x \<in> evars_crule ((l\<^sub>2, r\<^sub>2), ds)" using snoc by (auto simp: evars_crule_def vars_defs)
              with IH' show ?thesis .
            next
              case (V)
              let ?u = "fst d"
              { fix y
                assume "y \<in> vars_term ?u"
                then have "y \<in> vars_term l\<^sub>2 \<union> \<Union>(vars_term ` rhss (set (take (length ds) (ds @ [d]))))"
                  using snoc(6) by fastforce
                then consider (L) "y \<in> vars_term l\<^sub>2" | (E) "y \<in> evars_crule ((l\<^sub>2, r\<^sub>2), ds)"
                  by (auto simp: evars_crule_def vars_defs)
                then have "(?\<sigma>\<^sub>1 y, \<sigma>\<^sub>2 y) \<in> (cstep R)\<^sup>\<down>"
                proof (cases)
                  case (E)
                  with IH' show ?thesis using \<sigma>\<^sub>1' \<sigma>\<^sub>2' joinI by auto
                qed (auto simp: substl)
              }
              then have "(?u \<cdot> ?\<sigma>\<^sub>1, ?u \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>\<down>" using term_subst_csteps_join by blast
              then obtain s\<^sub>0 where u1: "(?u \<cdot> ?\<sigma>\<^sub>1, s\<^sub>0) \<in> (cstep R)\<^sup>*" and u2: "(?u \<cdot> \<sigma>\<^sub>2, s\<^sub>0) \<in> (cstep R)\<^sup>*" by blast
              have d': "(fst d, snd d) \<in> set (ds @ [d])" by simp
              then have "(?u \<cdot> ?\<sigma>\<^sub>1, v \<cdot> ?\<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*" unfolding V(2) using snoc by fastforce
              moreover have "(v \<cdot> ?\<sigma>\<^sub>1, v \<cdot> \<sigma>\<^sub>1') \<in> (cstep R)\<^sup>*" using substs_csteps [OF \<sigma>\<^sub>1' [rule_format]] by fast
              ultimately have u1': "(?u \<cdot> ?\<sigma>\<^sub>1, v \<cdot> \<sigma>\<^sub>1') \<in> (cstep R)\<^sup>*" by fastforce
              have "(?u \<cdot> ?\<sigma>\<^sub>1, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" using snoc unfolding \<open>t = l\<^sub>2 \<cdot> ?\<sigma>\<^sub>1\<close>
                by (metis in_set_conv_nth prod.collapse d')
              then have "(v \<cdot> \<sigma>\<^sub>1', s\<^sub>0) \<in> (cstep R)\<^sup>\<down>" using u1' u1 IH by blast
              then obtain s\<^sub>1 where s1': "(v \<cdot> \<sigma>\<^sub>1', s\<^sub>1) \<in> (cstep R)\<^sup>*" and s1: "(s\<^sub>0, s\<^sub>1) \<in> (cstep R)\<^sup>*" by auto
              have "(?u \<cdot> \<sigma>\<^sub>2, v \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*" unfolding V(2) using snoc(7) d' by blast
              moreover have "(v \<cdot> \<sigma>\<^sub>2, v \<cdot> \<sigma>\<^sub>2') \<in> (cstep R)\<^sup>*" using substs_csteps [OF \<sigma>\<^sub>2' [rule_format]] by fast
              ultimately have "(?u \<cdot> \<sigma>\<^sub>2, v \<cdot> \<sigma>\<^sub>2') \<in> (cstep R)\<^sup>*" by simp
              moreover have "(fst d \<cdot> \<sigma>\<^sub>2, s\<^sub>1) \<in> (cstep R)\<^sup>*" using u2 s1 by auto
              moreover have "(?u \<cdot> \<sigma>\<^sub>2, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" using snoc unfolding t(2)
                by (metis in_set_conv_nth prod.collapse d')
              ultimately have "(s\<^sub>1, v \<cdot> \<sigma>\<^sub>2') \<in> (cstep R)\<^sup>\<down>" using IH by blast
              then have "(v \<cdot> \<sigma>\<^sub>1', v \<cdot> \<sigma>\<^sub>2') \<in> (cstep R)\<^sup>\<down>" using s1' rtrancl_join_join by metis
              moreover have "v \<cdot> \<sigma>\<^sub>1' \<in> NF (cstep R)" "v \<cdot> \<sigma>\<^sub>2' \<in> NF (cstep R)"
                using snoc(5) d' V norm_\<sigma>\<^sub>1' norm_\<sigma>\<^sub>2' by (auto simp: strongly_irreducible_def)
              ultimately show ?thesis by (meson V(1) join_NF_imp_eq term_subst_eq_rev)
            qed (auto simp: IH')
          qed
        }
        then have evars_join: "\<forall>x \<in> evars_crule ?\<rho>\<^sub>2. \<sigma>\<^sub>1' x = \<sigma>\<^sub>2' x" by auto
        have "vars_term r\<^sub>2 \<subseteq> vars_term l\<^sub>2 \<union> vars_trs (set cs\<^sub>2)"
          using SDTRS [unfolded sdtrs_def wf_ctrs_def type3_def] r2 fst_conv snd_conv by fastforce
        then have "vars_crule ?\<rho>\<^sub>2 = evars_crule ?\<rho>\<^sub>2 \<union> vars_term l\<^sub>2" unfolding evars_crule_def
          by (auto simp: vars_crule_def vars_rule_def)
        then have "\<forall>x \<in> vars_crule ?\<rho>\<^sub>2. (\<sigma>\<^sub>1' x, \<sigma>\<^sub>2' x) \<in> (cstep R)\<^sup>\<down>"
          using evars_join substl \<sigma>\<^sub>1' \<sigma>\<^sub>2' \<sigma>\<^sub>1'_def \<sigma>\<^sub>2'_def by auto
        then have "\<forall>x \<in> vars_crule ?\<rho>\<^sub>2. (?\<sigma>\<^sub>1 x, \<sigma>\<^sub>2 x) \<in> (cstep R)\<^sup>\<down>"
          by (meson \<sigma>\<^sub>1' \<sigma>\<^sub>2' join_rtrancl_join rtrancl_join_join)
        then have "\<forall>x \<in> vars_term r\<^sub>2. (?\<sigma>\<^sub>1 x, \<sigma>\<^sub>2 x) \<in> (cstep R)\<^sup>\<down>"
          by (auto simp: vars_crule_def vars_rule_def)
        then show ?thesis unfolding t1 t2 by (meson term_subst_csteps_join)
      next
        case (proper)
        define \<sigma>' where "\<sigma>' \<equiv> \<lambda>x. if x \<in> vars_crule ?\<rho> then \<sigma> x else \<sigma>\<^sub>2 x"
        have unif: "l\<^sub>2 \<cdot> \<sigma>' = (l |_ p) \<cdot> \<sigma>'"
        proof -
          note coinc = coincidence_lemma' [of l\<^sub>2 "vars_crule ?\<rho>\<^sub>2"]
          have disj: "vars_crule ?\<rho>\<^sub>2 \<inter> vars_term (l |_ p) = {}"
            using vars_term_subt_at [OF poss] and disj
            by (auto simp: vars_crule_def vars_rule_def)
          have "l\<^sub>2 \<cdot> \<sigma>' = l\<^sub>2 \<cdot> (\<sigma>' |s vars_crule ?\<rho>\<^sub>2)"
            using coinc by (simp add: vars_crule_def vars_rule_def sup_assoc)
          also have "\<dots> = l\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_crule ?\<rho>\<^sub>2)" apply (simp add: \<sigma>'_def)
            by (metis (no_types) \<pi> crule_pt.permute_prod.simps cs_def l_def r_def
                rule_pt.permute_prod.simps subst_restrict_restrict)
          also have "\<dots> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using coinc by (simp add: vars_crule_def vars_rule_def) blast
          also have "\<dots> = (l \<cdot> \<sigma>) |_ p" by (simp add: \<open>l |_ p \<cdot> \<sigma> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> poss)
          also have "\<dots> = (l |_ p) \<cdot> \<sigma>" by (simp add: \<open>l |_ p \<cdot> \<sigma> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> \<open>l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = l \<cdot> \<sigma> |_ p\<close>) 
          also have "\<dots> = (l |_ p) \<cdot> (\<sigma> |s vars_term (l |_ p))"
            by (simp add: coincidence_lemma [symmetric])
          also have "\<dots> = (l |_ p) \<cdot> (\<sigma>' |s vars_term (l |_ p))" using disj
            by (simp add: \<sigma>'_def) (metis (no_types) \<open>vars_term (l |_ p) \<subseteq> vars_term l\<close>
                coincidence_lemma coincidence_lemma' fst_conv subst_restrict_vars sup.coboundedI1
                vars_crule_def vars_rule_def)
          finally show ?thesis by (simp add: coincidence_lemma [symmetric])
        qed
        from is_imgu_imp_is_mgu [OF mgu_sound [OF mgu]] have "is_mgu \<tau> {(l |_ p, l\<^sub>2)}" .
        with unif obtain \<delta> where \<sigma>': "\<sigma>' = \<tau> \<circ>\<^sub>s \<delta>" by (auto simp: is_mgu_def unifiers_def) presburger

        have ccp: "((r \<cdot> \<tau>, (ctxt_of_pos_term p l)\<langle>r\<^sub>2\<rangle> \<cdot> \<tau>), subst_list \<tau> (cs @ cs\<^sub>2)) \<in> CCP R"
          using proper CCP_I [OF rule_variants disj fun_poss] mgu by simp

        have t1: "t\<^sub>1 = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" by (metis C C' intp_actxt.simps(1) ctxt_supt
            subterm.dual_order.strict_implies_not_eq t)
        from t tp' have "t = (ctxt_of_pos_term p (l\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
          by (metis \<alpha> ctxt_supt_id fun_poss_imp_poss poss_imp_subst_poss)
        then have **: "D = ctxt_of_pos_term p (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using p D
          using ctxt_of_pos_term_hole_pos t by force
        then have t2: "t\<^sub>2 = (ctxt_of_pos_term p (l\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
          using D' [unfolded **] by simp
        from rename have "\<sigma>\<^sub>1 = sop \<pi> \<circ>\<^sub>s \<sigma>" unfolding subst_compose_def o_def
          by (metis inv_Rep_perm_simp permute_atom_def eval_term.simps(1))
        from t1 rename have "t\<^sub>1 = (-\<pi>) \<bullet> r \<cdot> (sop \<pi> \<circ>\<^sub>s \<sigma>)" by force
        then have t1': "t\<^sub>1 = r \<cdot> \<sigma>'" using \<sigma>'_def
          by (simp add: UnCI term_subst_eq_conv vars_crule_def vars_defs(2))
        from t2 rename have "t\<^sub>2 = (ctxt_of_pos_term p (l \<cdot> \<sigma>))\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" by force
        moreover have "l \<cdot> \<sigma> = l \<cdot> \<sigma>'" using \<sigma>'_def
          by (simp add: UnCI term_subst_eq_conv vars_crule_def vars_defs(2))
        moreover have "r\<^sub>2 \<cdot> \<sigma>\<^sub>2 = r\<^sub>2 \<cdot> \<sigma>'" using disj
          by (induct r\<^sub>2) (auto simp: \<sigma>'_def vars_crule_def vars_rule_def)
        ultimately have t2': "t\<^sub>2 = (ctxt_of_pos_term p l)\<langle>r\<^sub>2\<rangle> \<cdot> \<sigma>'"
          by (simp add: ctxt_of_pos_term_subst poss)

        { fix s t
          assume a: "(s, t) \<in> set cs"
          moreover have "\<forall>(s, t) \<in> set cs. \<forall>x \<in> vars_term s \<union> vars_term t. \<sigma> x = \<sigma>' x"
            by (fastforce simp: \<sigma>'_def vars_crule_def vars_trs_def vars_rule_def)
          ultimately have "\<forall>x \<in> vars_term s. \<sigma> x = \<sigma>' x" and "\<forall>x \<in> vars_term t. \<sigma> x = \<sigma>' x" by auto
          moreover have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" using cs a by fast
          ultimately have "(s \<cdot> \<sigma>', t \<cdot> \<sigma>') \<in> (cstep R)\<^sup>*" using term_subst_eq by metis
        }
        moreover
        { fix s t
          assume a: "(s, t) \<in> set cs\<^sub>2"
          moreover have "\<forall>(s, t) \<in> set cs\<^sub>2. \<forall>x \<in> vars_term s \<union> vars_term t. \<sigma>\<^sub>2 x = \<sigma>' x"
            using disj by (fastforce simp: \<sigma>'_def vars_crule_def vars_trs_def vars_rule_def)
          ultimately have "\<forall>x \<in> vars_term s. \<sigma>\<^sub>2 x = \<sigma>' x" and "\<forall>x \<in> vars_term t. \<sigma>\<^sub>2 x = \<sigma>' x" by auto
          moreover have "(s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*" using cs2 a by fast
          ultimately have "(s \<cdot> \<sigma>', t \<cdot> \<sigma>') \<in> (cstep R)\<^sup>*" using term_subst_eq by metis
        }
        ultimately have "\<forall>(s, t) \<in> set (cs @ cs\<^sub>2). (s \<cdot> \<sigma>', t \<cdot> \<sigma>') \<in> (cstep R)\<^sup>*" by auto
        then have 3: "conds_sat R (subst_list \<tau> (cs @ cs\<^sub>2)) \<delta>"
          using conds_sat_iff conds_sat_subst_list \<sigma>' by blast
        (* difference to 4.1 start *)
        consider (cps_join) "all_CPs_joinable R" | (ovs_nice) "all_overlaps_nice R S" using allCPs ..
        then show ?thesis
        proof (cases)
          case cps_join
          with ccp 3 have "(r \<cdot> \<tau> \<cdot> \<delta>, (ctxt_of_pos_term p l)\<langle>r\<^sub>2\<rangle> \<cdot> \<tau> \<cdot> \<delta>) \<in> (cstep R)\<^sup>\<down>"
          unfolding all_CPs_joinable_def by blast
          then have join: "(r \<cdot> \<sigma>', (ctxt_of_pos_term p l)\<langle>r\<^sub>2\<rangle> \<cdot> \<sigma>') \<in> (cstep R)\<^sup>\<down>" using \<sigma>' by simp
          from join t1' t2' show ?thesis by simp
        next
          case ovs_nice
          (* changes from Theorem 4.1 to 4.2 are here:
          "The only point we have to consider is the first case (proper) in (\<alpha>):" *)
          from 3 have sat: "\<forall>(s, t) \<in> set (subst_list \<tau> (cs @ cs\<^sub>2)). (s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> (cstep R)\<^sup>*"
            (is "\<forall>_ \<in> ?C. _") using conds_sat_iff by blast
          consider (unf) "unfeasible R S ?\<rho> ?\<rho>\<^sub>2 p"
                 | (cjn) "context_joinable R ?\<rho> ?\<rho>\<^sub>2 p"
          (* we also want to allow infeasible CCPs in general *)
                 | (inf) "infeasible R ?\<rho> ?\<rho>\<^sub>2 p"
            using proper ovs_nice [unfolded all_overlaps_nice_def] ccp
            by (metis * \<open>0 \<bullet> ?\<rho>\<^sub>2 \<in> R\<close> disj fst_conv fun_poss mgu overlapI)
          then show ?thesis
          proof (cases)
            case (unf)
            then obtain t\<^sub>0 t\<^sub>0' t\<^sub>0''
              where *: "\<forall>\<gamma>. (\<forall>(u, v) \<in> ?C. (u \<cdot> \<gamma>, v \<cdot> \<gamma>) \<in> (cstep R)\<^sup>*) \<longrightarrow> (clhs ?\<rho> \<cdot> \<tau> \<cdot> \<gamma>, t\<^sub>0 \<cdot> \<gamma>) \<in> S"
              and ctxts: "(t\<^sub>0, t\<^sub>0') \<in> (ctxt_step R ?C)\<^sup>*" "(t\<^sub>0, t\<^sub>0'') \<in> (ctxt_step R ?C)\<^sup>*"
              and nu: "\<not> unifiable {(t\<^sub>0', t\<^sub>0'')}"
              and si: "strongly_irreducible R t\<^sub>0'" "strongly_irreducible R t\<^sub>0''"
              unfolding unfeasible_def by (metis fst_conv mgu option.sel snd_conv)

            obtain \<mu> where norm_\<mu>: "normalized R \<mu>" and \<mu>: "\<forall>x. (\<delta> x, \<mu> x) \<in> (cstep R)\<^sup>*"
              using quasi_decreasing_obtains_normalized_subst [OF qro] by auto

            have "(t\<^sub>0 \<cdot> \<delta>, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>"
              using \<sigma>' \<open>\<sigma>\<^sub>1 = sop \<pi> \<circ>\<^sub>s \<sigma>\<close> \<open>l \<cdot> \<sigma> = l \<cdot> \<sigma>'\<close> l_def t * sat by auto
            moreover have "(t\<^sub>0 \<cdot> \<delta>, t\<^sub>0' \<cdot> \<mu>) \<in> (cstep R)\<^sup>*" and "(t\<^sub>0 \<cdot> \<delta>, t\<^sub>0'' \<cdot> \<mu>) \<in> (cstep R)\<^sup>*"
              using ctxt_steps_csteps [OF _ sat] ctxts \<mu> substs_csteps rtrancl_trans by metis+
            ultimately have "(t\<^sub>0' \<cdot> \<mu>, t\<^sub>0'' \<cdot> \<mu>) \<in> (cstep R)\<^sup>\<down>" using IH by blast
            moreover have "t\<^sub>0' \<cdot> \<mu> \<noteq> t\<^sub>0'' \<cdot> \<mu>" using nu unfolding unifiable_def unifiers_def by auto
            ultimately show ?thesis using si by (simp add: strongly_irreducible_def norm_\<mu> join_NF_imp_eq)
          next
            let ?s\<^sub>1 =  "crhs ?\<rho> \<cdot> \<tau>"
            let ?s\<^sub>2 = "(ctxt_of_pos_term p (clhs ?\<rho>))\<langle>crhs ?\<rho>\<^sub>2\<rangle> \<cdot> \<tau>"
            case (cjn)
            then obtain t\<^sub>0 where "(?s\<^sub>1, t\<^sub>0) \<in> (ctxt_step R ?C)\<^sup>*" and "(?s\<^sub>2, t\<^sub>0) \<in> (ctxt_step R ?C)\<^sup>*"
              unfolding context_joinable_def by (metis fst_conv mgu option.sel snd_conv)
            then show ?thesis using ctxt_steps_csteps [OF _ sat]
              by (auto simp add: \<sigma>' t1' t2' simp del: ctxt_subst_subst) 
                (metis eval_ctxt joinI)
          next
            (* not in original proof, but straight-forward *)
            case (inf)
            then show ?thesis using sat mgu unfolding infeasible_def by force
          qed
        qed
        (* difference to 4.2 end *)
      qed
    next
      case (\<beta>)
      have "p \<in> poss (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using D p t by auto
      then obtain q\<^sub>1 q\<^sub>2 x where [simp]: "p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss l\<^sub>1"
        and l\<^sub>1q\<^sub>1: "l\<^sub>1 |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma>\<^sub>1 x)"
        using poss_subst_apply_term [OF _ \<beta>] by blast
      moreover have [simp]: "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 |_ p = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using tp' [unfolded t] .
      ultimately have [simp]: "\<sigma>\<^sub>1 x |_ q\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" by simp
  
      have \<sigma>1step: "(\<sigma>\<^sub>1 x, replace_at (\<sigma>\<^sub>1 x) q\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) \<in> cstep R" (is "(_, ?t\<^sub>0) \<in> _")
        using cstep_ctxt s2 by (metis \<open>\<sigma>\<^sub>1 x |_ q\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> ctxt_supt_id q\<^sub>2)

      define \<tau> where "\<tau> \<equiv> \<lambda>y. if y = x then ?t\<^sub>0 else \<sigma>\<^sub>1 y"

      obtain \<tau>' where norm_\<tau>': "normalized R \<tau>'" and \<tau>': "\<forall>x. (\<tau> x, \<tau>' x) \<in> (cstep R)\<^sup>*"
        using quasi_decreasing_obtains_normalized_subst [OF qro] by auto

      have *: "\<And>x. (\<sigma>\<^sub>1 x, \<tau> x) \<in> (cstep R)\<^sup>*" by (auto simp: \<sigma>1step \<tau>_def)

      have "(t\<^sub>2, l\<^sub>1 \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
      proof -
        have "replace_at (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2) = replace_at (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) q\<^sub>1 (\<tau> x)"
          using q\<^sub>1 by (simp add: \<tau>_def ctxt_of_pos_term_append l\<^sub>1q\<^sub>1)
        moreover have "(replace_at (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) q\<^sub>1 (\<tau> x), l\<^sub>1 \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
          by (rule replace_at_subst_csteps [OF * q\<^sub>1 l\<^sub>1q\<^sub>1])
        ultimately show ?thesis by (metis D D' ctxt_of_pos_term_hole_pos p t)
      qed
      then have t2csteps: "(t\<^sub>2, l\<^sub>1 \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" unfolding t using \<tau>'
        by (meson * rtrancl_trans substs_csteps)

      have "\<forall>x \<in> vars_term r\<^sub>1. (\<sigma>\<^sub>1 x, \<tau> x) \<in> (cstep R)\<^sup>*" using * \<sigma>1step rtrancl.simps by auto
      then have "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" using term_subst_csteps [of r\<^sub>1 \<sigma>\<^sub>1 \<tau>] by blast
      then have "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using \<tau>' by (meson rtrancl_trans substs_csteps)
      then have t1csteps: "(t\<^sub>1, r\<^sub>1 \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using t s1
        by (metis C C' intp_actxt.simps(1) ctxt_supt supt_neqD)

      { fix u v
        assume a: "(u, v) \<in> set cs\<^sub>1"

        have "\<forall>i < length cs\<^sub>1. (fst (cs\<^sub>1 ! i) \<cdot> \<sigma>\<^sub>1, l\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>"
          using quasi_decreasing_order_conds_sat [OF qro r1 cs1] by auto
        then have "(u \<cdot> \<sigma>\<^sub>1, t) \<in> ((S \<union> {\<rhd>})\<^sup>+)\<inverse>" unfolding t using a by (metis fst_conv in_set_idx)
        moreover have "(u \<cdot> \<sigma>\<^sub>1, v \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using a cs1 * substs_csteps
          by (metis (lifting) \<tau>' case_prod_conv rtrancl_trans)
        moreover have "(u \<cdot> \<sigma>\<^sub>1, u \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" by (meson * \<tau>' rtrancl_trans substs_csteps)
        ultimately have "(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (cstep R)\<^sup>\<down>" using IH by blast
        moreover have "v \<cdot> \<tau>' \<in> NF (cstep R)"
          using SDTRS [unfolded sdtrs_def strongly_deterministic_def] r1 a norm_\<tau>'
          by (auto simp: strongly_irreducible_def split: prod.splits)
        ultimately have "(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" by (simp add: NF_join_imp_reach)
      }
      then have "(l\<^sub>1 \<cdot> \<tau>', r\<^sub>1 \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" by (auto intro!: cstepI [OF r1, of \<tau>' _ \<box>])
      then show ?thesis using t1csteps t2csteps joinI rtrancl_trans by auto
    qed
  qed
qed

text \<open>Theorem 4.1 from AL94, but using quasi-decreasingness\<close>
theorem quasi_decreasing_sdtrs_all_CPs_joinable_CR:
  assumes sdtrs: "sdtrs R"
    and qd: "quasi_decreasing R"
    and allCPs: "all_CPs_joinable R"
  shows "CR (cstep R)"
proof -
  { fix t t' t''
    from qd obtain S where qdo: "quasi_decreasing_order R S" by (auto simp: quasi_decreasing_def)
    then have SNS: "SN S" by (auto simp: quasi_decreasing_order_def)
    then have "SN ((S \<union> {\<rhd>})\<^sup>+)" (is "SN ?S")
    proof -
      have "{\<rhd>} \<subseteq> S"
        using qdo quasi_decreasing_order_def by blast
      then show ?thesis
        by (simp add: SNS SN_imp_SN_trancl subset_Un_eq sup_commute)
    qed
    from qdo have trans: "trans S" and RsubS: "cstep R \<subseteq> S"
      by (auto simp: quasi_decreasing_order_def)
    then have *: "cstep R \<subseteq> ?S" using qdo quasi_decreasing_order_def by auto

    from allCPs have **: "all_CPs_joinable R \<or> all_overlaps_nice R S" ..

    assume 1: "(t, t') \<in> (cstep R)\<^sup>*" and 2: "(t, t'') \<in> (cstep R)\<^sup>*"
    then have "(t', t'') \<in> (cstep R)\<^sup>\<down>"
    proof (induct t arbitrary: t' t'' rule: wf_induct[OF SN_imp_wf[OF \<open>SN ?S\<close>], rule_format])
      case (1 t)
      note IH = this(1)
      { assume "t = t' \<or> t = t''"
        then have "(t', t'') \<in> (cstep R)\<^sup>\<down>" using 1 2 by blast
      }
      moreover
      { assume "\<exists>t\<^sub>1. (t, t\<^sub>1) \<in> cstep R \<and> (t\<^sub>1, t') \<in> (cstep R)\<^sup>*"
          and "\<exists>t\<^sub>2. (t, t\<^sub>2) \<in> cstep R \<and> (t\<^sub>2, t'') \<in> (cstep R)\<^sup>*"
        then obtain t\<^sub>1 t\<^sub>2 where t11: "(t, t\<^sub>1) \<in> cstep R" and t12:"(t\<^sub>1, t') \<in> (cstep R)\<^sup>*"
          and t21: "(t, t\<^sub>2) \<in> cstep R" and t22: "(t\<^sub>2, t'') \<in> (cstep R)\<^sup>*" by blast
        from t11 obtain n' where "(t, t\<^sub>1) \<in> cstep_n R n'" using cstep_iff by blast 
        from cstep_nE [OF this] obtain C l\<^sub>1 r\<^sub>1 \<sigma>\<^sub>1 cs\<^sub>1 n
          where r1: "((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R"
          and "n' = Suc n"
          and cs1: "\<forall>(s, t) \<in> set cs\<^sub>1. (s \<cdot> \<sigma>\<^sub>1, t \<cdot> \<sigma>\<^sub>1) \<in> (cstep_n R n)\<^sup>*"
          and C: "t = C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
          and C': "t\<^sub>1 = C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>" by metis
        from t21 obtain m' where "(t, t\<^sub>2) \<in> cstep_n R m'" using cstep_iff by blast
        from cstep_nE [OF this] obtain D l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2 cs\<^sub>2 m
          where r2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
          and "m' = Suc m"
          and cs2: "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep_n R m)\<^sup>*"
          and D: "t = D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
          and D': "t\<^sub>2 = D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" by metis
        from cstep_n_SucI [OF r1 cs1, of "l\<^sub>1 \<cdot> \<sigma>\<^sub>1" \<box> "r\<^sub>1 \<cdot> \<sigma>\<^sub>1"]
          have s1: "(l\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> cstep R" by (simp add: cstep_n_imp_cstep)
        from cstep_n_SucI [OF r2 cs2, of "l\<^sub>2 \<cdot> \<sigma>\<^sub>2" \<box> "r\<^sub>2 \<cdot> \<sigma>\<^sub>2"]
          have s2: "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> cstep R" by (simp add: cstep_n_imp_cstep)
        obtain q p where q: "hole_pos C = q" and p: "hole_pos D = p" by simp
        have tq': "t |_q = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using C q by fastforce
        from cs1 have cs1': "\<forall>(s, t) \<in> set cs\<^sub>1. (s \<cdot> \<sigma>\<^sub>1, t \<cdot> \<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*"
          using csteps_n_imp_csteps by blast
        from cs2 have cs2': "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*"
          using csteps_n_imp_csteps by blast
        consider (GE) "q \<le>\<^sub>p p" | (LE) "p \<le>\<^sub>p q" | (PL) "q \<bottom> p" using parallel_pos by blast 
        then have "(t\<^sub>1, t\<^sub>2) \<in> (cstep R)\<^sup>\<down>"
        proof (cases)
          case (GE)
          from aux_lemma [OF qdo ** sdtrs r1 cs1' C C' r2 cs2' D D' q p GE IH]
            show ?thesis .
        next
          case (LE)
          from aux_lemma [OF qdo ** sdtrs r2 cs2' D D' r1 cs1' C C' p q LE IH]
            have "(t\<^sub>2, t\<^sub>1) \<in> (cstep R)\<^sup>\<down>" .
          then show ?thesis by auto
        next
          case (PL)
          from C D q p have tpar: "replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) = replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
            using hole_pos_id_ctxt by fastforce
          have *: "t = replace_at (replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using C tpar q by auto
          have **: "t = replace_at (replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using C tpar q by auto
          then have "C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = replace_at (replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using * C by blast
          then have "C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
            by (metis C D PL ctxt_of_pos_term_hole_pos hole_pos_poss p parallel_replace_at q)
          then have t1: "t\<^sub>1 = replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using C' by blast
          have 1: "(t\<^sub>1, replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) \<in> cstep R"
            (is "(_, ?t4) \<in> _") unfolding t1 using s2 by (simp add: cstep_ctxt)
          from ** have "D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = replace_at (replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using D by blast
          then have "D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
            using D p tpar by (metis C PL ctxt_of_pos_term_hole_pos hole_pos_poss parallel_replace_at q)
          then have t2: "t\<^sub>2 = replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using D' by blast
          have 2: "(t\<^sub>2, replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) \<in> cstep R"
            (is "(_, ?t3) \<in> _") unfolding t2 using s1 by (simp add: cstep_ctxt)
          have "?t3 = ?t4" using PL by (metis C D hole_pos_poss p parallel_replace_at q)
          then show ?thesis using 1 2 by auto
        qed
        then obtain s where s01: "(t\<^sub>1, s) \<in> (cstep R)\<^sup>*" and s02: "(t\<^sub>2, s) \<in> (cstep R)\<^sup>*" by blast
        from t11 * have "(t\<^sub>1, t) \<in> ?S\<inverse>" by blast
        from IH [OF this s01 t12] have "(s, t') \<in> (cstep R)\<^sup>\<down>" .
        then obtain s' where s11: "(t', s') \<in> (cstep R)\<^sup>*" and s12: "(s, s') \<in> (cstep R)\<^sup>*" by blast
        from t21 * have t2tqr: "(t\<^sub>2, t) \<in> ?S\<inverse>" by blast
        have "(t\<^sub>2, s') \<in> (cstep R)\<^sup>*" using s02 s12 by force
        from IH [OF t2tqr this t22] have "(s', t'') \<in> (cstep R)\<^sup>\<down>" .
        with s11 have "(t', t'') \<in> (cstep R)\<^sup>\<down>" by (simp add: rtrancl_join_join)
      }
      ultimately show "(t', t'') \<in> (cstep R)\<^sup>\<down>" using 1 2 converse_rtranclE by metis
    qed
  }
  then show "CR (cstep R)" unfolding CR_on_def by force
qed

text \<open>Theorem 4.1 from AL94\<close>
theorem quasi_reductive_sdtrs_all_CPs_joinable_CR:
  assumes sdtrs: "sdtrs R"
    and qd: "quasi_reductive R"
    and allCPs: "all_CPs_joinable R"
  shows "CR (cstep R)"
using assms
by (blast dest: quasi_reductive_quasi_decreasing quasi_decreasing_sdtrs_all_CPs_joinable_CR)

definition absolutely_irreducible :: "('f, 'v :: infinite) ctrs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "absolutely_irreducible R v \<longleftrightarrow> (\<forall>\<rho> \<in> R. \<forall>p \<in> fun_poss v.
    \<forall>\<pi>. vars_term (\<pi> \<bullet> clhs \<rho>) \<inter> vars_term (v |_ p) = {} \<longrightarrow> \<not> unifiable {(v |_ p, \<pi> \<bullet> clhs \<rho>)})"

definition absolutely_deterministic :: "('f, 'v :: infinite) ctrs \<Rightarrow> bool"
where
  "absolutely_deterministic R \<longleftrightarrow> (\<forall>\<rho> \<in> R. \<forall>(u, v) \<in> set (conds \<rho>). absolutely_irreducible R v)"

lemma disj_vars_not_unifiable:
  assumes "vars_term (\<pi> \<bullet> t) \<inter> vars_term (s) = {}"
    and "\<not> unifiable {(s, \<pi> \<bullet> t)}"
    and "vars_term (\<pi>' \<bullet> t) \<inter> vars_term (s) = {}"
  shows "\<not> unifiable {(s, \<pi>' \<bullet> t)}"
proof
  assume "unifiable {(s, \<pi>' \<bullet> t)}"
  then obtain \<sigma> \<tau> :: "('b, 'a) subst" where "s \<cdot> \<sigma> = (\<pi>' \<bullet> t) \<cdot> \<tau>" unfolding unifiable_def by auto
  also have "\<dots> = (\<pi> \<bullet> t) \<cdot> (sop (\<pi>' + -\<pi>) \<circ>\<^sub>s \<tau>)" by auto
  finally obtain \<mu> where "(\<pi> \<bullet> t) \<cdot> \<mu> = s \<cdot> \<sigma>" by metis
  from vars_term_disjoint_imp_unifier [OF assms(1) this] and assms(2) show "False"
    by (auto simp add: unifiable_def unifiers_def) metis
qed

(* TODO: move (?) *)
lemma disj_vars_term_matchers_unifieres:
  assumes disj: "vars_term s \<inter> vars_term t = {}"
    and matcher: "\<sigma> \<in> matchers {(s, t)}"
  shows "(\<sigma> |s vars_term s) \<in> unifiers {(t, s)}" (is "?\<sigma> \<in> _")
proof -
  from matcher have "s \<cdot> \<sigma> = t" unfolding matchers_def by force
  moreover have "s \<cdot> \<sigma> = s \<cdot> (\<sigma> |s vars_term s)" using coincidence_lemma by blast
  ultimately have "s \<cdot> ?\<sigma> = t \<cdot> ?\<sigma>" using disj by (simp add: inf_commute subst_apply_id')
  then show ?thesis unfolding unifiers_def by auto
qed

text \<open>Lemma 4.1a from AL94\<close>
lemma absolutely_irreducible_strongly_irreducible:
  assumes "absolutely_irreducible R v"
    and vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "strongly_irreducible R v"
proof (rule ccontr)
  assume "\<not> strongly_irreducible R v"
  then obtain \<tau> where norm: "normalized R \<tau>" and "\<not> v \<cdot> \<tau> \<in> NF (cstep R)" (is "\<not> ?v \<in> _")
    unfolding strongly_irreducible_def by blast
  then obtain v' where "(?v, v') \<in> (cstep R)" by blast
  from cstepE[OF this] obtain C \<sigma> l r cs where rule: "((l, r), cs) \<in> R"
    and cs: "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
    and v: "?v = C\<langle>l \<cdot> \<sigma>\<rangle>" and "v' = C\<langle>r \<cdot> \<sigma>\<rangle>" by metis
  then obtain p where "hole_pos C = p" and p: "p \<in> poss ?v" by auto
  with v norm have match: "?v |_ p = l \<cdot> \<sigma>" unfolding normalized_def by fastforce
  with p have "is_Fun (?v |_ p)" using rule vc by (cases l) auto
  then have p': "p \<in> fun_poss ?v" using poss_is_Fun_fun_poss p by blast
  have pfv: "p \<in> fun_poss v"
  proof (rule ccontr)
    assume "p \<notin> fun_poss v"
    with p' [THEN fun_poss_imp_poss] obtain q x where "\<tau> x |_ q = l \<cdot> \<sigma>" and "q \<in> poss (\<tau> x)"
      using match by (auto elim!: poss_subst_apply_term)
    with cstepI [OF rule cs] have "(\<tau> x, (ctxt_of_pos_term q (\<tau> x))\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (cstep R)"
      by auto (metis replace_at_ident)
    then show "False" using norm by (auto simp: normalized_def)
  qed
  then have pv: "p \<in> poss v" using fun_poss_imp_poss by auto
  have "\<exists>\<pi>. vars_term (\<pi> \<bullet> l) \<inter> (vars_term (?v |_ p) \<union> vars_term (v |_ p)) = {}"
  proof -
    obtain \<pi> where "term_pt.supp (\<pi> \<bullet> l) \<sharp> (?v |_ p, v |_ p)"
      by (metis finite_term_supp rule_fs.atom_set_avoiding supp_vars_term_eq vars_term_eqvt)
    from rule_pt.fresh_set_disjoint [OF this]
      show ?thesis by (auto simp: supp_vars_rule_eq vars_rule_def supp_vars_term_eq)
  qed
  then obtain \<pi> where disj: "vars_term (\<pi> \<bullet> l) \<inter> vars_term (?v |_ p) = {}"
    and disj': "vars_term (\<pi> \<bullet> l) \<inter> vars_term (v |_ p) = {}" by blast
  from match have \<sigma>: "\<sigma> \<in> matchers {(l, ?v |_ p)}" unfolding matchers_def by auto
  then have "sop (-\<pi>) \<circ>\<^sub>s \<sigma> \<in> matchers {(\<pi> \<bullet> l, ?v |_ p)}" (is "?\<sigma> \<in> _") unfolding matchers_def by auto
  from disj_vars_term_matchers_unifieres [OF disj this]
    have "?\<sigma> |s vars_term (\<pi> \<bullet> l) \<in> unifiers {(?v |_ p, \<pi> \<bullet> l)}" (is "?\<sigma>' \<in> _") .
  then have "?v |_ p \<cdot> ?\<sigma>' = \<pi> \<bullet> l \<cdot> ?\<sigma>'" unfolding unifiers_def by fastforce
  moreover have "?v |_ p \<cdot> ?\<sigma>' = v |_ p \<cdot> (\<tau> |s vars_term (v |_ p)) \<circ>\<^sub>s ?\<sigma>'" (is "_ = _ \<cdot> ?\<tau> \<circ>\<^sub>s _")
    using pv by (metis (no_types) coincidence_lemma subst_subst subt_at_subst)
  moreover have "\<pi> \<bullet> l \<cdot> ?\<sigma>' = \<pi> \<bullet> l \<cdot> ?\<tau> \<circ>\<^sub>s ?\<sigma>'" (is "_ = _ \<cdot> ?\<tau>'")
    using disj' by (simp add: subst_apply_id')
  ultimately have "v |_ p \<cdot> ?\<tau>' = \<pi> \<bullet> l \<cdot> ?\<tau>'" by auto
  then have "?\<tau>' \<in> unifiers {(v |_ p, \<pi> \<bullet> l)}" unfolding unifiers_def by auto
  then have "unifiable {(v |_ p, \<pi> \<bullet> l)}" unfolding unifiable_def by auto
  moreover from assms(1) [unfolded absolutely_irreducible_def] have "\<not> unifiable {(v |_ p, \<pi> \<bullet> l)}"
    using rule pfv fst_conv disj' by auto
  ultimately show "False" by auto
qed

text \<open>Lemma 4.1b from AL94\<close>
lemma absolutely_deterministic_strongly_deterministic:
  assumes "absolutely_deterministic R"
    and vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "strongly_deterministic R"
proof -
  { fix \<rho>
    assume "\<rho> \<in> R"
    with assms have *: "\<forall>(u, v) \<in> set (conds \<rho>). absolutely_irreducible R v"
      by (auto simp: absolutely_deterministic_def)
    { fix u v
      assume "(u, v) \<in> set (conds \<rho>)"
      then have "absolutely_irreducible R v" using * by fast
      from absolutely_irreducible_strongly_irreducible [OF this vc]
        have "strongly_irreducible R v" .
    }
    then have "\<forall>(u, v) \<in> set (conds \<rho>). strongly_irreducible R v" by auto
  }
  then have "\<forall> ((l, r), cs) \<in> R. \<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. strongly_irreducible R t\<^sub>i"
    by (simp add: case_prodI2)
  then show ?thesis by (auto simp: strongly_deterministic_def)
qed

text \<open>Theorem 4.2 from AL94, but using infeasibility and quasi-decreasingness\<close>
theorem quasi_decreasing_order_sdtrs_all_CPs_unfeasible_or_context_joinable_or_infeasible_CR:
  assumes sdtrs: "sdtrs R"
    and qdo: "quasi_decreasing_order R S"
    and allCPs: "all_overlaps_nice R S"
  shows "CR (cstep R)"
proof -
  from allCPs have **: "all_CPs_joinable R \<or> all_overlaps_nice R S" ..
  { fix t t' t''
    from qdo have SNS: "SN S" by (auto simp: quasi_decreasing_order_def)
    then have "SN ((S \<union> {\<rhd>})\<^sup>+)" (is "SN ?S")
    proof -
      have "{\<rhd>} \<subseteq> S"
        using qdo quasi_decreasing_order_def by blast
      then show ?thesis
        by (simp add: SNS SN_imp_SN_trancl subset_Un_eq sup_commute)
    qed
    from qdo have trans: "trans S" and RsubS: "cstep R \<subseteq> S"
      by (auto simp: quasi_decreasing_order_def)
    then have *: "cstep R \<subseteq> ?S" using qdo quasi_decreasing_order_def by auto

    assume 1: "(t, t') \<in> (cstep R)\<^sup>*" and 2: "(t, t'') \<in> (cstep R)\<^sup>*"
    then have "(t', t'') \<in> (cstep R)\<^sup>\<down>"
    proof (induct t arbitrary: t' t'' rule: wf_induct[OF SN_imp_wf[OF \<open>SN ?S\<close>], rule_format])
      case (1 t)
      note IH = this(1)
      { assume "t = t' \<or> t = t''"
        then have "(t', t'') \<in> (cstep R)\<^sup>\<down>" using 1 2 by blast
      }
      moreover
      { assume "\<exists>t\<^sub>1. (t, t\<^sub>1) \<in> cstep R \<and> (t\<^sub>1, t') \<in> (cstep R)\<^sup>*"
          and "\<exists>t\<^sub>2. (t, t\<^sub>2) \<in> cstep R \<and> (t\<^sub>2, t'') \<in> (cstep R)\<^sup>*"
        then obtain t\<^sub>1 t\<^sub>2 where t11: "(t, t\<^sub>1) \<in> cstep R" and t12:"(t\<^sub>1, t') \<in> (cstep R)\<^sup>*"
          and t21: "(t, t\<^sub>2) \<in> cstep R" and t22: "(t\<^sub>2, t'') \<in> (cstep R)\<^sup>*" by blast
        from t11 obtain n' where "(t, t\<^sub>1) \<in> cstep_n R n'" using cstep_iff by blast 
        from cstep_nE [OF this] obtain C l\<^sub>1 r\<^sub>1 \<sigma>\<^sub>1 cs\<^sub>1 n
          where r1: "((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R"
          and "n' = Suc n"
          and cs1: "\<forall>(s, t) \<in> set cs\<^sub>1. (s \<cdot> \<sigma>\<^sub>1, t \<cdot> \<sigma>\<^sub>1) \<in> (cstep_n R n)\<^sup>*"
          and C: "t = C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
          and C': "t\<^sub>1 = C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>" by metis
        from t21 obtain m' where "(t, t\<^sub>2) \<in> cstep_n R m'" using cstep_iff by blast
        from cstep_nE [OF this] obtain D l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2 cs\<^sub>2 m
          where r2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
          and "m' = Suc m"
          and cs2: "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep_n R m)\<^sup>*"
          and D: "t = D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
          and D': "t\<^sub>2 = D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" by metis
        from cstep_n_SucI [OF r1 cs1, of "l\<^sub>1 \<cdot> \<sigma>\<^sub>1" \<box> "r\<^sub>1 \<cdot> \<sigma>\<^sub>1"]
          have s1: "(l\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> cstep R" by (simp add: cstep_n_imp_cstep)
        from cstep_n_SucI [OF r2 cs2, of "l\<^sub>2 \<cdot> \<sigma>\<^sub>2" \<box> "r\<^sub>2 \<cdot> \<sigma>\<^sub>2"]
          have s2: "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> cstep R" by (simp add: cstep_n_imp_cstep)
        obtain q p where q: "hole_pos C = q" and p: "hole_pos D = p" by simp
        have tq': "t |_q = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using C q by fastforce
        from cs1 have cs1': "\<forall>(s, t) \<in> set cs\<^sub>1. (s \<cdot> \<sigma>\<^sub>1, t \<cdot> \<sigma>\<^sub>1) \<in> (cstep R)\<^sup>*"
          using csteps_n_imp_csteps by blast
        from cs2 have cs2': "\<forall>(s, t) \<in> set cs\<^sub>2. (s \<cdot> \<sigma>\<^sub>2, t \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>*"
          using csteps_n_imp_csteps by blast
        consider (GE) "q \<le>\<^sub>p p" | (LE) "p \<le>\<^sub>p q" | (PL) "q \<bottom> p" using parallel_pos by blast 
        then have "(t\<^sub>1, t\<^sub>2) \<in> (cstep R)\<^sup>\<down>"
        proof (cases)
          case (GE)
          from aux_lemma [OF qdo ** sdtrs r1 cs1' C C' r2 cs2' D D' q p GE IH]
            show ?thesis .
        next
          case (LE)
          from aux_lemma [OF qdo ** sdtrs r2 cs2' D D' r1 cs1' C C' p q LE IH]
            have "(t\<^sub>2, t\<^sub>1) \<in> (cstep R)\<^sup>\<down>" .
          then show ?thesis by auto
        next
          case (PL)
          from C D q p have tpar: "replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) = replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
            using hole_pos_id_ctxt by fastforce
          have *: "t = replace_at (replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using C tpar q by auto
          have **: "t = replace_at (replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using C tpar q by auto
          then have "C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = replace_at (replace_at t q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using * C by blast
          then have "C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
            by (metis C D PL ctxt_of_pos_term_hole_pos hole_pos_poss p parallel_replace_at q)
          then have t1: "t\<^sub>1 = replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using C' by blast
          have 1: "(t\<^sub>1, replace_at (replace_at t q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) \<in> cstep R"
            (is "(_, ?t4) \<in> _") unfolding t1 using s2 by (simp add: cstep_ctxt)
          from ** have "D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = replace_at (replace_at t p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using D by blast
          then have "D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
            using D p tpar by (metis C PL ctxt_of_pos_term_hole_pos hole_pos_poss parallel_replace_at q)
          then have t2: "t\<^sub>2 = replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" using D' by blast
          have 2: "(t\<^sub>2, replace_at (replace_at t p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)) q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)) \<in> cstep R"
            (is "(_, ?t3) \<in> _") unfolding t2 using s1 by (simp add: cstep_ctxt)
          have "?t3 = ?t4" using PL by (metis C D hole_pos_poss p parallel_replace_at q)
          then show ?thesis using 1 2 by auto
        qed
        then obtain s where s01: "(t\<^sub>1, s) \<in> (cstep R)\<^sup>*" and s02: "(t\<^sub>2, s) \<in> (cstep R)\<^sup>*" by blast
        from t11 * have "(t\<^sub>1, t) \<in> ?S\<inverse>" by blast
        from IH [OF this s01 t12] have "(s, t') \<in> (cstep R)\<^sup>\<down>" .
        then obtain s' where s11: "(t', s') \<in> (cstep R)\<^sup>*" and s12: "(s, s') \<in> (cstep R)\<^sup>*" by blast
        from t21 * have t2tqr: "(t\<^sub>2, t) \<in> ?S\<inverse>" by blast
        have "(t\<^sub>2, s') \<in> (cstep R)\<^sup>*" using s02 s12 by force
        from IH [OF t2tqr this t22] have "(s', t'') \<in> (cstep R)\<^sup>\<down>" .
        with s11 have "(t', t'') \<in> (cstep R)\<^sup>\<down>" by (simp add: rtrancl_join_join)
      }
      ultimately show "(t', t'') \<in> (cstep R)\<^sup>\<down>" using 1 2 converse_rtranclE by metis
    qed
  }
  then show "CR (cstep R)" unfolding CR_on_def by force
qed

text \<open>Theorem 4.2 from AL94, but using quasi-decreasingness\<close>
theorem quasi_decreasing_order_sdtrs_all_CPs_unfeasible_or_context_joinable_CR:
  assumes sdtrs: "sdtrs R"
    and qdo: "quasi_decreasing_order R S"
    and allCPs: "\<forall> r r' p. overlap R r r' p \<longrightarrow> unfeasible R S r r' p \<or> context_joinable R r r' p"
  shows "CR (cstep R)"
proof -
  from assms quasi_decreasing_order_sdtrs_all_CPs_unfeasible_or_context_joinable_or_infeasible_CR
    show ?thesis unfolding all_overlaps_nice_def by blast
qed

text \<open>Theorem 4.2 from AL94\<close>
theorem quasi_reductive_order_sdtrs_all_CPs_unfeasible_or_context_joinable_CR:
  assumes sdtrs: "sdtrs R"
    and qro: "quasi_reductive_order R S"
    and allCPs: "\<forall> r r' p. overlap R r r' p \<longrightarrow> unfeasible R S r r' p \<or> context_joinable R r r' p"
  shows "CR (cstep R)"
proof -
  from quasi_reductive_order_quasi_decreasing_order [OF qro]
    have qdo: "quasi_decreasing_order R ((S \<union> {\<rhd>})\<^sup>+)" .
  moreover have "\<forall> r r' p. overlap R r r' p \<longrightarrow> unfeasible R ((S \<union> {\<rhd>})\<^sup>+) r r' p \<or> context_joinable R r r' p"
    using allCPs unfeasible_supt_trancl by blast
  ultimately show ?thesis using quasi_decreasing_order_sdtrs_all_CPs_unfeasible_or_context_joinable_CR sdtrs
    by blast
qed

text \<open>Theorem 4.2 from AL94, but using absolute determinism, infeasibility and quasi-decreasingness\<close>
theorem quasi_decreasing_order_adtrs_all_CPs_unfeasible_or_context_joinable_or_infeasible_CR:
  assumes wf_ctrs: "wf_ctrs R"
    and ad: "absolutely_deterministic R"
    and qdo: "quasi_decreasing_order R S"
    and allCPs: "all_overlaps_nice R S"
  shows "CR (cstep R)"
proof -
  from wf_ctrs [unfolded wf_ctrs_def] ad absolutely_deterministic_strongly_deterministic wf_ctrs
    have "sdtrs R" unfolding sdtrs_def by auto
  with assms and quasi_decreasing_order_sdtrs_all_CPs_unfeasible_or_context_joinable_or_infeasible_CR
    show ?thesis by blast
qed

end
