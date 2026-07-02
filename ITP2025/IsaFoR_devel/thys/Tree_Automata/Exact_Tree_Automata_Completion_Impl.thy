(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2019)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Exact_Tree_Automata_Completion_Impl
  imports
    Exact_Tree_Automata_Completion
    TRS.Signature_Extension
    Tree_Automata_Impl
begin

lemma fground_rsteps:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes "(a, 0) \<in> F"
    and rsteps: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
    and "funas_trs R \<subseteq> F" and "funas_term s \<subseteq> F" and "funas_term t \<subseteq> F"
  shows "\<exists>\<sigma> \<tau>. fground F (s \<cdot> \<sigma>) \<and> fground F (t \<cdot> \<tau>) \<and> (s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
proof -
  interpret cleaning_const F "\<lambda>_. Fun a []" "Fun a []"
    using assms by (unfold_locales) (auto)
  let ?\<sigma> = "star a \<circ> clean_subst \<sigma>"
  let ?\<tau> = "star a \<circ> clean_subst \<tau>"
  from rsteps_imp_clean_rsteps [OF \<open>funas_trs R \<subseteq> F\<close> rsteps]
    have "(clean_term (s \<cdot> \<sigma>), clean_term (t \<cdot> \<tau>)) \<in> (rstep R)\<^sup>*" .
  then have *: "(s \<cdot> clean_subst \<sigma>, t \<cdot> clean_subst \<tau>) \<in> (rstep R)\<^sup>*"
    using \<open>funas_term s \<subseteq> F\<close> and \<open>funas_term t \<subseteq> F\<close> by (auto simp: sig_step_def)
  from star_rsteps [OF this] have "(s \<cdot> ?\<sigma>, t \<cdot> ?\<tau>) \<in> (rstep R)\<^sup>*" by simp
  moreover have "fground F (s \<cdot> ?\<sigma>)" and "fground F (t \<cdot> ?\<tau>)"
    using \<open>(a, 0) \<in> F\<close> and \<open>funas_term s \<subseteq> F\<close> and \<open>funas_term t \<subseteq> F\<close>
    by (auto simp: funas_term_star_conv funas_term_subst split: if_splits)
  ultimately show ?thesis by blast
qed

lemma set_ta_rules_impl' [simp]: "set (ta_rules_impl' A) = ta_rules (ta_of_ta A)"
by (cases A) auto

lemma (in etac) [simp]: "ta_eps mp_ta = {}" by (auto simp: mp_ta_def)

lemma (in etac) [simp]: "ta_final mp_ta = {}" by (auto simp: mp_ta_def)

(* a list of all assignments from 'a's to 'b's *)
fun combs :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list list"
where
  "combs [] ys = [[]]"
| "combs (x # xs) ys = concat (map (\<lambda>l. (map (\<lambda>y. (x, y) # l) ys)) (combs xs ys))"

value "combs [a,b,c] [x,y,z]"

definition state_substs :: "'v list \<Rightarrow> 'q list \<Rightarrow> ('v \<times> 'q) list list" where
  "state_substs V Q \<equiv> combs V Q"

fun qi' :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('v \<Rightarrow> ('f, 'v) term) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "qi' c t g (Var x) = (if x \<in> vars_term t then g x else star c (Var x))"
| "qi' c t g (Fun f ts) = star c (Fun f ts)"

definition inf_step :: "'f \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('v \<times> (('f, 'v) term)) list list
  \<Rightarrow> (('f, 'v) term, 'f) ta_rule set \<Rightarrow> (('f, 'v) term, 'f) ta_rule set"
where
  "inf_step c R S \<Delta> = \<Union>(set (map (\<lambda>((l, r), \<theta>). (case l of Fun f ls \<Rightarrow>
    (\<lambda>q. TA_rule f (map (\<lambda>li. qi' c r (fun_of \<theta>) li) ls) q) `
    (reachable_states' \<Delta> (fterm r \<cdot> (State \<circ> (fun_of \<theta>)) :: ('f, 'v) crterm))))
    (List.product R S))
  )"

lemma (in etac) qi_qi' [simp]:
  "qi' c t g s = qi t g s"
by (cases s) auto

lemma (in etac) qi_qi'_2:
  assumes "\<forall>x \<in> vars_term t. g x = g' x"
  shows "qi' c t g' s = qi t g s"
using assms by (cases s) auto

lemma (in etac) qi_qi'_3:
  assumes "\<forall>x \<in> vars_term t. g x = g' x"
  shows "qi' c t g' = qi t g"
using qi_qi'_2 [OF assms] by blast


lemma inf_stepE:
  assumes "\<forall>(l, r) \<in> set R. is_Fun l"
    and  "TA_rule f qs q \<in> inf_step c R S \<Delta>"
  obtains ls r \<theta> where "(Fun f ls, r) \<in> set R" and "\<theta> \<in> set S"
    and "q \<in> reachable_states' \<Delta> (fterm r \<cdot> (State \<circ> fun_of \<theta>) ::
      ('b + ('b, 'c) term, 'c) term)"
    and "qs = map (qi' c r (fun_of \<theta>)) ls"
  using assms by (fastforce simp: inf_step_def)

lemma inf_stepI:
  assumes "(Fun f ls, r) \<in> set R" and "\<theta> \<in> set S"
    and "q \<in> reachable_states' \<Delta> (fterm r \<cdot> (State \<circ> fun_of \<theta>) ::
      ('b + ('b, 'c) term, 'c) term)"
    and "qs = map (qi' c r (fun_of \<theta>)) ls"
  shows "TA_rule f qs q \<in> inf_step c R S \<Delta>"
using assms by (auto simp: inf_step_def split: prod.splits term.splits)

lemma inf_step_mono:
  assumes "\<forall>(l, r) \<in> set R. is_Fun l" and "\<Delta> \<subseteq> \<Delta>'"
  shows "inf_step c R S \<Delta> \<subseteq> inf_step c R S \<Delta>'" (is "?L \<subseteq> ?R")
proof
  fix tr
  assume "tr \<in> ?L"
  moreover then obtain f qs q where [simp]: "TA_rule f qs q = tr"
    by (metis Tree_Automata.r_sym.cases)
  ultimately obtain ls r \<theta> where 1: "(Fun f ls, r) \<in> set R" and 2: "\<theta> \<in> set S"
    and rs: "q \<in> reachable_states' \<Delta> (fterm r \<cdot> (State \<circ> fun_of \<theta>) ::
      ('a + ('a, 'b) term, 'b) term)"
    and 3: "qs = map (qi' c r (fun_of \<theta>)) ls"
    using inf_stepE [OF assms(1)] by blast
  have "q \<in> reachable_states' \<Delta>' (fterm r \<cdot> (State \<circ> fun_of \<theta>) ::
      ('a + ('a, 'b) term, 'b) term)"
    using reachable_states'_mono [OF assms(2)] rs by auto
  from inf_stepI [OF 1 2 this 3] have "TA_rule f qs q \<in> inf_step c R S \<Delta>'" .
  then show "tr \<in> ?R" by auto
qed

abbreviation "r_vars R \<equiv> remdups (concat (map (vars_term_list \<circ> snd) R))"

definition graph_of :: "'v list \<Rightarrow> ('v \<Rightarrow> 'q) \<Rightarrow> ('v \<times> 'q) list"
where
  "graph_of V f = map (\<lambda>x. (x, f x)) V"

lemma fun_of_graph_of:
  assumes "x \<in> set V"
  shows "fun_of (graph_of V f) x = f x"
using assms by (induct V) (auto simp: graph_of_def fun_of_def)

lemma combs_graph_of:
  assumes "distinct V"
  shows "set (combs V Q) = {graph_of V f|f. f ` set V \<subseteq> set Q}"
using assms
proof (induct V)
  case (Cons v vs)
  then have "set (combs vs Q) = {graph_of vs f |f. f ` set vs \<subseteq> set Q}" by force
  moreover {
    fix y f
    assume "y \<in> set Q"
      and "f ` set vs \<subseteq> set Q"
    with Cons(2) have "\<exists>g. y = g v \<and> (\<forall>x\<in>set vs. f x = g x) \<and> g v \<in> set Q \<and> g ` set vs \<subseteq> set Q"
    by (intro exI [of _ "\<lambda>x. (if x = v then y else f x)"]) auto
  }
  ultimately show ?case unfolding combs.simps using Cons(2)
  by (simp only: set_concat set_map) (auto simp: graph_of_def)
qed (auto simp: graph_of_def)

definition "sr_impl R = remdups (concat (map (supteq_list \<circ> fst) R))"

definition "lhss_impl R = remdups (map fst R)"

lemma sr_impl [simp]: "set (sr_impl R) = sr (set R)"
by (induct R) (auto simp: sr_def sr_impl_def)

lemma lhss_impl [simp]: "set (lhss_impl R) = lhss (set R)"
by (induct R) (auto simp: lhss_impl_def)

definition "sig_rules_list F c = map (\<lambda>(f, n). TA_rule f (replicate n c) c) F"

lemma sig_rules_list [simp]: "set (sig_rules_list F c) = sig_rules (set F) c"
by (auto simp: sig_rules_list_def sig_rules_def)

fun gi_rules_list :: "('f \<times> nat) list \<Rightarrow> 'f \<Rightarrow> ('f, 'v) term \<Rightarrow> (('f ,'v) term, 'f) ta_rule list"
where
  "gi_rules_list F c (Var x) = sig_rules_list F (Fun c [])"
| "gi_rules_list F c (Fun f ts) =
    TA_rule f (map (star c) ts) (star c (Fun f ts)) # concat (map (gi_rules_list F c) ts)"

lemma gi_rules_list [simp]:
  "set (gi_rules_list F c t) = ground_instances_rules (set F) c t"
by (induct t) (auto)

definition "mp_ta_rules R F c = concat (map (gi_rules_list F c) (lhss_impl R))"

lemma (in etac) mp_ta_rules [simp]:
  assumes "set R' = R" and "set F' = F"
  shows "set (mp_ta_rules R' F' c) = ta_rules (mp_ta)"
using assms by (auto simp: mp_ta_rules_def mp_ta_def)

locale gi_etac =
  etac c F R a A for c F and R :: "('f, 'v) trs" and a and A :: "(('f, 'v) term, 'f) ta" +
  assumes eps_empty: "ta_eps A = {}"
begin

lemma overapproximation_of_\<Delta>\<^sub>C:
  assumes "ta_rules cr_ta \<subseteq> \<Delta>"
    and "set R' = R"
    and "set Q = ta_states cr_ta"
    and "inf_step c R' (state_substs (r_vars R') Q) \<Delta> \<subseteq> \<Delta>" (is "inf_step _ _ ?S _ \<subseteq> _")
  shows "\<Delta>\<^sub>C \<subseteq> \<Delta>"
proof (intro subsetI)
  fix tr
  assume "tr \<in> \<Delta>\<^sub>C"
  then show "tr \<in> \<Delta>"
  proof (induct)
    case (base r)
    then show ?case using assms by auto
  next
    case (step f ls r \<theta> q)
    let ?A = "cr_ta\<lparr>ta_rules := {x \<in> \<Delta>\<^sub>C. x \<in> \<Delta>}\<rparr>"
    have *: "q \<in> reachable_states ?A (fterm r \<cdot> (State \<circ> \<theta>) :: ('f, 'v) crterm)"
      using move_reachable_states [THEN iffD1, OF step(4)] .
    have "ta_eps ?A = {}" using eps_empty by (auto simp: cr_ta_def mp_ta_def)
    from reachable_states_reachable_states'_iff [OF this, THEN iffD1, OF *]
      have 3: "q \<in> reachable_states' {x \<in> \<Delta>\<^sub>C. x \<in> \<Delta>} (fterm r \<cdot> (State \<circ> \<theta>) :: ('f, 'v) crterm)"
      by auto
    have **: "range \<theta> \<subseteq> set Q" using step assms by simp
    let ?V = "r_vars R'"
    let ?\<theta> = "graph_of ?V \<theta>"
    have 9: "\<forall>x \<in> set ?V. \<theta> x = fun_of ?\<theta> x" using fun_of_graph_of [of _ ?V \<theta>] by auto
    have 8: "?\<theta> \<in> {graph_of ?V f |f. f ` set ?V \<subseteq> set Q}" using ** by fast
    have "distinct (r_vars R')" by (auto)
    from combs_graph_of [OF this, of Q]
      have "set (combs ?V Q) = {graph_of ?V f |f. f ` set ?V \<subseteq> set Q}" .
    then have 2: "?\<theta> \<in> set (state_substs ?V Q)" using 8 by (auto simp: state_substs_def)
    have 4: "map (qi' c r (fun_of ?\<theta>)) ls = map (qi' c r (fun_of ?\<theta>)) ls" ..
    from 9 have "(fterm r \<cdot> (State \<circ> \<theta>) :: ('f, 'v) crterm) =
      (fterm r \<cdot> (State \<circ> fun_of ?\<theta>) :: ('f, 'v) crterm)"
      using assms step by (simp add: term_subst_eq_conv)
    with 3 have 7: "q \<in> reachable_states' {x \<in> \<Delta>\<^sub>C. x \<in> \<Delta>} (fterm r \<cdot> (State \<circ> fun_of ?\<theta>) ::
        ('f, 'v) crterm)" by simp
    have "(Fun f ls, r) \<in> set R'" using step assms by fast
    from inf_stepI [OF this 2 7 4]
      have 6: "TA_rule f (map (qi' c r (fun_of ?\<theta>)) ls) q \<in> inf_step c R' ?S {x \<in> \<Delta>\<^sub>C. x \<in> \<Delta>}"
      using assms by auto
    have 5: "{x \<in> \<Delta>\<^sub>C. x \<in> \<Delta>} \<subseteq> \<Delta>" by auto
    have "TA_rule f (map (qi' c r (fun_of ?\<theta>)) ls) q \<in> inf_step c R' ?S \<Delta>"
      using inf_step_mono [OF novar [unfolded assms(2) [symmetric]] 5] 6 by auto
    from assms(4) [THEN subsetD, OF this]
      have "TA_rule f (map (qi' c r (fun_of ?\<theta>)) ls) q \<in> \<Delta>" .
    then show ?case using qi_qi'_3 9 \<open>(Fun f ls, r) \<in> set R'\<close> by auto
  qed
qed

end

lemma finite_states_ground_instances_ta [intro]:
  "finite F \<Longrightarrow> finite (ta_states (ground_instances_ta F c t))"
by (induct t) auto

lemma finite_sig_rules [intro]:
  assumes "finite F"
  shows "finite (sig_rules F c)"
proof -
  have [simp]: "sig_rules F c = (\<lambda>(f, n). TA_rule f (replicate n c) c) ` F"
    by (auto simp: sig_rules_def)
  show ?thesis using assms by simp
qed

lemma finite_ta_rules_ground_instances_ta [intro]:
  "finite F \<Longrightarrow> finite (ta_rules (ground_instances_ta F c t))"
by (induct t) (auto simp: ground_instances_ta_def)

definition "check_rules_subseteq rs A =
  check_subseteq rs (ta_rules_impl' A) <+? (\<lambda>r. showsl_lit (STR ''rule '') \<circ> showsl r \<circ> showsl_lit (STR '' is missing''))"

lemma check_rules_subseteq [simp]:
  "isOK (check_rules_subseteq rs A) \<longleftrightarrow> set rs \<subseteq> set (ta_rules_impl' A)"
by (auto simp: check_rules_subseteq_def)

definition "add_rule_states rs ss =
  fold (\<lambda>r ss. case r of TA_rule f qs q \<Rightarrow> List.insert q (fold (List.insert) qs ss)) rs ss"

lemma add_rule_states_Nil [simp]: "add_rule_states [] ss = ss" by (simp add: add_rule_states_def)

lemma add_rule_states_Cons [simp]: "add_rule_states (r # rs) =
  add_rule_states rs \<circ> List.insert (r_rhs r) \<circ> fold List.insert (r_lhs_states r)"
by (cases r) (auto simp: add_rule_states_def [abs_def])

lemma set_add_rule_states [simp]:
  "set (add_rule_states rs ss) = \<Union>(r_states ` set rs) \<union> set ss"
by (induct rs arbitrary: ss) (auto simp: r_states_def List.union_def [symmetric])

definition "check_growing R = check (growing (set R)) (showsl_lit (STR ''TRS is not growing''))"

lemma check_growing [simp]:
  "isOK (check_growing R) = growing (set R)"
by (simp add: check_growing_def)

type_synonym ('f, 'v) etac_ta = "(('f, 'v) term, 'f) tree_automaton"

(*needed due to later container setup (in Proof_Checker/Container_Setup)*)
definition "ta_inter_eps_empty T T' = \<lparr>
  ta_final = ta_final T \<times> ta_final T',
  ta_rules = (\<lambda>r. case r of (TA_rule f ps p, TA_rule g qs q) \<Rightarrow> (TA_rule f (zip ps qs) (p, q))) `
    (\<Union> ((\<lambda> f. {r \<in> ta_rules T. r_sym r = f} \<times> {r \<in> ta_rules T'. r_sym r = f}) ` ta_syms T)),
  ta_eps = {}
\<rparr>"

lemma ta_inter_eps_empty [simp]:
  "ta_eps A = {} \<Longrightarrow> ta_eps B = {} \<Longrightarrow> ta_inter_eps_empty A B = intersect_ta A B"
by (simp add: intersect_ta_def prod_ta_code ta_inter_eps_empty_def)

definition
  check_etac_nonreachable ::
    "('f \<times> nat) list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f, 'v) etac_ta \<Rightarrow>
      ('f::showl, 'v::showl) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_etac_nonreachable F' a c A' R' s t = do {
    let F = set F';
    check ((a, 0) \<in> F) (showsl_lit (STR ''constant '') \<circ> showsl a \<circ> showsl_lit (STR '' is not in signature''));
    check ((c, 0) \<notin> F) (showsl_lit (STR ''star-symbol is not fresh w.r.t. signature''));
    check_subseteq (funas_term_impl s) F' <+? (\<lambda>_. showsl_lit (STR ''lhs violates signature''));
    check_subseteq (funas_term_impl t) F' <+? (\<lambda>_. showsl_lit (STR ''rhs violates signature''));
    let fs = funas_trs_impl R';
    check_subseteq fs F' <+? (\<lambda>_. showsl_lit (STR ''TRS violates signature''));
    check_varcond_no_Var_lhs R';
    check_linear_trs R';
    check_growing R';
    let A = ta_of_ta A';
    check (ta_eps A = {}) (showsl_lit (STR ''no epsilon transitions allowed''));
    check (star c t \<in> ta_final A) (showsl_lit (STR ''final state for '') \<circ> showsl t \<circ> showsl_lit (STR '' is missing''));
    check (funas_ta A \<subseteq> F) (showsl_lit (STR ''the given automaton does not respect the signature''));
    let ts = (gi_rules_list F' c t);
    let ms = (mp_ta_rules R' F' c);
    check_rules_subseteq ts A';
    check_rules_subseteq ms A';
    let Q = add_rule_states ts (add_rule_states ms []); \<comment> \<open>states of internally constructed base TA\<close>
    let ss = state_substs (r_vars R') Q; \<comment> \<open>state substitutions\<close>
    let D = set (ta_rules_impl' A');
    let D' = inf_step c R' ss D;
    check (D' \<subseteq> D) (showsl_lit (STR ''the given tree automaton is not closed under completion rules''));
    check (ta_empty (ta_inter_eps_empty A (ground_instances_ta F c s)))
      (showsl_lit (STR ''the given tree automaton does not certify non-reachability''))
  }"

lemma check_etac_nonreachable:
  assumes ok: "isOK (check_etac_nonreachable F a c A R s t)"
  shows "\<not> (\<exists>(\<sigma>::('f::showl, 'v::showl) subst) \<tau>. (s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*)"
proof
  assume "\<exists>(\<sigma>::('f, 'v) subst) \<tau>. (s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*"
  then obtain \<sigma> \<tau> :: "('f, 'v) subst" where steps: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*" by blast
  let ?F = "set F"
  let ?A = "ta_of_ta A"
  let ?T = "ground_instances_ta ?F c t"
  let ?ts = "(gi_rules_list F c t)"
  let ?ms = "(mp_ta_rules R F c)"
  let ?Q = "add_rule_states ?ts (add_rule_states ?ms [])"
  have aux: "\<And>x A f B. x \<in> A \<Longrightarrow> f ` A \<subseteq> B \<Longrightarrow> f x \<in> B" by blast
  have a: "(a, 0) \<in> ?F" and "(c, 0) \<notin> ?F"
    "\<forall>(l, r) \<in> set R. is_Fun l"
    "\<forall>(l, r) \<in> set R. linear_term l \<and> linear_term r"
    and funas: "funas_trs (set R) \<subseteq> ?F" "funas_term s \<subseteq> ?F" "funas_term t \<subseteq> ?F"
    and "growing (set R)"
    and final: "star c t \<in> ta_final ?A"
    and [simp]: "ta_eps ?A = {}"
    and ts: "set ?ts \<subseteq> ta_rules ?A"
    and ms: "set ?ms \<subseteq> ta_rules ?A"
    and inf_step: "inf_step c R (state_substs (r_vars R) ?Q) (ta_rules ?A) \<subseteq> ta_rules ?A"
    and empty: "ta_empty (ta_inter_eps_empty ?A (ground_instances_ta ?F c s))"
    using ok
    by (auto simp: check_etac_nonreachable_def funas_defs linear_trs_def split: tree_automaton.splits)
  moreover then have "funas_ta ?T \<subseteq> ?F" by (simp add: funas_ta_ground_instances_ta)
  ultimately interpret gi_etac c ?F "set R" a ?T
    by (unfold_locales) (auto simp: accessible_ground_instances_ta)
  have subset: "ta_rules cr_ta \<subseteq> ta_rules (ta_of_ta A)"
    using ok
    apply (auto simp: check_etac_nonreachable_def cr_ta_def map_r_states_def split: tree_automaton.splits)
    by (force simp: ground_instances_ta_def)+
  have "set ?Q = ta_states cr_ta"
   by (simp add: cr_ta_def ta_states_ground_instances_ta [OF a, of c t])
      (auto simp: ta_states_def r_states_def map_r_states_def)
  from overapproximation_of_\<Delta>\<^sub>C [OF subset refl this inf_step]
    have rules: "\<Delta>\<^sub>C \<subseteq> ta_rules ?A" .
  have "\<forall>q\<in>ta_states (\<A>\<^sub>\<Sigma> t) \<inter> ta_states mp_ta. sterms TYPE('v) (\<A>\<^sub>\<Sigma> t) q = sterms TYPE('v) mp_ta q"
    using ta_states_intersection_reachable_from_same_terms [OF _ \<open>funas_term t \<subseteq> ?F\<close>] by auto
  have "lang ?A \<inter> lang (\<A>\<^sub>\<Sigma> s) = {}"
    using empty [simplified] and intersect_ta and ta_empty
    unfolding ta_lang_lang_eq by blast
  moreover have "lang C\<^sub>R \<subseteq> lang ?A"
  proof (rule ta_lang_mono [unfolded ta_lang_lang_eq])
    have "ta_rules C\<^sub>R \<subseteq> ta_rules ?A" using rules by (auto simp: C\<^sub>R_def)
    moreover have "ta_eps C\<^sub>R \<subseteq> ta_eps ?A" by (auto simp: C\<^sub>R_def cr_ta_def)
    moreover have "ta_final C\<^sub>R \<subseteq> ta_final ?A" using final by (auto simp: C\<^sub>R_def cr_ta_def)
    ultimately show "ta_subset C\<^sub>R ?A" by (auto simp: ta_subset_def)
  qed
  ultimately have "lang (\<A>\<^sub>\<Sigma> s) \<inter> lang C\<^sub>R = {}" by blast
  have "ground_instances (set F) t \<subseteq> lang (\<A>\<^sub>\<Sigma> t)"
    using ground_instances_subseteq_lang_ground_instances_ta [OF funas(3)] .
  have "\<not> (\<exists>\<sigma> \<tau>. fground ?F (s \<cdot> \<sigma>) \<and> fground ?F (t \<cdot> \<tau>) \<and> (s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*)"
    by (intro etac_nonreachable) fact+
  with fground_rsteps [OF \<open>(a, 0) \<in> ?F\<close> steps funas] show False by blast
qed

fun map_states_impl
where
  "map_states_impl f (Tree_Automaton qs ts eps) =
    Tree_Automaton (map f qs) (map (map_r_states f) ts) (map (\<lambda>(p, q). (f p, f q)) eps)"

end
