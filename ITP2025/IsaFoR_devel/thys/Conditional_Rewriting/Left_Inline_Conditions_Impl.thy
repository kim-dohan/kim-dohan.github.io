(*
Author:  Florian Meßner <florian.messner@outlook.com> (2020)
License: LGPL (see file COPYING.LESSER)
*)
theory Left_Inline_Conditions_Impl
  imports
    Left_Inline_Conditions
    Inline_Conditions_Impl
begin

(* This file is an adjusted copy of Inline_Conditions_Impl.thy *)

fun check_left_inline_conds_rule
  where
    "check_left_inline_conds_rule R \<rho> [] = return (R, \<rho>)"
  | "check_left_inline_conds_rule R \<rho> (c # cs) = do {
      let ((l, r), cs') = \<rho>;
      check (linear_term l) (showsl_lit (STR ''non-linear lhs in rule''));
      let (s, t) = c;
      check (is_Var s) (showsl_lit (STR ''condition with non-variable lhs''));
      let x = the_Var s;
      i \<leftarrow> find_index 0 c cs' <+? (\<lambda>(). showsl_lit (STR ''condition does not occur in rule''));
      check (x \<notin> vars_term t) (showsl_lit (STR ''occurs check failed''));
      check (x \<notin> vars_term r) (showsl_lit (STR ''left-inlining not allowed in rhs of rule''));
      check (x \<notin> \<Union>(vars_term ` lhss (set (take i cs'))) \<union> \<Union>(vars_term ` lhss (set (drop (Suc i) cs'))))
        (showsl_lit (STR ''left-inlining not allowed in lhss of conditions''));
      check_left_inline_conds_rule (left_inline i \<rho> # removeAll \<rho> R) (left_inline i \<rho>) (map (\<lambda>(u, v). (u, v \<cdot> subst x t)) cs)
    } <+? (\<lambda>e. showsl_lit (STR ''error while left-inlining condition '') \<circ> showsl_eq c \<circ> showsl_lit (STR '' of rule '') \<circ>
               showsl_crule \<rho> \<circ> showsl_nl \<circ> e)"

fun check_left_inline_conds_ctrs
  where
    "check_left_inline_conds_ctrs R [] = return R"
  | "check_left_inline_conds_ctrs R ((r, cs) # rcs) = do {
      check (r \<in> set R) (showsl_crule r \<circ> showsl_lit (STR '' does not occur in the input CTRS''));
      (R', r') \<leftarrow> check_left_inline_conds_rule R r cs;
      check_left_inline_conds_ctrs (r' # removeAll r' R') rcs
    } <+? (\<lambda>e. showsl_lit (STR ''error while left-inlining conditions\<newline>'') \<circ> e)"

lemma check_left_inline_conds_ctrs_Inr:
  assumes "check_left_inline_conds_ctrs R rcs = Inr R'"
  shows "(cstep (set R))\<^sup>* \<subseteq> (cstep (set R'))\<^sup>*"
  using assms
proof (induct "length rcs" arbitrary: rcs R R')
  case (Suc n rcs R R'')
  then obtain \<rho> cs rcs' where [simp]: "length rcs' = n" "rcs = (\<rho>, cs) # rcs'"
    by (cases rcs) auto
  from Suc.prems obtain R' and r'
    where check: "check_left_inline_conds_rule R \<rho> cs = Inr (R', r')"
      and "\<rho> \<in> set R"
      and "check_left_inline_conds_ctrs (r' # removeAll r' R') rcs' = Inr R''" by auto
  from Suc.hyps(1) [OF _ this(3)] have IH1: "(cstep (set (r' # removeAll r' R')))\<^sup>* \<subseteq> (cstep (set R''))\<^sup>*" by simp
  from check and \<open>\<rho> \<in> set R\<close>
  show ?case
  proof (induct "length cs" arbitrary: cs \<rho> R)
    case 0
    then show ?case using IH1 by (simp add: insert_absorb)
  next
    case (Suc n)
    then obtain c and ds where [simp]: "cs = c # ds" by (cases cs) auto
    obtain l r cs' where [simp]: "\<rho> = ((l, r), cs')" by (cases \<rho> rule: crule_cases) auto
    obtain s t where [simp]: "c = (s, t)" by (cases c) auto
    from Suc.prems obtain x where [simp]: "s = Var x" by auto
    from Suc.prems obtain i where find [simp]: "find_index 0 (Var x, t) cs' = Inr i" by auto
    from Suc.prems have vars: "x \<notin> vars_term (crhs \<rho>) \<union> vars_term t \<union>
      \<Union>(vars_term ` lhss (set (take i (conds \<rho>)))) \<union>
      \<Union>(vars_term ` lhss (set (drop (Suc i) (conds \<rho>))))" (is "x \<notin> ?V") by simp
    from Suc.prems have lin: "linear_term l" by simp
    from Suc.prems
    have rec: "check_left_inline_conds_rule (left_inline i \<rho> # removeAll \<rho> R) (left_inline i \<rho>) (map (\<lambda>(u, v). (u, v \<cdot> subst x t)) ds) = Inr (R', r')"
      by auto
    have i: "i < length (conds \<rho>)" "conds \<rho> ! i = (Var x, t)"
      using find_index_Inr [OF find] by auto
    have ne: "\<rho> \<noteq> left_inline i \<rho>"
      using find_index_Inr [OF find]
      by (auto simp: left_inline_def Let_def list_eq_iff_zip_eq)
    have "n = length (map (\<lambda>(u, v). (u, v \<cdot> subst x t)) ds)"
      using Suc.hyps by simp
    from Suc.hyps(1) [OF this rec]
    have IH: "(cstep (set (left_inline i \<rho> # removeAll \<rho> R)))\<^sup>* \<subseteq> (cstep (set R''))\<^sup>*"
      by (simp add: Suc)
    then show ?case
      using left_inline_cond' [OF \<open>\<rho> \<in> set R\<close> i _ vars] lin by auto
  qed
qed simp

definition "check_left_inline_conds R R' rcs = do {
  R'' \<leftarrow> check_left_inline_conds_ctrs R rcs;
  check_same_set R' R'' <+? (\<lambda>_. showsl_lit (STR ''error while left-inlining:'') \<circ>
    showsl_lit (STR ''\<newline>internally computed CTRS\<newline>'') \<circ> showsl_ctrs R'' \<circ>
    showsl_lit (STR ''\<newline>but certificate contains CTRS\<newline>'') \<circ> showsl_ctrs R')
}"

lemma check_left_inline_conds [simp]:
  assumes "isOK (check_left_inline_conds R R' rcs)"
  shows "(cstep (set R))\<^sup>* \<subseteq> (cstep (set R'))\<^sup>*"
  using assms
  apply (cases "check_left_inline_conds R R' rcs"; cases "check_left_inline_conds_ctrs R rcs")
     apply (auto simp: check_left_inline_conds_def dest: check_left_inline_conds_ctrs_Inr)
  done

end
