(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Inline_Conditions_Impl
imports
  Conditional_Rewriting_Impl
  Inline_Conditions
begin


fun find_index
  where
    "find_index i x [] = error ()"
  | "find_index i x (y#ys) = (if x = y then return i else find_index (Suc i) x ys)"

lemma find_index_Inr:
  assumes "find_index i x ys = Inr j"
  shows "i \<le> j \<and> j - i < length ys \<and> ys ! (j - i) = x"
  using assms by (induct ys arbitrary: i j) (fastforce split: if_splits dest: Suc_leD)+

fun check_inline_conds_rule
  where
    "check_inline_conds_rule R \<rho> [] = return (R, \<rho>)"
  | "check_inline_conds_rule R \<rho> (c # cs) = do {
      let ((l, r), cs') = \<rho>;
      let (s, t) = c;
      check (is_Var t) (showsl_lit (STR ''condition with non-variable rhs''));
      let x = the_Var t;
      i \<leftarrow> find_index 0 c cs' <+? (\<lambda>(). showsl_lit (STR ''condition does not occur in rule''));
      check (x \<notin> vars_term s) (showsl_lit (STR ''occurs check failed''));
      check (x \<notin> vars_term l) (showsl_lit (STR ''inlining not allowed in lhs of rule''));
      check (x \<notin> \<Union>(vars_term ` rhss (set (take i cs'))) \<union> \<Union>(vars_term ` rhss (set (drop (Suc i) cs'))))
        (showsl_lit (STR ''inlining not allowed in rhss of conditions''));
      check_inline_conds_rule (inline i \<rho> # removeAll \<rho> R) (inline i \<rho>) (map (\<lambda>(u, v). (u \<cdot> subst x s, v)) cs)
    } <+? (\<lambda>e. showsl_lit (STR ''error while inlining condition '') \<circ> showsl_eq c \<circ> showsl_lit (STR '' of rule '') \<circ>
               showsl_crule \<rho> \<circ> showsl_nl \<circ> e)"

fun check_inline_conds_ctrs
  where
    "check_inline_conds_ctrs R [] = return R"
  | "check_inline_conds_ctrs R ((r, cs) # rcs) = do {
      check (r \<in> set R) (showsl_crule r \<circ> showsl_lit (STR '' does not occur in the input CTRS''));
      (R', r') \<leftarrow> check_inline_conds_rule R r cs;
      check_inline_conds_ctrs (r' # removeAll r' R') rcs
    } <+? (\<lambda>e. showsl_lit (STR ''error while inlining conditions\<newline>'') \<circ> e)"

lemma check_inline_conds_ctrs_Inr:
  assumes "check_inline_conds_ctrs R rcs = Inr R'"
  shows "(cstep (set R))\<^sup>* = (cstep (set R'))\<^sup>*"
  using assms
proof (induct "length rcs" arbitrary: rcs R R')
  case (Suc n rcs R R'')
  then obtain \<rho> cs rcs' where [simp]: "length rcs' = n" "rcs = (\<rho>, cs) # rcs'"
    by (cases rcs) auto
  from Suc.prems obtain R' and r'
    where check: "check_inline_conds_rule R \<rho> cs = Inr (R', r')"
      and "\<rho> \<in> set R"
      and "check_inline_conds_ctrs (r' # removeAll r' R') rcs' = Inr R''" by auto
  from Suc.hyps(1) [OF _ this(3)] have IH1: "(cstep (set (r' # removeAll r' R')))\<^sup>* = (cstep (set R''))\<^sup>*" by simp
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
    from Suc.prems obtain x where [simp]: "t = Var x" by auto
    from Suc.prems obtain i where find [simp]: "find_index 0 (s, Var x) cs' = Inr i" by auto
    from Suc.prems have vars: "x \<notin> vars_term (clhs \<rho>) \<union> vars_term s \<union>
      \<Union>(vars_term ` rhss (set (take i (conds \<rho>)))) \<union>
      \<Union>(vars_term ` rhss (set (drop (Suc i) (conds \<rho>))))" (is "x \<notin> ?V") by simp
    from Suc.prems
    have rec: "check_inline_conds_rule (inline i \<rho> # removeAll \<rho> R) (inline i \<rho>) (map (\<lambda>(u, v). (u \<cdot> subst x s, v)) ds) = Inr (R', r')"
      by auto
    have i: "i < length (conds \<rho>)" "conds \<rho> ! i = (s, Var x)"
      using find_index_Inr [OF find] by auto
    have ne: "\<rho> \<noteq> inline i \<rho>"
      using find_index_Inr [OF find]
      by (auto simp: inline_def Let_def list_eq_iff_zip_eq)
    have "n = length (map (\<lambda>(u, v). (u \<cdot> subst x s, v)) ds)"
      using Suc.hyps by simp
    from Suc.hyps(1) [OF this rec]
    have IH: "(cstep (set (inline i \<rho> # removeAll \<rho> R)))\<^sup>* = (cstep (set R''))\<^sup>*"
      by (simp add: Suc)
    then show ?case
      unfolding inline_cond [OF \<open>\<rho> \<in> set R\<close> i vars] by simp
  qed
qed simp

definition "check_inline_conds R R' rcs = do {
  R'' \<leftarrow> check_inline_conds_ctrs R rcs;
  check_same_set R' R'' <+? (\<lambda>_. showsl_lit (STR ''error while inlining:'') \<circ> 
    showsl_lit (STR ''\<newline>internally computed CTRS\<newline>'') \<circ> showsl_ctrs R'' \<circ> 
    showsl_lit (STR ''\<newline>but certificate contains CTRS\<newline>'') \<circ> showsl_ctrs R')
}"

lemma check_inline_conds [simp]:
  assumes "isOK (check_inline_conds R R' rcs)"
  shows "(cstep (set R))\<^sup>* = (cstep (set R'))\<^sup>*"
  using assms
  apply (cases "check_inline_conds R R' rcs"; cases "check_inline_conds_ctrs R rcs")
     apply (auto simp: check_inline_conds_def dest: check_inline_conds_ctrs_Inr)
  done

end
