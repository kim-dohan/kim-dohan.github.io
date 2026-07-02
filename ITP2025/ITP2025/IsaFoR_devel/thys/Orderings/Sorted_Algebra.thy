(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Sorted_Algebra
imports 
  F_Algebra
begin

type_synonym ('f,'v,'t) exp = "('f,'v \<times>'t) term"

consts rename_vars :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd"

definition rename_vars_exp :: "('v \<Rightarrow> 'w) \<Rightarrow> ('f,'v,'t) exp \<Rightarrow> ('f,'w,'t) exp" where
  "rename_vars_exp r = map_term id (map_prod r id)"

adhoc_overloading rename_vars \<rightleftharpoons> rename_vars_exp

lemma rename_vars_exp_simps[simp]:
  "rename_vars_exp r (Var (x,ty)) = Var (r x, ty)"
  "rename_vars_exp r (Fun f ts) = Fun f (map (rename_vars_exp r) ts)"
  by (auto simp: rename_vars_exp_def)

lemma rename_vars_exp_comp[simp]:
  "rename_vars f (rename_vars g (t::(_,_,_) exp)) = rename_vars (f \<circ> g) t"
   by (induct t, auto)

lemma vars_term_rename_vars[simp]: "vars_term (rename_vars f t) = map_prod f id ` vars_term t" by (induct t, auto)

lemma rename_vars_exp_id[THEN ext, simp]: "rename_vars id (t :: ('f,'v,'t) exp) = t"
proof (induct t)
  case (Var x)
  then show ?case by (cases x, auto)
next
  case (Fun f ts)
  then show ?case by (auto intro: map_idI)
qed


locale pre_sorted_algebra = algebra I
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  and type_of_fun :: "'f \<Rightarrow> 't list \<times> 't"
  and Values_of_type :: "'t \<Rightarrow> 'a set"
  and type_fixer :: "('f\<times>'t\<times>'a) itself" (* Is this a good solution? *)
begin

abbreviation type_of_var :: "'v \<times> 't \<Rightarrow> 't" where "type_of_var \<equiv> snd"

definition "assignment \<alpha> \<equiv> \<forall>x. \<alpha> x \<in> Values_of_type (type_of_var x)"

abbreviation return_type where "return_type f \<equiv> snd (type_of_fun f)"
abbreviation param_types where "param_types f \<equiv> fst (type_of_fun f)"

lemma assignmentI[intro]:
  assumes "\<And>x t. \<alpha> (x,t) \<in> Values_of_type t" shows "assignment \<alpha>"
  using assms by (auto simp: assignment_def)

lemma assignmentD[dest]:
  assumes "assignment \<alpha>" shows "\<And>x. \<alpha> x \<in> Values_of_type (type_of_var x)" using assms by (auto simp: assignment_def)

lemma assignmentE[elim]:
  assumes "assignment \<alpha>" and "(\<And>x. \<alpha> x \<in> Values_of_type (type_of_var x)) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: assignment_def)

fun has_type (infix ":\<^sub>f" 60) where
  "Var v :\<^sub>f ty \<longleftrightarrow> type_of_var v = ty"
| "Fun f es :\<^sub>f ty \<longleftrightarrow>
  (ty = return_type f \<and> length es = length (param_types f) \<and> (\<forall>i < length es. es ! i :\<^sub>f param_types f ! i))"

notation has_type (infix ":\<^sub>f" 60)

abbreviation "expression e \<equiv> \<exists>ty. e :\<^sub>f ty"

lemma map_term_has_type:
  assumes "\<And>x. x \<in> vars_term e \<Longrightarrow> type_of_var (r x) = type_of_var x"
      and "\<And>f. f \<in> funs_term e \<Longrightarrow> type_of_fun (rf f) = type_of_fun f"
  shows "map_term rf r e :\<^sub>f ty \<longleftrightarrow> e :\<^sub>f ty"
proof-
  { fix X F
    assume X: "\<And>x. x \<in> X \<Longrightarrow> type_of_var (r x) = type_of_var x"
       and F: "\<And>f. f \<in> F \<Longrightarrow> type_of_fun (rf f) = type_of_fun f"
    have "vars_term e \<subseteq> X \<Longrightarrow> funs_term e \<subseteq> F \<Longrightarrow> ?thesis"
    proof (induct e arbitrary: ty)
      case (Var x)
      then show ?case using X by auto
    next
      case (Fun f es)
      show ?case
      proof (cases "type_of_fun f")
        case (Pair tys ty')
        moreover {
          fix i assume i: "i < length es" "length es = length tys"
          from Fun X F have "e \<in> set es \<Longrightarrow> vars_term e \<subseteq> X \<and> funs_term e \<subseteq> F" for e by auto
          with i have "vars_term (es!i) \<subseteq> X" "funs_term (es!i) \<subseteq> F" by auto
          with Fun(1)[OF _ this, of "tys!i"] i Pair Fun
          have "map_term rf r (es ! i) :\<^sub>f tys ! i = es ! i :\<^sub>f tys ! i" by auto
        }
        moreover from Fun F have "type_of_fun (rf f) = type_of_fun f" by auto
        ultimately show ?thesis by auto
      qed
    qed
  }
  from this[OF assms] show ?thesis by auto
qed

lemma rename_vars_has_type[simp]: "rename_vars r e :\<^sub>f ty \<longleftrightarrow> e :\<^sub>f ty"
  by (unfold rename_vars_exp_def, intro map_term_has_type, auto)

context
  fixes \<alpha> :: "'v \<times> 't \<Rightarrow> 'a" and \<beta> :: "'w \<times> 't \<Rightarrow> 'a" and r :: "'v \<Rightarrow> 'w"
  assumes r: "\<And> x t. \<alpha> (x,t) = \<beta> (r x, t)"
begin

lemma eval_rename_vars: "\<lbrakk>rename_vars r a\<rbrakk> \<beta> = \<lbrakk>a\<rbrakk> \<alpha>"
proof (induct a)
  case (Var x)
  show ?case by (cases x, auto simp: rename_vars_exp_def r)
next
  case (Fun f ts)
  then show ?case by (auto intro: arg_cong[of _ _ "I f"])
qed

lemma assignment_rename_vars: "assignment \<beta> \<Longrightarrow> assignment \<alpha>"
  unfolding assignment_def using r by auto

end

end

locale sorted_algebra = pre_sorted_algebra + 
  assumes well_typed:
    "\<And>f ds. length ds = length (param_types f) \<Longrightarrow>
     (\<And>i. i < length ds \<Longrightarrow> ds!i \<in> Values_of_type (param_types f ! i)) \<Longrightarrow> I f ds \<in> Values_of_type (return_type f)"
  and consistent: "\<And>ty. Values_of_type ty \<noteq> {}"
begin

lemma eval_types:
  assumes "assignment \<alpha>" and "x :\<^sub>f ty" shows "\<lbrakk>x\<rbrakk> \<alpha> \<in> Values_of_type ty"
  using assms by (induct x arbitrary: ty, insert well_typed, auto)

end

end
