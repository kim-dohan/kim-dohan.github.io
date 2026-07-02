theory IA_Instance
imports
  Ord.IA_Checker
  LTS_Termination_Prover
  LTS_Safety_Prover
begin

no_notation Simplex.curr_val_satisfies_state ("\<Turnstile>")

context IA_locale begin

fun constant_exp where
  "constant_exp (Bool True) = Fun LessF [const 0, const 1]"
| "constant_exp (Bool False) = Fun LessF [const 1, const 0]"
| "constant_exp (Int n) = const n"

sublocale algebra_constant I constant_exp
proof
  show "vars_term (constant_exp d) = {}" for d by (cases d rule: constant_exp.cases, auto)
  show "\<lbrakk>constant_exp d\<rbrakk> \<alpha> = d" for d \<alpha> by (cases d rule: constant_exp.cases, auto)
qed

fun is_constant where
  "is_constant (Fun _ []) = True"
| "is_constant _ = False"

lemma is_constant:
  assumes "is_constant e" shows "\<lbrakk>e\<rbrakk>\<alpha> = \<lbrakk>e\<rbrakk>\<beta>"
proof(cases e)
  case (Fun f es) with assms show ?thesis by (cases es, auto)
qed (insert assms, auto)

sublocale art_checker
  where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and tc = check_clause
    and tc2 = check_clause
    and sa = showsl_IA_exp
    and sa2 = showsl_IA_exp
    and ne = lit_normalize
    and ne2 = lit_normalize
    and ned = lit_normalized 
    and ned2 = lit_normalized ..

abbreviation "less_eq_formula s t \<equiv> Atom (Fun LeF [s,t])"
abbreviation "less_formula s t \<equiv> Atom (Fun LessF [s,t])"

lemma less_eq_meaning:
  assumes \<alpha>: "assignment \<alpha>"
      and s: "s :\<^sub>f IntT"
      and t: "t :\<^sub>f IntT"
  shows "\<alpha> \<Turnstile> less_eq_formula s t \<longleftrightarrow> \<lbrakk>s\<rbrakk> \<alpha> \<le> \<lbrakk>t\<rbrakk> \<alpha>"
  using eval_types[OF \<alpha> s] eval_types[OF \<alpha> t] s t
  by (cases "\<lbrakk>s\<rbrakk>\<alpha>"; cases "\<lbrakk>t\<rbrakk>\<alpha>", auto simp: is_bool_def)

lemma less_meaning:
  assumes \<alpha>: "assignment \<alpha>"
      and s: "s :\<^sub>f IntT"
      and t: "t :\<^sub>f IntT"
  shows "\<alpha> \<Turnstile> less_formula s t \<longleftrightarrow> \<lbrakk>s\<rbrakk> \<alpha> < \<lbrakk>t\<rbrakk> \<alpha>"
  using eval_types[OF \<alpha> s] eval_types[OF \<alpha> t] s t
  by (cases "\<lbrakk>s\<rbrakk>\<alpha>"; cases "\<lbrakk>t\<rbrakk>\<alpha>", auto simp: is_bool_def)

(* lemma transition_removal is an instance of transition_removal_bounded *)
interpretation transition_removal: transition_removal_bounded
  where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and showsl_atom = showsl_IA_exp
    and logic_checker = check_clause
    and normalize_lit = lit_normalize
    and normalized_lit = lit_normalized
    and dom_type = IntT
    and less_eq = "(\<le>) :: val \<Rightarrow> _ \<Rightarrow> _"
    and less = "(<)"
    and less_eq_formula = less_eq_formula
    and less_formula = less_formula
    and is_constant = is_constant
  by (unfold_locales; (fact less_eq_meaning less_meaning is_constant | simp add: All_less_Suc))


sublocale termination_checker: termination_checker
  where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and sa = showsl_IA_exp
    and tc = check_clause
    and ne = lit_normalize
    and ne2 = lit_normalize
    and sa2 = showsl_IA_exp
    and tc2 = check_clause
    and ned = lit_normalized 
    and ned2 = lit_normalized
    and dom_type = IntT
    and less_eq = "(\<le>) :: val \<Rightarrow> _ \<Rightarrow> _"
    and less = "(<)"
    and less_eq_formula = less_eq_formula
    and less_formula = less_formula
    and definability_checker = def_checker
    and is_constant = is_constant
    by unfold_locales

definition check_termination where "check_termination \<equiv> termination_checker.check"

lemma check_termination: "isOK (check_termination P prf) \<Longrightarrow> lts_termination (lts_of P)"
  by (unfold check_termination_def, fact termination_checker.sound)

end


thm IA.check_termination IA.check_safety

declare IA.constant_exp.simps[code]
  IA.check_termination_def[code]
  IA.check_safety_def[code]

end
