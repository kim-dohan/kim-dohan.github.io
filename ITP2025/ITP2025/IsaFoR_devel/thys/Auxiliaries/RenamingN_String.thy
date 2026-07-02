theory RenamingN_String 
  imports 
    RenamingN
    Show.Number_Parser
    First_Order_Terms.Lists_are_Infinite
begin

lemma underscore_not_show: "CHR ''_'' \<notin> set (show (n :: nat))"
  using set_show_nat[of n] unfolding digits_def by auto

lemma append_Cons_eq_iff':
  "x \<notin> set xs \<Longrightarrow> x \<notin> set xs' \<Longrightarrow>
   xs @ x # ys = xs' @ x # ys' \<longleftrightarrow> (xs = xs' \<and> ys = ys')"
  by (auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)

definition x_var_list :: "nat \<times> string \<Rightarrow> string"
  where "x_var_list ns \<equiv> case ns of (n, s) \<Rightarrow> CHR ''x'' # show n @ ''_'' @ s"

lemma inj_x_var_list: "inj x_var_list" 
  unfolding x_var_list_def inj_def 
proof (clarify, goal_cases)
  case (1 n1 x1 n2 x2)
  from 1 append_Cons_eq_iff'[OF underscore_not_show[of n1] underscore_not_show[of n2], of x1 x2]
  have n: "show n1 = show n2" and x: "x1 = x2" by auto
  with inj_show_nat have "n1 = n2" by (auto simp: inj_def)
  with x show ?case by auto
qed    

lift_definition string_renameN :: "string renamingN" is "(x_var_list, Cons (CHR ''y''))" 
  using inj_x_var_list
  by (auto simp: x_var_list_def)

end