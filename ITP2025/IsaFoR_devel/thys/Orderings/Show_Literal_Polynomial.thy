theory Show_Literal_Polynomial
  imports Polynomials.Polynomials
    Show.Shows_Literal
begin

fun showsl_monom_list :: "('v :: {linorder,showl})monom_list \<Rightarrow> showsl" where 
  "showsl_monom_list [(x,p)] = (if p = 1 then showsl_lit (STR ''x'') o showsl x else showsl_lit (STR ''x'') o showsl x o showsl_lit (STR ''^'') o showsl p)"
| "showsl_monom_list ((x,p) # m) = ((if p = 1 then showsl_lit (STR ''x'') o showsl x else showsl_lit (STR ''x'') o showsl x o showsl (STR ''^'') o showsl p) 
     o showsl (STR ''*'') o showsl_monom_list m)"
| "showsl_monom_list [] = showsl (STR ''1'')"

instantiation monom :: ("{linorder,showl}") showl 
begin
lift_definition showsl_monom :: "'a monom \<Rightarrow> showsl" is showsl_monom_list .
definition "showsl_list (xs :: 'a monom list) = default_showsl_list showsl xs"
instance ..
end

fun showsl_poly :: "('v :: {showl,linorder},'a :: {one,showl})poly \<Rightarrow> showsl" where 
  "showsl_poly [] = showsl_lit (STR ''0'')"
| "showsl_poly ((m,c) # p) = ((if c = 1 then showsl m else if m = 1 then showsl c else showsl c o 
     showsl_lit (STR ''*'') o showsl m) o (if p = [] then id else showsl_lit (STR '' + '') o showsl_poly p))"
end
