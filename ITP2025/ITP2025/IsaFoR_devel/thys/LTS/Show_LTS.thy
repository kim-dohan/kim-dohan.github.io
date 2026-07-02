theory Show_LTS
  imports 
    LTS 
    Cooperation_Program
begin

locale showsl_transition = showsl_formula showsl_atom + T: showsl_formula showsl_tatom
  for showsl_atom :: "('f,'v,'t) exp \<Rightarrow> showsl"
  and showsl_tatom :: "('f,'v trans_var,'t)exp \<Rightarrow> showsl"
begin
fun showsl_transition :: "('f,'v,'t,'l :: showl) transition_rule \<Rightarrow> showsl" where
  "showsl_transition (Transition s t \<phi>) = showsl s o showsl_lit (STR '' ---> '') o showsl t o showsl_lit (STR '': '') o T.showsl_formula \<phi>"

fun showsl_labeled_transition :: "('tr :: showl \<times> ('f,'v,'t,'l :: showl) transition_rule) \<Rightarrow> showsl" where
  "showsl_labeled_transition (lab, tran) = showsl lab o showsl_lit (STR '': '') o showsl_transition tran"

fun showsl_lts :: "('f,'v,'t,'l :: showl ,'tr :: showl)lts_impl \<Rightarrow> showsl" where
  "showsl_lts (Lts_Impl I tran lc) = showsl_lit (STR ''LTS:\<newline>Initial locations: '') o showsl_list I o showsl_lit (STR ''\<newline>Transitions\<newline>'')
     o showsl_sep showsl_labeled_transition showsl_nl tran o showsl_lit (STR ''\<newline>Location conditions'')
     o showsl_sep (\<lambda> (l,f). showsl l o showsl_lit (STR '': '') o showsl_formula f) showsl_nl lc o showsl_nl"

end

fun showsl_cooperation_program :: "('f,'v,'t,('l :: showl)sharp,'tr :: showl)lts_impl \<Rightarrow> showsl" where
  "showsl_cooperation_program (Lts_Impl I tran lc) = (let tran' = filter (\<lambda> (t,tt). is_sharp (target tt)) tran;
     tran'' = (case partition (\<lambda> (t,tt). is_sharp (source tt)) tran' of (ss, fs) \<Rightarrow> fs @ ss)
     in showsl_lit (STR ''Cooperation program (only sharp-part)\<newline>'') o
        showsl_sep 
          (\<lambda> (t,tt). showsl t o showsl_lit (STR '': '') o showsl (source tt) o showsl_lit (STR '' --> '') o showsl (target tt)) 
          showsl_nl 
          tran'') o showsl_nl"

declare showsl_transition.showsl_transition.simps[code]
declare showsl_transition.showsl_labeled_transition.simps[code]
declare showsl_transition.showsl_lts.simps[code]

end
