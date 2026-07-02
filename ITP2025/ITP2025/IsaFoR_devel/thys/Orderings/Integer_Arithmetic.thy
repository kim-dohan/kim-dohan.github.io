(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Integer_Arithmetic
imports
  Formula
  Deriving.Compare_Generator
  Certification_Monads.Check_Monad
  Non_Inf_Orders
  Show_Literal_Polynomial
begin

locale IA_locale
begin

datatype ty = BoolT | IntT

datatype sig = LessF | LeF | SumF nat | ConstF (the_ConstF: int) | ProdF nat | EqF

datatype "val" = Int (to_int: int) | Bool (to_bool: bool)

type_synonym 'v exp = "(sig,'v,ty) Sorted_Algebra.exp"

type_synonym 'v formula = "'v exp Formula.formula"

no_notation inter (infixl "Int" 70)

abbreviation "var x \<equiv> Var (x,IntT)"
abbreviation le_t where "le_t s t \<equiv> Atom (Fun LeF [s,t])"
abbreviation less_t where "less_t s t \<equiv> Atom (Fun LessF [s,t])"
abbreviation eq_t where "eq_t s t \<equiv> Atom (Fun EqF [s,t])"

fun type_of_fun :: "sig \<Rightarrow> ty list \<times> ty" where
  "type_of_fun LessF = ([IntT,IntT], BoolT)"
| "type_of_fun LeF = ([IntT,IntT], BoolT)"
| "type_of_fun EqF = ([IntT,IntT], BoolT)"
| "type_of_fun (SumF n) = (replicate n IntT, IntT)"
| "type_of_fun (ConstF _) = ([], IntT)"
| "type_of_fun (ProdF n) = (replicate n IntT, IntT)" 

fun Values_of_type :: "ty \<Rightarrow> val set" where
  "Values_of_type BoolT = range Bool"
| "Values_of_type IntT = range Int"

lemma mem_Values_of_typeE[elim]:
  assumes "v \<in> Values_of_type ty"
      and "\<And>i. ty = IntT \<Longrightarrow> v = Int i \<Longrightarrow> thesis"
      and "\<And>b. ty = BoolT \<Longrightarrow> v = Bool b \<Longrightarrow> thesis"
  shows "thesis" using assms by (cases ty, auto)

lemma mem_Values_of_typeD[dest]:
  assumes "v \<in> Values_of_type ty"
  shows "(ty = IntT \<longrightarrow> (\<exists>i. v = Int i)) \<and> (ty = BoolT \<longrightarrow> (\<exists>b. v = Bool b))"
  by (insert assms, auto)

fun "I" :: "sig \<Rightarrow> val list \<Rightarrow> val" where
  "I LessF [x, y] = Bool (to_int x < to_int y)"
| "I LeF [x, y] = Bool (to_int x \<le> to_int y)"
| "I EqF [x, y] = Bool (to_int x = to_int y)"
| "I (SumF n) xs = Int (sum_list (map to_int xs))"
| "I (ConstF x) [] = Int x"
| "I (ProdF n) xs = Int (prod_list (map to_int xs))"
| "I _ _ = undefined"

sublocale prelogic
  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and type_fixer= "TYPE(_)".

abbreviation const where "const x \<equiv> Fun (ConstF x) []"

end

(* don't do this before "sublocale prelogic"; otherwise you lose term IA.eval *)
global_interpretation IA: IA_locale.

notation IA.le_t (infix "\<le>\<^sub>I\<^sub>A" 50)
notation IA.less_t (infix "<\<^sub>I\<^sub>A" 50)
notation IA.eq_t (infix "=\<^sub>I\<^sub>A" 50)
notation IA.valid ("\<Turnstile>\<^sub>I\<^sub>A _" [40]40)


instantiation IA.sig :: showl
begin
fun showsl_sig where 
  "showsl_sig IA.LessF = showsl_lit (STR ''<'')" 
| "showsl_sig IA.LeF = showsl_lit (STR ''<='')" 
| "showsl_sig IA.EqF = showsl_lit (STR ''='')" 
| "showsl_sig (IA.SumF n) = showsl_lit (STR ''+'')" 
| "showsl_sig (IA.ProdF n) = showsl_lit (STR ''*'')" 
| "showsl_sig (IA.ConstF n) = showsl n" 
definition "showsl_list (xs :: IA.sig list) = default_showsl_list showsl xs"
instance ..
end

instantiation IA.ty :: showl
begin
fun showsl_ty where 
  "showsl_ty IA.BoolT = showsl_lit (STR ''Bool'')" 
| "showsl_ty IA.IntT = showsl_lit (STR ''Int'')" 
definition "showsl_list (xs :: IA.ty list) = default_showsl_list showsl xs"
instance ..
end
derive compare_order IA.val

context IA_locale
begin

lemma has_type_induct[consumes 1, case_names Less Lesseq Equals Sum Const Prod Var]:
  assumes "e :\<^sub>f ty"
  and LessCase: "\<And> ta tb.
       ta :\<^sub>f IntT \<Longrightarrow> tb :\<^sub>f IntT \<Longrightarrow> P ta IntT \<Longrightarrow> P tb IntT \<Longrightarrow> P (Fun IA.LessF [ta,tb]) BoolT"
  and LesseqCase: "\<And> ta tb.
       ta :\<^sub>f IntT \<Longrightarrow> tb :\<^sub>f IntT \<Longrightarrow> P ta IntT \<Longrightarrow> P tb IntT \<Longrightarrow> P (Fun IA.LeF [ta,tb]) BoolT"
  and EqualsCase: "\<And> ta tb.
       ta :\<^sub>f IntT \<Longrightarrow> tb :\<^sub>f IntT \<Longrightarrow> P ta IntT \<Longrightarrow> P tb IntT \<Longrightarrow> P (Fun IA.EqF [ta,tb]) BoolT"
  and SumCase: "\<And> ts n.
       (\<And> t. t \<in> set ts \<Longrightarrow> t :\<^sub>f IntT) \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> P t IntT) \<Longrightarrow> P (Fun (SumF n) ts) IntT"
  and ConstCase: "\<And> x. P (const x) IntT"
  and ProdCase: "\<And> ts n. 
       (\<And> t. t \<in> set ts \<Longrightarrow> t :\<^sub>f IntT) \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> P t IntT) \<Longrightarrow> P (Fun (ProdF n) ts) IntT"
  and VarCase: "\<And> x ty. P (Var (x,ty)) ty"
  shows "P e ty"
using assms(1) proof(induct e ty rule: has_type.induct)
  case (1 x ty) with VarCase show ?case by(cases x, auto)
next
  case Fun: (2 f ls ty)
  show ?case
  proof(cases f)
    case [simp]: LessF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f IntT" and bt: "tb :\<^sub>f IntT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] LessCase show ?thesis by auto
  next
    case [simp]: LeF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f IntT" and bt: "tb :\<^sub>f IntT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] LesseqCase show ?thesis by auto
  next
    case [simp]: EqF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f IntT" and bt: "tb :\<^sub>f IntT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] EqualsCase show ?thesis by auto
  next
    case [simp]: (SumF n)
    {
      fix l
      assume "l \<in> set ls" 
      then obtain i where l: "l = ls ! i" and i: "i < length ls" unfolding set_conv_nth by auto
      from Fun(2) l i have lty: "l :\<^sub>f IntT" by auto
      from Fun.hyps[OF i] lty i l Fun(2) have "P l IntT" by auto
      note lty this
    }
    from SumCase[OF this, of ls n] Fun(2) show ?thesis by auto
  next
    case [simp]: (ConstF x)
    with Fun have [simp]: "ls = []" by auto
    show ?thesis using Fun ConstCase by simp
  next
    case [simp]: (ProdF n)
    {
      fix l
      assume "l \<in> set ls" 
      then obtain i where l: "l = ls ! i" and i: "i < length ls" unfolding set_conv_nth by auto
      from Fun(2) l i have lty: "l :\<^sub>f IntT" by auto
      from Fun.hyps[OF i] lty i l Fun(2) have "P l IntT" by auto
      note lty this
    }
    from ProdCase[OF this, of ls n] Fun(2) show ?thesis by auto
  qed
qed

sublocale logic
  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and type_fixer = "TYPE(_)"
proof
  fix f ds
  show "length ds = length (param_types f) \<Longrightarrow>
       (\<And>i. i < length ds \<Longrightarrow> ds ! i \<in> Values_of_type (param_types f ! i)) \<Longrightarrow>
       I f ds \<in> Values_of_type (return_type f)"
  by (cases f; induct f ds rule: IA.I.induct, auto)
  show "Values_of_type ty \<noteq> {}" for ty by(cases ty, auto)
qed

lemmas [simp] = less_val_def compare_val_def lt_of_comp_def comparator_of_def

lemma less_IA_value_simps[simp]:
 "\<And>x y. Bool x > Bool y \<longleftrightarrow> x > y"
 "\<And>x y. Bool x > Int y"
 "\<And>x y. Int x > Int y \<longleftrightarrow> x > y"
 "\<And>x y. Int x > Bool y \<longleftrightarrow> False"
proof-
  show "Bool x > Bool y \<longleftrightarrow> x > y" for x y by (cases x; cases y, auto)
qed auto

lemmas [simp del] = less_val_def compare_val_def lt_of_comp_def comparator_of_def

lemma val_le[simp]: "(x :: val) \<ge> y \<longleftrightarrow> x = y \<or> x > y" by auto

lemma to_int_iff:
  assumes \<alpha>: "assignment \<alpha>" and s: "s :\<^sub>f IntT" and t: "t :\<^sub>f IntT"
  shows "to_int (\<lbrakk>s\<rbrakk>\<alpha>) < to_int (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> < \<lbrakk>t\<rbrakk>\<alpha>"
    and "to_int (\<lbrakk>s\<rbrakk>\<alpha>) \<le> to_int (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> \<le> \<lbrakk>t\<rbrakk>\<alpha>"
    and "to_int (\<lbrakk>s\<rbrakk>\<alpha>) = to_int (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> = \<lbrakk>t\<rbrakk>\<alpha>"
  using s t by (auto dest!: eval_types[OF \<alpha>])

end

instance "IA.val" :: non_inf_quasi_order
proof(intro_classes)
  fix f :: "nat \<Rightarrow> IA.val" and a
  assume "\<forall>i. f (Suc i) < f i"
  note chain = this[rule_format]
  have f0: "\<not> IA.Bool True < f 0" by (cases "f 0", auto)
  from chain[of 0] have f1: "\<not> IA.Bool False < f 1" by (cases "f 0"; cases "f 1", auto)
  have "\<exists>x. f (Suc (Suc n)) = IA.Int x" for n
  proof(induct n)
    case 0
    from f1 chain[of 1] have "f (Suc (Suc 0)) < IA.Bool False" by auto
    then show ?case by (cases "f (Suc (Suc 0))", auto)
  next
    case (Suc n)
    then obtain x where IH: "f (Suc (Suc n)) = IA.Int x" by auto
    with chain[of "Suc (Suc n)"] show ?case by (cases "f (Suc (Suc (Suc n)))", auto)
  qed
  from choice[OF allI[OF this]] obtain g where g: "\<And>i. f (Suc (Suc i)) = IA.Int (g i)" by force
  then have chaing: "g (Suc i) < g i" for i using chain[of "Suc (Suc i)"] by auto
  with non_inf_int_gt[unfolded non_inf_def]
  have "\<And>n. \<exists>i. \<not> n < g i" by blast
  with g have "\<exists>i. \<not> IA.Int n < f (Suc (Suc i))" for n by auto
  then have *: "\<exists>i. \<not> IA.Int n < f i" for n by auto
  show "\<exists>i. \<not> a < f i"
  proof(cases a)
    case a: (Bool b) with f0 f1 show ?thesis by (cases b, auto)
  next
    case a: (Int i) with * show ?thesis by auto
  qed
qed

subsection \<open>Non-term, polynomial version\<close>

type_synonym 'v ipoly = "('v,int)poly" 

context
  notes [[typedef_overloaded]]
begin
datatype 'v poly_constraint = 
  Poly_Ge "'v ipoly" (* meaning: p \<ge> 0 *)
| Poly_Eq "'v ipoly" (* meaning: p = 0 *) 
end

context IA_locale begin

fun showsl_poly_constraint :: "'v :: {showl,linorder} poly_constraint \<Rightarrow> showsl" where 
  "showsl_poly_constraint (Poly_Ge p) = (showsl_poly p o showsl_lit (STR '' >= 0''))"
| "showsl_poly_constraint (Poly_Eq p) = (showsl_poly p o showsl_lit (STR '' = 0''))"

fun interpret_poly_constraint :: "('v :: linorder \<Rightarrow> int) \<Rightarrow> 'v poly_constraint \<Rightarrow> bool" where
  "interpret_poly_constraint f (Poly_Ge p) = (eval_poly f p \<ge> 0)" 
| "interpret_poly_constraint f (Poly_Eq p) = (eval_poly f p = 0)" 
  
fun vars_poly_constraint :: "'v :: linorder poly_constraint \<Rightarrow> 'v set" where
  "vars_poly_constraint (Poly_Ge p) = poly_vars p"
| "vars_poly_constraint (Poly_Eq p) = poly_vars p"

fun vars_poly_constraint_list :: "'v :: linorder poly_constraint \<Rightarrow> 'v list" where
  "vars_poly_constraint_list (Poly_Ge p) = poly_vars_list p"
| "vars_poly_constraint_list (Poly_Eq p) = poly_vars_list p"
  
lemma vars_poly_constraint_list[simp]: "set (vars_poly_constraint_list c) = vars_poly_constraint c" 
  by (cases c, auto)

fun IA_exp_to_tpoly :: "'v IA.exp \<Rightarrow> ('v,int) tpoly" where
 "IA_exp_to_tpoly (Var (a,ty)) = PVar a" |
 "IA_exp_to_tpoly (Fun (SumF _) as) = PSum (map IA_exp_to_tpoly as)" |
 "IA_exp_to_tpoly (Fun (ConstF a) []) = PNum a" |
 "IA_exp_to_tpoly (Fun (ProdF _) as) = PMult (map IA_exp_to_tpoly as)"
    
definition IA_exp_to_poly :: "'v :: linorder IA.exp \<Rightarrow> ('v,int) poly" where
  "IA_exp_to_poly = poly_of o IA_exp_to_tpoly" 

fun IA_exp_to_poly_constraint :: "'v :: linorder IA.exp \<Rightarrow> 'v poly_constraint" where
  "IA_exp_to_poly_constraint (Fun LeF [a, b]) = Poly_Ge (poly_minus (IA_exp_to_poly b) (IA_exp_to_poly a))" 
| "IA_exp_to_poly_constraint (Fun EqF [a, b]) = Poly_Eq (poly_minus (IA_exp_to_poly b) (IA_exp_to_poly a))" 
| "IA_exp_to_poly_constraint (Fun LessF [a, b]) = Poly_Ge (poly_minus (poly_minus (IA_exp_to_poly b) (IA_exp_to_poly a)) one_poly)" 

lemma IA_exp_to_tpoly:
  assumes \<alpha>: "assignment \<alpha>"
  and "e :\<^sub>f IntT"
  shows "\<lbrakk>e\<rbrakk>\<alpha> = Int (eval_tpoly (\<lambda>a. to_int (\<alpha> (a, IntT))) (IA_exp_to_tpoly e))"
proof -
  have "e :\<^sub>f IntT \<Longrightarrow> ?thesis" 
  proof(induct e IntT rule:has_type_induct)
    case (Var x)
    from \<alpha> obtain i where "\<alpha> (x, IntT) = Int i" by force
    then show ?case by auto
  next
    case (Sum es n)
    then show ?case by (auto, induct es, auto)
  next
    case (Prod es n)
    then show ?case by (auto, induct es, auto)
  qed auto
  then show ?thesis using assms by simp
qed
  
lemma IA_exp_to_poly:
  assumes \<alpha>: "assignment \<alpha>"
  and "e :\<^sub>f IntT"
shows "\<lbrakk>e\<rbrakk>\<alpha> = Int (eval_poly (\<lambda>a. to_int (\<alpha> (a, IntT))) (IA_exp_to_poly e))"
  using IA_exp_to_tpoly[OF assms] unfolding IA_exp_to_poly_def o_def poly_of .
  
lemma IA_exp_to_poly_constraint: 
  assumes \<alpha>: "assignment \<alpha>"
  and e: "is_bool e" "is_Fun e" 
  shows "to_bool (\<lbrakk>e\<rbrakk>\<alpha>) = (interpret_poly_constraint (\<lambda>a. to_int (\<alpha> (a, IntT))) (IA_exp_to_poly_constraint e))"
proof -
  have "e :\<^sub>f BoolT \<Longrightarrow> is_Fun e \<Longrightarrow> ?thesis"
    by (induct e BoolT rule: has_type_induct, insert IA_exp_to_poly[OF \<alpha>], auto)
  then show ?thesis using e[unfolded is_bool_def] by auto
qed

fun showsl_IA_exp where
  "showsl_IA_exp (Fun LessF [s,t]) = showsl_IA_exp s o showsl_lit (STR '' < '') o showsl_IA_exp t"
| "showsl_IA_exp (Fun LeF [s,t]) = showsl_IA_exp s o showsl_lit (STR '' <= '') o showsl_IA_exp t"
| "showsl_IA_exp (Fun EqF [s,t]) = showsl_IA_exp s o showsl_lit (STR '' = '') o showsl_IA_exp t"
| "showsl_IA_exp e = showsl_poly (IA_exp_to_poly e)"

definition "showsl_IA_clause = showsl_list_gen showsl_IA_exp (STR ''FALSE'') (STR '''') (STR '' || '') (STR '''')" 

definition "showsl_IA_formula = showsl_list_gen (showsl_paren o showsl_IA_clause) (STR ''TRUE'') (STR '''') (STR '' && '') (STR '''')" 

definition def_checker_main where
  "def_checker_main x ty l1 r1 l2 r2 = (is_bool (Fun LeF [l1, r1]) \<and>
    r1 :\<^sub>f ty \<and> is_bool (Fun LeF [l2,r2]) \<and> Var (x,ty) = l1 \<and> l1 = r2 \<and> l2 = r1 \<and> (x,ty) \<notin> vars_term r1)" 

definition def_checker_main' where
  "def_checker_main' x ty l1 r1 = (is_bool (Fun EqF [l1,r1]) \<and>
    r1 :\<^sub>f ty \<and> Var (x,ty) = l1 \<and> (x,ty) \<notin> vars_term r1)" 

definition def_checker_eq where "def_checker_eq x ty eq =
  (case eq of Atom e1 \<Rightarrow> (case e1 of Fun EqF [l1,r1] \<Rightarrow> 
              check (def_checker_main' x ty l1 r1 \<or> def_checker_main' x ty r1 l1)
              (showsl_lit (STR ''Non-equation not supported'')) | _ \<Rightarrow> error (showsl_lit (STR ''Invalid literal'')))
            | _ \<Rightarrow> error (showsl_lit (STR ''Invalid clause'')))" 

definition def_checker :: "(sig, 'v :: {showl, linorder}, ty) definability_checker"
(* unfortunately, a nice pattern matching doesn't go well for proving... *)
where "def_checker x ty \<phi> \<equiv>
 (case \<phi> of Conjunction \<phi>s \<Rightarrow>
   (case \<phi>s of [] \<Rightarrow> succeed
    | [eq] \<Rightarrow> def_checker_eq x ty eq
    | [lt1, lt2] \<Rightarrow>
     (case lt1 of Atom e1 \<Rightarrow>
       (case e1 of Fun IA.LeF [l1,r1] \<Rightarrow>
         (case lt2 of Atom e2 \<Rightarrow>
           (case e2 of Fun IA.LeF [l2,r2] \<Rightarrow>
              check (def_checker_main x ty l1 r1 l2 r2 \<or> def_checker_main x ty l2 r2 l1 r1)
              (showsl_lit (STR ''Non-equation not supported''))
             | _ \<Rightarrow> error (showsl_lit (STR ''Invalid 2nd literal''))
           )
          | _ \<Rightarrow> error (showsl_lit (STR ''Invalid 2nd clause''))
         )
        | _ \<Rightarrow> error (showsl_lit (STR ''Invalid 1st literal''))
        )
      | _ \<Rightarrow> error (showsl_lit (STR ''Invalid 1st clause''))
     )
   | _ \<Rightarrow> error (showsl_lit (STR ''Conjunction of more than two''))
  )
 | _ \<Rightarrow> def_checker_eq x ty \<phi>)
 <+? (\<lambda> s. showsl_lit (STR ''error in definibility checker for '') o showsl x o showsl_lit (STR '' on formula\<newline>  '') o showsl_formula.showsl_formula showsl_IA_exp \<phi> o showsl_nl o s)"

sublocale definability_checker
  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and definability_checker = "def_checker :: (_,'v :: {showl, linorder},_) definability_checker"
    and type_fixer = "TYPE(_)"
proof
  fix \<alpha> :: "'v \<times> ty \<Rightarrow> val" and x :: 'v and ty \<phi>
  assume ok: "isOK (def_checker x ty \<phi>)" and alpha: "assignment \<alpha>"
  note ok = ok[unfolded def_checker_def, simplified]
  { fix l1 r1 l2 r2
    assume "def_checker_main x ty l1 r1 l2 r2"
    note ok = this[unfolded def_checker_main_def]
    then have "is_bool (Fun LeF [l1, r1])" and "is_bool (Fun LeF [l2, r2])" by auto
    from ok have id: "l1 = Var (x,ty)" "r2 = Var (x,ty)" "l2 = r1" and fresh: "(x,ty) \<notin> vars_term r1" by auto
    from fresh have id2: "(\<lbrakk>r1\<rbrakk> (\<alpha>((x, ty) := a))) = (\<lbrakk>r1\<rbrakk> \<alpha>)" for a by simp
    from ok have "r1 :\<^sub>f ty" by auto
    with alpha have r1: "\<lbrakk>r1\<rbrakk> \<alpha> \<in> Values_of_type ty"
      using eval_types by auto
    have "(\<exists>a \<in> Values_of_type ty. \<alpha>((x, ty) := a) \<Turnstile> l1 \<le>\<^sub>I\<^sub>A r1 \<and> \<alpha>((x, ty) := a) \<Turnstile> l2 \<le>\<^sub>I\<^sub>A r2)"
      unfolding id using r1 by (intro bexI[of _ "\<lbrakk>r1\<rbrakk> \<alpha>"], auto simp: id2)
  } note * = this
  { fix l1 r1
    assume "def_checker_main' x ty l1 r1"
    note ok = this[unfolded def_checker_main'_def]
    then have "is_bool (Fun EqF [l1,r1])" by auto
    from ok have id: "l1 = Var (x,ty)" and fresh: "(x,ty) \<notin> vars_term r1" by auto
    from fresh have id2: "(\<lbrakk>r1\<rbrakk> (\<alpha>((x, ty) := a))) = (\<lbrakk>r1\<rbrakk> \<alpha>)" for a by simp
    from ok have "r1 :\<^sub>f ty" by auto
    with alpha have r1: "\<lbrakk>r1\<rbrakk> \<alpha> \<in> Values_of_type ty"
      using eval_types by auto
    have "\<exists>a \<in> Values_of_type ty.
      to_int (\<lbrakk>l1\<rbrakk> (\<alpha>((x, ty) := a))) = to_int (\<lbrakk>r1\<rbrakk> (\<alpha>((x, ty) := a)))"
      unfolding id using r1 by (intro bexI[of _ "\<lbrakk>r1\<rbrakk> \<alpha>"], auto simp: id2)
  } note ** = this
  {
    fix eq
    assume ok: "isOK(def_checker_eq x ty eq)"
    note ok = ok[unfolded def_checker_eq_def]
    from ok obtain l1 r1 where [simp]: "eq = (l1 =\<^sub>I\<^sub>A r1)"
      by (auto split: list.splits sig.splits formula.splits term.splits)
    note **[dest!]
    note ok = ok[simplified]
    from ok have "\<exists>a\<in>Values_of_type ty. \<alpha>((x, ty) := a) \<Turnstile> eq" by force
  } note *** = this
  show "\<exists>a \<in> Values_of_type ty. \<alpha>((x, ty) := a) \<Turnstile> \<phi>"
  proof (cases \<phi>)
    case [simp]: (Conjunction \<phi>s)
    note ok = ok[simplified]
    show ?thesis
    proof (cases \<phi>s rule: list_4_cases)
      case Nil with ok show ?thesis by (cases ty, auto)
    next
      case [simp]: (2 cl1 cl2)
      note ok = ok[simplified]
      from ok obtain l1 r1 where [simp]: "cl1 = (l1 \<le>\<^sub>I\<^sub>A r1)"
        by (auto split: list.splits sig.splits formula.splits term.splits)
      with ok obtain l2 r2 where [simp]: "cl2 = (l2 \<le>\<^sub>I\<^sub>A r2)"
        by (auto split: list.splits sig.splits formula.splits term.splits)
      note ok = ok[simplified]
      note *[dest!]
      from ok show ?thesis by auto
    next
      case [simp]: (1 eq)
      show ?thesis using ok ***[of eq] by auto
    qed (insert ok, auto)
  next
    case [simp]: (Atom eq)
    with ok ***[of "Atom eq"] show ?thesis by auto
  qed (insert ok, auto simp: def_checker_eq_def)
qed
end

end
