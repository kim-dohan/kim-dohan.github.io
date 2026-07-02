(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory IA_Checker
imports
  Integer_Arithmetic
  Branch_and_Bound
  "HOL-Library.Mapping"
  Auxx.Util
begin

no_notation Simplex.curr_val_satisfies_state ("\<Turnstile>")
hide_const (open) eval_poly

datatype la_solver_type = Simplex_Solver | BB_Solver

fun la_solver :: "la_solver_type \<Rightarrow> constraint list \<Rightarrow> (nat \<Rightarrow> int) option" where
  "la_solver BB_Solver cs = branch_and_bound_int cs" 
| "la_solver Simplex_Solver cs = (case simplex cs of Unsat _ \<Rightarrow> None | Sat v \<Rightarrow> Some (\<lambda> x. floor (\<langle>v\<rangle> x)))" 

lemma la_solver_unsat: assumes "la_solver type cs = None"
  shows "\<not> (rat_of_int \<circ> v) \<Turnstile>\<^sub>c\<^sub>s set cs"
proof (cases type)
  case BB_Solver
  thus ?thesis using assms branch_and_bound_int_unsat[of cs] by auto
next
  case Simplex_Solver
  thus ?thesis using simplex(1)[of cs] assms by (auto split: sum.splits)
qed

subsection \<open>Validity checking functionality\<close>

datatype 'v linearity = Non_Linear | One | Variable 'v

fun monom_list_linearity :: "'v monom_list \<Rightarrow> 'v linearity" where
  "monom_list_linearity [] = One"
| "monom_list_linearity [(x,n)] = (if n = 1 then Variable x else Non_Linear)"
| "monom_list_linearity _ = Non_Linear"

lift_definition monom_linearity :: "'v :: linorder monom \<Rightarrow> 'v linearity" is monom_list_linearity .

lemma monom_linearity: "monom_linearity m = One \<Longrightarrow> eval_monom \<alpha> m = 1"
  "monom_linearity (m :: 'v :: linorder monom) = Variable x \<Longrightarrow> eval_monom \<alpha> m = \<alpha> x"
  "monom_linearity (m :: 'v :: linorder monom) = Variable x \<Longrightarrow> monom_vars_list m = [x]"
proof (atomize (full), transfer fixing: x \<alpha>)
  fix m :: "'v monom_list"
  show "(monom_list_linearity m = linearity.One \<longrightarrow> eval_monom_list \<alpha> m = 1) \<and>
         (monom_list_linearity m = Variable x \<longrightarrow> eval_monom_list \<alpha> m = \<alpha> x) \<and>
         (monom_list_linearity m = Variable x \<longrightarrow> map fst m = [x])"
    by (cases m, force, cases "tl m", cases "hd m", auto)
qed

context IA_locale begin

subsubsection \<open>Via Automatic Solver\<close>

context
  fixes \<rho> :: "'v :: linorder \<Rightarrow> nat" (* renamings between variables *)
    and \<tau> :: "nat \<Rightarrow> 'v"
begin
fun ipoly_to_linear_poly :: "'v ipoly \<Rightarrow> (linear_poly \<times> int) option" where
  "ipoly_to_linear_poly [] = Some (0,0)"
| "ipoly_to_linear_poly ((monomial,c) # rest) = do {
     (p,d) \<leftarrow> ipoly_to_linear_poly rest;
     case monom_linearity monomial of
       One \<Rightarrow> Some (p,c + d)
     | Variable x \<Rightarrow> Some (lp_monom (of_int c) (\<rho> x) + p, d)
     | Non_Linear \<Rightarrow> None
  }"

definition True_constraint :: constraint where "True_constraint = GEQ 0 0"

lemma True_constraint[simp]: "a \<Turnstile>\<^sub>c True_constraint"
  unfolding True_constraint_def by (auto, transfer, auto)

primrec to_linear_constraints :: "'v poly_constraint \<Rightarrow> constraint list" where
  "to_linear_constraints (Poly_Ge p) = (case ipoly_to_linear_poly p of None \<Rightarrow> []
       | Some (q,c) \<Rightarrow> [GEQ q (of_int (- c))])"
| "to_linear_constraints (Poly_Eq p) = (case ipoly_to_linear_poly p of None \<Rightarrow> []
       | Some (q,c) \<Rightarrow> [EQ q (of_int (- c))])"

definition to_rat_assignment :: "('v \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> rat)" where
  "to_rat_assignment \<alpha> = rat_of_int o (\<lambda> n. \<alpha> (\<tau> n))"

context
  fixes \<alpha> :: "'v :: linorder \<Rightarrow> int"
    and \<beta> :: "nat \<Rightarrow> rat"
  assumes beta: "\<beta> = to_rat_assignment \<alpha>"
begin

lemma ipoly_to_linear_poly: "(\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v)
  \<Longrightarrow> ipoly_to_linear_poly p = Some (q, c)
  \<Longrightarrow> of_int (eval_poly \<alpha> p) =  (q \<lbrace>\<beta>\<rbrace> + of_int c)"
proof (induct p arbitrary: q c)
  case Nil
  then show ?case by (simp add: valuate_zero)
next
  case (Cons xc p qq e)
  obtain xs c where xc: "xc = (xs,c)" by force
  from Cons(3) xc obtain q d where p: "ipoly_to_linear_poly p = Some (q,d)" by (auto split: bind_splits)
  from Cons(1)[OF Cons(2) this] have IH: "of_int (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_int d" by (auto simp: poly_vars_def)
  show ?case
  proof (cases "monom_linearity xs")
    case One
    with Cons(3) p xc have id: "qq = q" "e = d + c" by auto
    show ?thesis unfolding id xc One using IH monom_linearity(1)[OF One] by auto
  next
    case (Variable x)
    note xs = monom_linearity(2-3)[OF Variable]
    from Cons(3) p xc Variable have id: "qq = lp_monom (rat_of_int c) (\<rho> x) + q" "e = d" by auto
    from Cons(2)[of x] have "\<tau> (\<rho> x) = x" unfolding xc poly_vars_def by (auto simp: xs)
    then show ?thesis unfolding id xc using IH xs(1)[of \<alpha>]
      by (simp add: Cons xc valuate_add valuate_lp_monom beta to_rat_assignment_def[abs_def] o_def ac_simps)
  qed (insert Cons, auto simp: xc split: bind_splits)
qed

lemma to_linear_constraints:
  assumes "interpret_poly_constraint \<alpha> c"
    and "(\<And> v. v \<in> vars_poly_constraint c \<Longrightarrow> \<tau> (\<rho> v) = v)"
    and cc: "cc \<in> set (to_linear_constraints c)"
  shows "\<beta> \<Turnstile>\<^sub>c cc"
proof (cases c)
  case (Poly_Ge p)
  let ?c = "ipoly_to_linear_poly p"
  show ?thesis
  proof (cases ?c)
    case (Some qc)
    then obtain q d where c: "?c = Some (q,d)" by (cases qc, auto)
    with Poly_Ge cc have id: "cc = GEQ q (of_int (- d))" by auto
    from Poly_Ge assms(2) have "\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v" by auto
    from ipoly_to_linear_poly[OF this c]
    have id': "of_int (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_int d" by auto
    from assms(1)[unfolded Poly_Ge, simplified] have ge: "eval_poly \<alpha> p \<ge> 0" by auto
    show ?thesis unfolding id using ge id' by auto
  qed (insert Poly_Ge cc, auto)
next
  case (Poly_Eq p)
  let ?c = "ipoly_to_linear_poly p"
  show ?thesis
  proof (cases ?c)
    case (Some qc)
    then obtain q d where c: "?c = Some (q,d)" by (cases qc, auto)
    with Poly_Eq cc have id: "cc = EQ q (of_int (- d))" by auto
    from Poly_Eq assms(2) have "\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v" by auto
    from ipoly_to_linear_poly[OF this c]
    have id': "of_int (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_int d" by auto
    from assms(1)[unfolded Poly_Eq, simplified] have eq: "eval_poly \<alpha> p = 0" by auto
    show ?thesis unfolding id using eq id' by auto
  qed (insert Poly_Eq cc, auto)
qed

lemma la_solver_to_linear_constraints_unsat:
  assumes "la_solver type (concat (map to_linear_constraints \<phi>s)) = None"
    and "\<And> \<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
    and renaming: "(\<And> v \<phi>. v \<in> vars_poly_constraint \<phi> \<Longrightarrow> \<phi> \<in> set \<phi>s \<Longrightarrow> \<tau> (\<rho> v) = v)"
  shows False
proof -
  from to_linear_constraints[OF assms(2) renaming]
  have "\<And> \<phi> c. \<phi> \<in> set \<phi>s \<Longrightarrow> c \<in> set (to_linear_constraints \<phi>) \<Longrightarrow> \<beta> \<Turnstile>\<^sub>c c" by auto
  then have "\<beta> \<Turnstile>\<^sub>c\<^sub>s set (concat (map to_linear_constraints \<phi>s))" by simp
  with la_solver_unsat[OF assms(1)]
  have "\<beta> \<noteq> rat_of_int \<circ> v" for v by auto
  thus False unfolding beta to_rat_assignment_def by auto
qed
end
end

(* la_solver BB_Solver is not a decision procedure because of the linearization process;
   therefore if la_solver finds a solution, we always check it against the original constraints *)
definition unsat_via_la_solver :: "la_solver_type \<Rightarrow> 'v :: linorder poly_constraint list \<Rightarrow> ('v list \<times> ('v \<Rightarrow> int)) option option" where
  "unsat_via_la_solver type les = (let vs = remdups (concat (map vars_poly_constraint_list les));
     ren_map = Mapping.of_alist (zip vs [0 ..< length vs]);
     ren_fun = (\<lambda> v. case Mapping.lookup ren_map v of None \<Rightarrow> 0 | Some n \<Rightarrow> n);
     cs = concat (map (to_linear_constraints ren_fun) les)     
    in case la_solver type cs of None \<Rightarrow> Some None  \<comment> \<open>unsat\<close>
     | Some \<beta> \<Rightarrow> \<comment> \<open>linearized constraints are sat\<close>
      let \<alpha> = \<beta> o ren_fun in if 
      (\<forall> li \<in> set les. interpret_poly_constraint \<alpha> li) then Some (Some (vs, \<alpha>)) else None)"

lemma sat_via_la_solver: assumes "unsat_via_la_solver type les = Some (Some (vs, \<alpha>))" 
  shows "\<phi> \<in> set les \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
  using assms unfolding unsat_via_la_solver_def Let_def
  by (auto split: option.splits if_splits)

lemma unsat_via_la_solver: assumes unsat: "unsat_via_la_solver type les = Some None"
  and sat: "\<And> \<phi>. \<phi> \<in> set les \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
shows False
proof -
  obtain vs ren_fun invi where
    vs: "vs = remdups (concat (map vars_poly_constraint_list les))" and
    ren_fun: "ren_fun = (\<lambda> v. case map_of (zip vs [0 ..< length vs]) v of None \<Rightarrow> 0 | Some n \<Rightarrow> n)" and
    inv: "invi = (\<lambda> i. vs ! i)" by auto
  have dist: "distinct vs" unfolding vs by auto
  {
    fix v \<phi>
    assume "v \<in> vars_poly_constraint \<phi>" "\<phi> \<in> set les"
    then have "v \<in> set vs" unfolding vs by auto
    then obtain i where i: "i < length vs" and v: "v = vs ! i" unfolding set_conv_nth by auto
    then have "ren_fun (vs ! i) = i" unfolding ren_fun using dist by simp
    then have "invi (ren_fun v) = v" unfolding v inv by simp
  } note inv = this
  from unsat[unfolded unsat_via_la_solver_def Let_def lookup_of_alist, folded vs, folded ren_fun]
  have unsat: "la_solver type (concat (map (to_linear_constraints ren_fun) les)) = None"
    by (auto split: option.splits if_splits)
  from la_solver_to_linear_constraints_unsat[OF refl unsat sat inv] show False .
qed

end


instantiation la_solver_type :: default begin
  definition "default = BB_Solver"
  instance ..
end


instantiation la_solver_type :: showl
begin
fun showsl_la_solver_type where
  "showsl_la_solver_type BB_Solver = showsl_lit (STR ''Branch-and-Bound'')"
| "showsl_la_solver_type Simplex_Solver = showsl_lit (STR ''Simplex'')"
definition "showsl_list (xs :: la_solver_type list) = default_showsl_list showsl xs"
instance ..
end

fun is_Atom_Var where 
    "is_Atom_Var (Atom _) = True" 
  | "is_Atom_Var (NegAtom (Var _)) = True"
  | "is_Atom_Var _ = False" 

inductive is_conj_atom_var
where "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> is_Atom_Var \<phi>) \<Longrightarrow> is_conj_atom_var (Conjunction \<phi>s)"

definition split_bool_vars where
  "split_bool_vars = List.partition (\<lambda> lit. is_Var (get_Atom lit))" 

context IA_locale begin

definition unsat_checker :: "la_solver_type \<Rightarrow> 'v :: {showl,linorder} poly_constraint list \<Rightarrow> showsl check" where
  "unsat_checker solver cnjs = (
       case unsat_via_la_solver solver cnjs
         of None \<Rightarrow> error (showsl_lit (STR ''could not use linear arithmetic solver to prove unsatisfiability''))
         | Some None \<Rightarrow> return ()
         | Some (Some (vs, \<alpha>)) \<Rightarrow> error (showsl_lit (STR ''the linear inequalities are satisfiable:\<newline>'')
             o showsl_list_gen (\<lambda> v. showsl (var_monom v) o showsl_lit (STR '' := '') o showsl (\<alpha> v) ) (STR '''') (STR '''') (STR ''\<newline>'') (STR '''') vs
           )
    )
  <+? (\<lambda> s. showsl_lit (STR ''The linear inequalities\<newline>  '') \<circ> showsl_sep showsl_poly_constraint (showsl_lit (STR ''\<newline>  '')) cnjs \<circ>
     showsl_lit (STR ''\<newline>cannot be proved unsatisfiable via solver\<newline>  '') \<circ> showsl solver \<circ> showsl_nl \<circ> s)"


(* Show that there exists an assignment \<alpha> *)
fun some_alpha::"'a \<times> ty \<Rightarrow> val" where
  "some_alpha (v,IntT) = Int 0" |
  "some_alpha (v,BoolT) = Bool True"

lemma some_alpha:"assignment some_alpha"
proof
  fix x t show "some_alpha (x::'a, t) \<in> Values_of_type t" by (cases t; simp)
qed

lemma unsat_checker:
  assumes ok: "isOK(unsat_checker type cnjs)"
  and "\<And> c. c \<in> set cnjs \<Longrightarrow> interpret_poly_constraint \<alpha> c"
shows False
proof -
  from ok have "unsat_via_la_solver type cnjs = Some None" by (auto simp: unsat_checker_def split: option.splits)
  from unsat_via_la_solver[OF this assms(2)] show False by auto
qed

subsection \<open>Encoding entailment checking as UNSAT-problems\<close>

(* negated literals and variables are normalized *)
fun lit_normalized :: "bool \<Rightarrow> 'v IA.exp \<Rightarrow> bool" where
  "lit_normalized False e = True" 
| "lit_normalized True (Var _) = True" 
| "lit_normalized _ _ = False" 

fun lit_normalize :: "bool \<Rightarrow> 'v IA.exp \<Rightarrow> 'v IA.formula"
  where "lit_normalize False e = NegAtom e"
    | "lit_normalize _ (Fun LessF [a,b]) = NegAtom (Fun LeF [b,a])"
    | "lit_normalize _ (Fun LeF [a,b]) = NegAtom (Fun LessF [b,a])"
    | "lit_normalize _ (Fun EqF [a,b]) = Conjunction [NegAtom (Fun LessF [a,b]), NegAtom (Fun LessF [b,a])]"
    | "lit_normalize _ (Var x) = Atom (Var x)" 

lemma is_boolE:
  assumes e: "is_bool e"
  and "\<And> s e1 e2. e = Fun s [e1,e2] \<Longrightarrow> s \<in> {LessF, LeF, EqF} \<Longrightarrow> e1 :\<^sub>f IntT \<Longrightarrow> e2 :\<^sub>f IntT \<Longrightarrow> thesis"
  and "\<And> x. e = Var (x,BoolT) \<Longrightarrow> thesis" 
  shows "thesis"
proof (cases e)
  case Fun
  with e[unfolded is_bool_def] obtain ty where ty: "e :\<^sub>f ty" "ty \<in> {BoolT}" "is_Fun e" by auto
  from ty assms(2) show thesis by (induct e ty rule: has_type_induct, auto)
next
  case (Var xty)
  with e[unfolded is_bool_def] show ?thesis using assms(3) by (cases xty, auto)
qed

fun translate_atom
where "translate_atom (Atom e) = e"

definition "translate_atoms = map translate_atom"

fun translate_conj
  where "translate_conj (Conjunction \<phi>s) = (case split_bool_vars \<phi>s of
      (bvars, ia_lits) \<Rightarrow> (bvars, translate_atoms ia_lits))"

(* find complementary boolean literals *)
definition unsat_bool_checker where 
  "unsat_bool_checker blits = (\<exists> blit \<in> set blits. (\<not>\<^sub>f blit) \<in> set blits)" 

definition check_clause :: "la_solver_type \<Rightarrow> 'v::{showl,linorder} IA.formula \<Rightarrow> showsl check"
  where "check_clause type \<phi> \<equiv> case translate_conj (\<not>\<^sub>f \<phi>) of (bvars, ia_lits)
     \<Rightarrow> let es = map IA_exp_to_poly_constraint ia_lits in
     if unsat_bool_checker bvars then succeed else
    unsat_checker type es
       <+? (\<lambda> s. showsl_lit (STR ''Could not prove unsatisfiability of IA conjunction\<newline>'')
     \<circ> showsl_list_gen showsl_poly_constraint (STR ''False'') (STR '''') (STR '' && '') (STR '''') es \<circ> showsl_nl \<circ> s)"

lemma translate_atom:
  assumes "translate_atom \<phi> = e" and "formula \<phi>" and "is_Atom \<phi>"
  shows "\<phi> \<Longleftrightarrow>\<^sub>f Atom e" by (cases \<phi>, insert assms, auto)

lemma translate_conj:
  assumes es: "translate_conj (\<phi> :: 'v IA.formula) = (bvars, es)"
      and \<phi>: "formula \<phi>" "is_conj_atom_var \<phi>"
    shows "\<phi> \<Longleftrightarrow>\<^sub>f (Conjunction bvars \<and>\<^sub>f conj_atoms es)" 
       "e \<in> set es \<Longrightarrow> is_bool e \<and> is_Fun e"
       "bv \<in> set bvars \<Longrightarrow> isLit bv \<and> is_Var (get_Atom bv) \<and> is_bool (get_Atom bv)" 
proof-
  from \<phi>(2,1) obtain lits where \<phi>C: "\<phi> = Conjunction lits" and l: "\<And> l. l \<in> set lits \<Longrightarrow> is_Atom_Var l \<and> formula l"
    by (cases, auto)
  with es obtain ls where lits: "split_bool_vars lits = (bvars, ls)" 
    by (auto split: prod.splits)
  with es lits \<phi>C have es: "es = map translate_atom ls" by (auto simp: translate_atoms_def)
  {
    assume "e \<in> set es"
    then obtain l where 
      l: "l \<in> set lits" and e: "e = translate_atom l" and noVar: "\<not> is_Var (get_Atom l)" 
      unfolding es using lits[unfolded split_bool_vars_def] by auto
    from \<phi>(2,1) l \<phi>C have l': "is_Atom_Var l" "formula l" 
      by (induct, auto)
    then show "is_bool e \<and> is_Fun e" unfolding e using noVar 
      by (cases l, auto)
  }
  have "\<phi> \<Longleftrightarrow>\<^sub>f (Conjunction bvars \<and>\<^sub>f Conjunction ls)" 
    unfolding \<phi>C using lits unfolding split_bool_vars_def by auto
  moreover have "Conjunction ls \<Longleftrightarrow>\<^sub>f conj_atoms es" 
  proof -
    {
      fix l
      assume l: "l \<in> set ls" 
      have "l \<Longleftrightarrow>\<^sub>f Atom (IA.translate_atom l)" 
      proof (rule translate_atom[OF refl])
        from l have l: "l \<in> set lits" and noVar: "\<not> is_Var (get_Atom l)" 
          using lits[unfolded split_bool_vars_def] by auto
        from \<phi>(2,1) l \<phi>C have l': "is_Atom_Var l" "formula l" 
          by (induct, auto)
        thus "is_Atom l" using noVar by (cases l, auto)
        show "formula l" by fact
      qed
    }
    thus ?thesis unfolding es by simp
  qed  
  ultimately show "\<phi> \<Longleftrightarrow>\<^sub>f (Conjunction bvars \<and>\<^sub>f conj_atoms es)"  by auto
  {
    assume "bv \<in> set bvars" 
    hence bv: "bv \<in> set lits" and isVar: "is_Var (get_Atom bv)" 
      using lits[unfolded split_bool_vars_def] by auto
    from l[OF bv] isVar
    show "isLit bv \<and> is_Var (get_Atom bv) \<and> is_bool (get_Atom bv)" 
      by (cases bv, auto)
  }
qed

sublocale pre_logic_checker
  where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and logic_checker = check_clause
    and showsl_atom = showsl_IA_exp
    and normalize_lit = lit_normalize
    and normalized_lit = lit_normalized .


lemma negate_normalized_clause: "is_normalized_clause \<phi> \<Longrightarrow> is_conj_atom_var (\<not>\<^sub>f \<phi>)" 
  apply (cases \<phi>, auto simp: is_normalized_clause_def intro!: is_conj_atom_var.intros)
  subgoal for fs f
    apply (cases f)
    subgoal for x by (cases x, auto)
    apply auto
    done
  done
    

lemma check_clause:
  fixes \<phi> :: "'a::{linorder,showl} IA.formula"
  assumes ok: "isOK (check_clause solver \<phi>)" and \<phi>: "formula \<phi>" and clause: "is_normalized_clause \<phi>"
  shows "\<Turnstile>\<^sub>f \<phi>"
proof
  fix \<alpha> :: "'a \<times> ty \<Rightarrow> val"
  assume \<alpha>: "assignment \<alpha>"
  show "satisfies \<alpha> \<phi>"
    proof (rule ccontr)
    assume not: "\<not> ?thesis"
    from ok obtain es bvars
    where es: "translate_conj (\<not>\<^sub>f\<phi>) = (bvars, es)"
      and ok: "unsat_bool_checker bvars \<or> isOK (unsat_checker solver (map IA_exp_to_poly_constraint es))"
      by (unfold check_clause_def, force)
    have is_conj: "is_conj_atom_var (\<not>\<^sub>f \<phi>)" by (rule negate_normalized_clause[OF clause])
    hence "\<not>\<^sub>f \<phi> \<Longleftrightarrow>\<^sub>f Conjunction bvars \<and>\<^sub>f conj_atoms es"
      by (intro translate_conj[OF es], simp add: \<phi>)
    from this \<alpha> not have 
      sat_bool: "\<alpha> \<Turnstile> Conjunction bvars" and 
      sat_ia: "\<alpha> \<Turnstile> conj_atoms es" 
      by (auto simp:satisfies_Language)
    from sat_bool have sat_bool: "bv \<in> set bvars \<Longrightarrow> \<alpha> \<Turnstile> bv" for bv by auto
    have "\<not> unsat_bool_checker bvars" 
    proof 
      assume "unsat_bool_checker bvars" 
      from this[unfolded unsat_bool_checker_def] obtain bv where
        "bv \<in> set bvars" and "(\<not>\<^sub>f bv) \<in> set bvars" 
        unfolding unsat_bool_checker_def by auto
      from sat_bool[OF this(1)] sat_bool[OF this(2)] 
      show False by simp
    qed
    with ok have ok: "isOK (IA.unsat_checker solver (map IA_exp_to_poly_constraint es))" by simp
    show False
    proof(rule unsat_checker[OF ok])
      fix v
      assume v: "v \<in> set (map IA_exp_to_poly_constraint es)"
      then obtain w where w: "w \<in> set es" and v: "v = IA_exp_to_poly_constraint w" by force
      from sat_ia w have eval: "\<alpha> \<Turnstile> Atom w" by auto
      from \<phi> translate_conj(2)[OF es _ is_conj w]
      have "is_bool w" "is_Fun w" by auto
      from IA_exp_to_poly_constraint[OF \<alpha> this] eval
      show "interpret_poly_constraint (\<lambda>a. to_int (\<alpha> (a, IntT))) v"
        by (auto simp: v)
    qed
  qed
qed


sublocale logic_checker
where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and logic_checker = check_clause
    and showsl_atom = showsl_IA_exp
    and normalize_lit = lit_normalize
    and normalized_lit = lit_normalized 
proof (unfold_locales, goal_cases)
  case (1 h \<phi>)
  then show ?case using check_clause by auto
next
  case *: (2 e b)
  show ?case
  proof (cases b)
    case False
    thus ?thesis using * by auto
  next
    case True
    hence b: "b = True" by auto
    show ?thesis unfolding b using *
    proof (elim is_boolE, simp, goal_cases)
      case (1 le e1 e2)
      have [simp]: "i < Suc (Suc 0) \<longleftrightarrow> i = 0 \<or> i = Suc 0" for i by auto
      from 1(2-4)
      show ?case by (cases le, auto)
    qed auto
  qed
next
  case *: (3 e \<alpha> b)
  show ?case
  proof (cases b)
    case False
    thus ?thesis using * by auto
  next
    case True
    hence b: "b = True" by auto
    show ?thesis unfolding b using *
    proof (elim is_boolE, simp, goal_cases)
      case (1 le e1 e2)
      have [simp]: "i < Suc (Suc 0) \<longleftrightarrow> i = 0 \<or> i = Suc 0" for i by auto
      from 1(2-4)
      show ?case by (cases le, auto)
    qed auto
  qed
qed
  
end
end
