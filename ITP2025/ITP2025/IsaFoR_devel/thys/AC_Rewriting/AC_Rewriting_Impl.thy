(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Rewriting_Impl
imports 
  AC_Rewriting
  First_Order_Rewriting.Trs_Impl
  "Transitive-Closure-II.RTrancl"
  AC_Equivalence
begin

definition check_AC_rule :: "('f,'v)rule \<Rightarrow> bool" where 
  "check_AC_rule lr \<equiv> case lr of (l,r) \<Rightarrow> if is_Var l then False
    else let f = fst (the (root l)) in
      funas_term l = {(f,2)} 
    \<and> funas_term r = {(f,2)}
    \<and> vars_term_ms l = vars_term_ms r 
    \<and> funs_term_ms l = funs_term_ms r"
  
lemma check_AC_rule: "check_AC_rule (l,r) \<longleftrightarrow>
  funs_term_ms l = funs_term_ms r \<and> vars_term_ms l = vars_term_ms r \<and> (\<exists> f. funas_term l = {(f,2)} \<and> funas_term r = {(f,2)})"
  unfolding check_AC_rule_def split Let_def
  by (cases l, auto)

definition check_AC_theory :: "('f :: showl, 'v :: showl)rules \<Rightarrow> showsl check" where
  "check_AC_theory E \<equiv> check_allm (\<lambda> lr. check (check_AC_rule lr) 
    (showsl_lit (STR ''rule '') o showsl_rule lr o showsl_lit (STR '' violates AC-property''))) E"

lemma check_AC_theory[simp]: "isOK(check_AC_theory E) = AC_theory (set E)"
  unfolding check_AC_theory_def AC_theory_def
  by (auto simp: check_AC_rule)

definition check_E_reachable :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" where
  "check_E_reachable E s t \<equiv> t \<in> set (mk_rtrancl_list (=) (rewrite E) [s])"

lemma check_E_reachable[simp]: assumes "AC_theory (set E)" (* symbol_preserving would suffice *)
  shows "check_E_reachable E s t = ((s,t) \<in> (rstep (set E))^*)"
proof -
  interpret AC_theory "set E" by fact
  let ?rewr = "{(a, b). b \<in> set (rewrite E a)}"
  have rewr: "?rewr = rstep (set E)"
  proof (subst rewrite)
    fix l r
    assume "(l,r) \<in> set E"
    from ac_ruleD(2)[OF this] show "vars_term r \<subseteq> vars_term l" 
    unfolding set_mset_vars_term_ms[symmetric] by auto
  qed auto
  interpret relation_subsumption_list "rewrite E" "(=)"
  proof
    fix a
    show "finite {b. (a, b) \<in> {(a, b). b \<in> set (rewrite E a)}\<^sup>*}" unfolding rewr
      by (rule finite_reachable)      
  qed auto
  show ?thesis unfolding check_E_reachable_def mk_rtrancl_list 
    mk_rtrancl_no_subsumption[OF refl] symmetric_trs_def rewr by auto
qed
  

definition check_symmetric_AC_theory :: "('f :: showl, 'v :: showl)rules \<Rightarrow> showsl check" where
  "check_symmetric_AC_theory E \<equiv> do {
     check_AC_theory E;
     check_allm (\<lambda> (l,r). check (check_E_reachable E r l) 
       (showsl_lit (STR ''rhs '') o showsl r o showsl_lit (STR '' does not rewrite to lhs '') o showsl l)) E
       <+? (\<lambda> s. showsl_lit (STR ''theory is not symmetric\<newline>'') o s)
   }"

lemma check_symmetric_AC_theory[simp]: "isOK(check_symmetric_AC_theory E) \<longleftrightarrow>
  AC_theory (set E) \<and> symmetric_trs (set E)"
  by (auto simp: check_symmetric_AC_theory_def symmetric_trs_def)

definition check_size_preserving_trs :: "('f :: showl, 'v :: showl)rules \<Rightarrow> showsl check" where
  "check_size_preserving_trs E \<equiv> do {
     check_allm (\<lambda> (l,r). check (num_symbs l = num_symbs r \<and> vars_term_ms l = vars_term_ms r) 
       (showsl_lit (STR ''rule '') o showsl_rule (l,r) o showsl_lit (STR '' is not size preserving''))) E
       <+? (\<lambda> s. showsl_lit (STR ''TRS is not size-preserving\<newline>'') o s)
   }"

lemma check_size_preserving_trs[simp]: "isOK(check_size_preserving_trs E) \<longleftrightarrow>
  size_preserving_trs (set E)"
  by (auto simp: check_size_preserving_trs_def size_preserving_trs_def)

definition check_only_C_rule :: "'f set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "check_only_C_rule OC lr \<equiv> case lr of (Fun f [s,t], r) \<Rightarrow> f \<in> OC \<longrightarrow> r = Fun f [t,s]
    | _ \<Rightarrow> True"

lemma check_only_C_rule[simp]: "check_only_C_rule OC (l,r) = (\<forall> f. root l = Some (f,2) \<longrightarrow> f \<in> OC \<longrightarrow> 
  (\<exists> s t. (l,r) = (Fun f [s,t], Fun f [t,s])))"
proof (cases "is_Fun l \<and> num_args l = 2")
  case False
  then show ?thesis unfolding check_only_C_rule_def
    by (cases l, force, cases "args l"; cases "tl (args l)"; cases "tl (tl (args l))"; auto)
next
  case True
  from True obtain f s t where l: "l = Fun f [s,t]"
    by (cases l, force, cases "args l"; cases "tl (args l)"; cases "tl (tl (args l))"; auto)
  show ?thesis unfolding l check_only_C_rule_def by simp
qed

definition check_only_C_theory :: "'f set \<Rightarrow> ('f :: showl,'v :: showl)rules \<Rightarrow> showsl check" where
  "check_only_C_theory OC E \<equiv> check_allm (\<lambda> lr. check (check_only_C_rule OC lr) 
    (showsl_lit (STR ''rule '') o showsl_rule lr o showsl_lit (STR '' violates only-C-property''))) E"

lemma check_only_C_theory[simp]: "AC_theory (set E) \<Longrightarrow> 
  isOK(check_only_C_theory OC E) = AC_C_theory (set E) OC"
  unfolding AC_C_theory_def AC_C_theory_axioms_def check_only_C_theory_def by auto

fun check_ext_rule1 :: "('f,'v)rule \<Rightarrow> 'f \<Rightarrow> 'v set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "check_ext_rule1 (l,r) f X (Fun g [l', Var x], Fun g' [r', Var x']) = (((l,r,f,f,x) = (l',r',g,g',x')) \<and> x \<notin> X)"
| "check_ext_rule1 _ _ _ _ = False"

fun check_ext_rule2 :: "('f,'v)rule \<Rightarrow> 'f \<Rightarrow> 'v set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "check_ext_rule2 (l,r) f X (Fun g [Var x,l'], Fun g' [Var x',r']) = (((l,r,f,f,x) = (l',r',g,g',x')) \<and> x \<notin> X)"
| "check_ext_rule2 _ _ _ _ = False"

fun check_ext_rule3 :: "('f,'v)rule \<Rightarrow> 'f \<Rightarrow> 'v set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "check_ext_rule3 (l,r) f X (Fun g [Fun h [Var x,l'], Var y], Fun g' [Fun h' [Var x',r'], Var y']) 
    = ((l,r,f,f,f,f,x,y) = (l',r',g,g',h,h',x',y') \<and> x' \<noteq> y' \<and> x' \<notin> X \<and> y' \<notin> X)"
| "check_ext_rule3 _ _ _ _ = False"

definition check_ext_rule :: "('f,'v)rules \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "check_ext_rule Rext A C lr \<equiv> case lr of (l,r) \<Rightarrow>
    if is_Var l \<or> num_args l \<noteq> 2 \<or> fst (the (root l)) \<notin> A then True else 
    let f = fst (the (root l));
      X = vars_rule lr
    in (\<exists> lr' \<in> set Rext. check_ext_rule1 lr f X lr') \<and> 
    (f \<notin> C \<longrightarrow> (\<exists> lr' \<in> set Rext. check_ext_rule2 lr f X lr') \<and> (\<exists> lr' \<in> set Rext. check_ext_rule3 lr f X lr'))"

definition check_ext_trs :: "('f :: showl,'v :: showl)rules \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check" where
  "check_ext_trs R A C Rext \<equiv> let A' = set A; C' = set C in
    check_allm (\<lambda> lr. check (check_ext_rule Rext A' C' lr) 
      (showsl_lit (STR ''could not find extended rules for rule l -> r:\<newline>  '') o showsl_rule lr o
       showsl_lit (STR ''\<newline>  expecting rule f(l,x) -> f(r,x) for all A and AC symbols,\<newline>'') o
       showsl_lit (STR ''and rules f(x,l) -> f(x,r) and f(f(x,l),y) -> f(f(x,r),y) for all A symbols''))) R
    <+? (\<lambda> s. showsl_lit (STR ''could not ensure validity of AC-extended system\<newline>'') o s)"

lemma check_ext_trs[simp]: assumes ok: "isOK(check_ext_trs R A C Rext)"
  shows "is_ext_trs (set R) (set A) (set C) (set Rext)"
  unfolding is_ext_trs_def
proof (intro allI impI conjI)
  fix l r f
  assume lr: "(l,r) \<in> set R" and f: "f \<in> set A" and l: "root l = Some (f,2)"
  note ok = ok[unfolded check_ext_trs_def Let_def]
  from ok lr have check: "check_ext_rule Rext (set A) (set C) (l,r)" by auto
  let ?X = "vars_rule (l,r)"
  from l f have "(is_Var l \<or> num_args l \<noteq> 2 \<or> fst (the (root l)) \<notin> set A) = False"
    by (cases l, auto)
  note check = check[unfolded check_ext_rule_def split Let_def this if_False, unfolded l]
  from check obtain l' r' where lr': "(l',r') \<in> set Rext" and "check_ext_rule1 (l,r) f ?X (l',r')" by force
  then obtain x where id: "l' = Bin f l (Var x)" "r' = Bin f r (Var x)" and x: "x \<notin> ?X"
    by (cases rule: check_ext_rule1.cases[of "((l,r),f,?X,(l',r'))"], auto)
  show "\<exists>x. x \<notin> ?X \<and> ext_AC_rule f (l, r) (Var x) \<in> set Rext"
    by (intro exI conjI, rule x, insert lr'[unfolded id], auto simp: ext_AC_rule_def)
  assume C: "f \<notin> set C"
  with check obtain l' r' where lr': "(l',r') \<in> set Rext" and "check_ext_rule2 (l,r) f ?X (l',r')" by force
  then obtain x where id: "l' = Bin f (Var x) l" "r' = Bin f (Var x) r" and x: "x \<notin> ?X"
    by (cases rule: check_ext_rule2.cases[of "((l,r),f,?X,(l',r'))"], auto) 
  note 2 = lr'[unfolded id]
  from C check obtain l' r' where lr': "(l',r') \<in> set Rext" and check: "check_ext_rule3 (l,r) f ?X (l',r')" by force
  let ?l = "args l' ! 0" let ?r = "args r' ! 0"
  from check have "\<exists> y z. l' = Bin f (Bin f (Var y) l) (Var z) \<and> r' = Bin f (Bin f (Var y) r) (Var z)
    \<and> y \<notin> ?X \<and> z \<notin> ?X \<and> y \<noteq> z"
    by (cases rule: check_ext_rule3.cases[of "((l,r),f,?X,(l',r'))"], auto)
  then obtain y z where id: "l' = Bin f (Bin f (Var y) l) (Var z)" "r' = Bin f (Bin f (Var y) r) (Var z)" 
    and yz: "y \<notin> ?X" "z \<notin> ?X" "y \<noteq> z"
    by blast
  note 3 = lr'[unfolded id]
  show "\<exists>x y z. x \<notin> ?X \<and> y \<notin> ?X \<and> z \<notin> ?X \<and> x \<noteq> y \<and>
          (Fun f [Var z, l], Fun f [Var z, r]) \<in> set Rext \<and>
          (Fun f [Fun f [Var x, l], Var y], Fun f [Fun f [Var x, r], Var y]) \<in> set Rext"
    using 2 3 x yz by blast
qed
  

definition check_AC_same_as_E :: "'v \<Rightarrow> 'v \<Rightarrow> 'v :: showl \<Rightarrow> ('f :: showl) list \<Rightarrow> 'f list \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check" where
  "check_AC_same_as_E x y z A C E \<equiv> do {
     let X = Var x;
     let Y = Var y; 
     let Z = Var z; 
     check_allm (\<lambda> f. check (check_E_reachable E (Bin f X Y) (Bin f Y X)) f) C
       <+? (\<lambda> f. showsl_lit (STR ''could not simulate C-rules for '') o showsl f o showsl_lit (STR '' by E''));
     check_allm (\<lambda> f. check (check_E_reachable E (Bin f X (Bin f Y Z)) (Bin f (Bin f X Y) Z)) f) A
       <+? (\<lambda> f. showsl_lit (STR ''could not simulate A-rules for '') o showsl f o showsl_lit (STR '' by E''));
     check_allm (\<lambda> f. check (check_E_reachable E (Bin f (Bin f X Y) Z) (Bin f X (Bin f Y Z))) f) A
       <+? (\<lambda> f. showsl_lit (STR ''could not simulate A-rules for '') o showsl f o showsl_lit (STR '' by E''));
     check_allm (\<lambda> (l,r). check ((l,r) \<in> aoc_rewriting.AOCEQ (set A) (set C)) (l,r)) E
       <+? (\<lambda> lr. showsl_lit (STR ''equation '') o showsl_rule lr o showsl_lit (STR '' is not AC-equivalent''))
   } <+? (\<lambda> s. showsl_lit (STR ''could not ensure that equations simulate AC-equivalence\<newline>'') o s)"

(* should be if and only if, but was too lazy to prove it *)
lemma check_AC_same_as_E[simp]: assumes xyz: "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"  
  and AC: "AC_theory (set E :: ('f :: showl,'v :: showl)trs)"
  and ok: "isOK(check_AC_same_as_E x y z A C E)" 
  shows "aoc_rewriting.AOCEQ (set A) (set C) = (rstep (set E))^*" (is "?l = ?r^*")
proof -
  let ?A = "set A" let ?C = "set C"
  let ?X = "Var x" let ?Y = "Var y" let ?Z = "Var z"
  let ?AC = "AC_rules ?A ?C"
  interpret aoc_rewriting ?A ?C .
  define \<delta> where "\<delta> = (\<lambda> (a :: ('f,'v)term) b c u. if u = x then a else if u = y then b else c)"
  have [simp]: 
    "\<And> a b c. \<delta> a b c x = a"
    "\<And> a b c. \<delta> a b c y = b" 
    "\<And> a b c. \<delta> a b c z = c"
    unfolding \<delta>_def using xyz by auto
  have l_rstep: "AOCEQ = (rstep (?AC\<^sup>\<leftrightarrow>))^*" unfolding conversion_def rstep_simps(5) ..
  have ctxt: "ctxt.closed AOCEQ" unfolding l_rstep by auto
  have subst: "subst.closed AOCEQ" unfolding l_rstep 
    by (rule subst.closed_rtrancl, auto)
  have subst': "subst.closed (?r^*)"
    by (rule subst.closed_rtrancl, auto)
  note subst2 = subst.closedD[OF this]
  note ok = ok[unfolded check_AC_same_as_E_def Let_def check_E_reachable[OF AC], simplified]
  have "?r \<subseteq> ?l"
    by (rule rstep_subset[OF ctxt subst], insert ok, auto)
  from rtrancl_mono[OF this]
  have "?r^* \<subseteq> ?l" by auto
  moreover
  {
    fix l r :: "('f,'v)term"
    assume "(l,r) \<in> ?AC\<^sup>\<leftrightarrow>"
    then consider (A) "(l,r) \<in> (A_rules ?A)\<^sup>\<leftrightarrow>" | (C) "(l,r) \<in> (C_rules ?C)\<^sup>\<leftrightarrow>" unfolding AC_rules_def by blast
    then have "(l,r) \<in> ?r^*"
    proof (cases)
      case C
      from this[unfolded C_rules_def] obtain s t f where 
        l: "l = Bin f s t" and r: "r = Bin f t s" and f: "f \<in> ?C" by auto
      from ok f have "(Bin f ?X ?Y, Bin f ?Y ?X) \<in> ?r^*" by auto
      from subst2[OF this, of "\<delta> s t t"] show ?thesis unfolding l r by auto
    next
      case A
      from this[unfolded A_rules_def] consider 
        (1) s t u f where "l = Bin f s (Bin f t u)" "r = Bin f (Bin f s t) u" "f \<in> ?A"
      | (2) s t u f where "l = Bin f (Bin f s t) u" "r = Bin f s (Bin f t u)" "f \<in> ?A" by auto
      then show ?thesis
      proof (cases)
        case 1
        from 1(3) ok have "(Bin f ?X (Bin f ?Y ?Z), Bin f (Bin f ?X ?Y) ?Z) \<in> ?r^*" by auto
        from subst2[OF this, of "\<delta> s t u"] show ?thesis unfolding 1(1-2) by auto
      next
        case 2
        from 2(3) ok have "(Bin f (Bin f ?X ?Y) ?Z, Bin f ?X (Bin f ?Y ?Z)) \<in> ?r^*" by auto
        from subst2[OF this, of "\<delta> s t u"] show ?thesis unfolding 2(1-2) by auto
      qed
    qed
  } note main = this
  have "rstep (?AC\<^sup>\<leftrightarrow>) \<subseteq> ?r^*"
    by (rule rstep_subset[OF _ subst'], insert main, auto)
  from rtrancl_mono[OF this]
  have "?l \<subseteq> ?r^*" unfolding l_rstep by auto
  ultimately show ?thesis by auto
qed

end
