(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Formula
imports
  "Abstract-Rewriting.Abstract_Rewriting"
  First_Order_Rewriting.Trs_Impl
  First_Order_Terms.Option_Monad
  Sorted_Algebra
begin

type_synonym ('v,'t,'d) valuation = "'v \<times> 't \<Rightarrow> 'd"

datatype 'a formula =
  Atom "'a"
| NegAtom "'a"
| Conjunction "'a formula list"
| Disjunction "'a formula list"

syntax "_list_all" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"    ("(3\<And>\<^sub>f _\<leftarrow>_. _)" [0, 51, 10] 10)
translations "\<And>\<^sub>f x\<leftarrow>xs. b" \<rightleftharpoons> "CONST Conjunction (CONST map (\<lambda>x. b) xs)"

syntax "_list_exists" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"    ("(3\<Or>\<^sub>f _\<leftarrow>_. _)" [0, 51, 10] 10)
translations "\<Or>\<^sub>f x\<leftarrow>xs. b" \<rightleftharpoons> "CONST Disjunction (CONST map (\<lambda>x. b) xs)"

instantiation formula :: (showl) showl
begin
fun showsl_formula where 
  "showsl_formula (Atom a) = showsl a" 
| "showsl_formula (NegAtom a) = showsl_lit (STR ''! ('') o showsl a o showsl_lit (STR '')'')" 
| "showsl_formula (Conjunction a) = showsl_list_gen id (STR ''TRUE'') (STR ''('') (STR '' & '') (STR '')'') (map showsl a)"  
| "showsl_formula (Disjunction a) = showsl_list_gen id (STR ''FALSE'') (STR ''('') (STR '' | '') (STR '')'') (map showsl a)"  
definition "showsl_list (xs :: 'a formula list) = default_showsl_list showsl xs"
instance ..
end

fun isLit where "isLit (Atom _) = True" | "isLit (NegAtom _) = True" | "isLit _ = False"

abbreviation disj_atoms :: "'a list \<Rightarrow> 'a formula" where
  "disj_atoms as \<equiv> Disjunction (map Atom as)"
abbreviation conj_atoms :: "'a list \<Rightarrow> 'a formula" where
  "conj_atoms as \<equiv> Conjunction (map Atom as)"

inductive is_conj_lits
where "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> isLit \<phi>) \<Longrightarrow> is_conj_lits (Conjunction \<phi>s)"

inductive is_clause
  where "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> isLit \<phi>) \<Longrightarrow> is_clause (Disjunction \<phi>s)"

lemma is_clause_code[code]: "is_clause (Disjunction ls) = (\<forall> l \<in> set ls. isLit l)" 
  "is_clause (Conjunction xs) = False" 
  "is_clause (Atom a) = False" 
  "is_clause (NegAtom a) = False" 
  by (auto simp: is_clause.simps)
    
fun is_Atom where "is_Atom (Atom _) = True" | "is_Atom _ = False" 
fun get_Atom where "get_Atom (Atom a) = a" | "get_Atom (NegAtom a) = a" 

inductive is_conj_atoms
where "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> is_Atom \<phi>) \<Longrightarrow> is_conj_atoms (Conjunction \<phi>s)"

inductive is_cnf
where "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> is_clause \<phi>) \<Longrightarrow> is_cnf (Conjunction \<phi>s)"

abbreviation form_False :: "'a formula" ("False\<^sub>f")
where "form_False \<equiv> Disjunction []"

abbreviation form_True  :: "'a formula" ("True\<^sub>f")
where "form_True \<equiv> Conjunction []"

fun form_not :: "'a formula \<Rightarrow> 'a formula" ("\<not>\<^sub>f _" [43] 43)
where "(\<not>\<^sub>f Atom a) = NegAtom a"
    | "(\<not>\<^sub>f NegAtom a) = Atom a"
    | "(\<not>\<^sub>f Conjunction \<phi>s) = Disjunction (map form_not \<phi>s)"
    | "(\<not>\<^sub>f Disjunction \<phi>s) = Conjunction (map form_not \<phi>s)"

fun form_and :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infixl "\<and>\<^sub>f" 42)
where "(True\<^sub>f \<and>\<^sub>f \<psi>) = \<psi>"
    | "(\<phi> \<and>\<^sub>f True\<^sub>f) = \<phi>"
    | "(Conjunction \<phi>s \<and>\<^sub>f Conjunction \<psi>s) = Conjunction (\<phi>s @ \<psi>s)"
    | "(Conjunction \<phi>s \<and>\<^sub>f \<psi>) = Conjunction (\<phi>s @ [\<psi>])"
    | "(\<phi> \<and>\<^sub>f Conjunction \<psi>s) = Conjunction (\<phi> # \<psi>s)"
    | "(\<phi> \<and>\<^sub>f \<psi>) = Conjunction [\<phi>,\<psi>]"

fun form_or :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infixl "\<or>\<^sub>f" 41)
where "(False\<^sub>f \<or>\<^sub>f \<psi>) = \<psi>"
    | "(\<phi> \<or>\<^sub>f False\<^sub>f) = \<phi>"
    | "(Disjunction \<phi>s \<or>\<^sub>f Disjunction \<psi>s) = Disjunction (\<phi>s @ \<psi>s)"
    | "(Disjunction \<phi>s \<or>\<^sub>f \<psi>) = Disjunction (\<phi>s @ [\<psi>])"
    | "(\<phi> \<or>\<^sub>f Disjunction \<psi>s) = Disjunction (\<phi> # \<psi>s)"
    | "(\<phi> \<or>\<^sub>f \<psi>) = Disjunction [\<phi>,\<psi>]"

fun simplify
where "simplify (Disjunction (\<phi>#\<phi>s)) = (simplify \<phi> \<or>\<^sub>f simplify (Disjunction \<phi>s))"
    | "simplify (Conjunction [\<phi>]) = simplify \<phi>"
    | "simplify (Conjunction (\<phi>#\<phi>s)) = (simplify \<phi> \<and>\<^sub>f simplify (Conjunction \<phi>s))"
    | "simplify \<phi> = \<phi>"

fun cnf_form_or :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infixl "\<or>\<^sub>c\<^sub>f" 41) where 
  "(Conjunction \<phi>s \<or>\<^sub>c\<^sub>f Conjunction \<psi>s) = Conjunction [\<phi> \<or>\<^sub>f \<psi> . \<phi> \<leftarrow> \<phi>s, \<psi> \<leftarrow> \<psi>s]"
| "(\<phi> \<or>\<^sub>c\<^sub>f \<psi>) = (\<phi> \<or>\<^sub>f \<psi>)"

lemma map_form_and: "map_formula f (\<phi> \<and>\<^sub>f \<psi>) = (map_formula f \<phi> \<and>\<^sub>f map_formula f \<psi>)"
  by (cases "(\<phi>,\<psi>)" rule:form_and.cases, auto)

lemma map_form_or: "map_formula f (\<phi> \<or>\<^sub>f \<psi>) = (map_formula f \<phi> \<or>\<^sub>f map_formula f \<psi>)"
  by (cases "(\<phi>,\<psi>)" rule:form_or.cases, auto)

lemma map_form_not: "map_formula f (\<not>\<^sub>f \<phi>) = (\<not>\<^sub>f map_formula f \<phi>)"
  by (induct \<phi>, auto)

text \<open>The internal constructs are less useful.\<close>

declare form_and.simps[simp del] form_or.simps[simp del]

abbreviation form_imp (infixr "\<longrightarrow>\<^sub>f" 40) where "(\<phi> \<longrightarrow>\<^sub>f \<psi>) \<equiv> \<not>\<^sub>f \<phi> \<or>\<^sub>f \<psi>"

fun form_all
where "form_all [] = True\<^sub>f"
    | "form_all (\<phi>#\<phi>s) = (\<phi> \<and>\<^sub>f form_all \<phi>s)"

fun form_ex
where "form_ex [] = False\<^sub>f"
    | "form_ex (\<phi>#\<phi>s) = (\<phi> \<or>\<^sub>f form_ex \<phi>s)"

fun form_cnf_ex
where "form_cnf_ex [] = Conjunction [False\<^sub>f]"
    | "form_cnf_ex (\<phi>#\<phi>s) = (\<phi> \<or>\<^sub>c\<^sub>f form_cnf_ex \<phi>s)"

fun flatten where
  "flatten (Conjunction \<phi>s) = form_all (map flatten \<phi>s)"
| "flatten (Disjunction \<phi>s) = form_cnf_ex (map flatten \<phi>s)"
| "flatten \<phi> = Conjunction [Disjunction [\<phi>]]"
  
fun conjuncts where "conjuncts (Conjunction \<phi>s) = \<phi>s" | "conjuncts \<phi> = [\<phi>]"

fun disjuncts where "disjuncts (Disjunction \<phi>s) = \<phi>s" | "disjuncts \<phi> = [\<phi>]"

fun triv_unsat :: "'a formula \<Rightarrow> bool"
where "triv_unsat (Conjunction \<phi>s) = (\<forall>\<phi> \<in> set \<phi>s. triv_unsat \<phi>)"
    | "triv_unsat _ = False"




locale formula =
  fixes atom :: "'atom \<Rightarrow> bool"
    and assignment :: "'assignment \<Rightarrow> bool"
    and eval_true :: "'assignment \<Rightarrow> 'atom \<Rightarrow> bool"
begin

abbreviation "Assignments \<equiv> Collect assignment"

subsection \<open>Well-formedness\<close>

fun formula :: "'atom formula \<Rightarrow> bool" where
  "formula (Atom a) = atom a"
| "formula (NegAtom a) = atom a"
| "formula (Conjunction \<phi>s) = (\<forall>\<phi> \<in> set \<phi>s. formula \<phi>)"
| "formula (Disjunction \<phi>s) = (\<forall>\<phi> \<in> set \<phi>s. formula \<phi>)"
 
lemma formula_and[simp]: "formula (\<phi> \<and>\<^sub>f \<psi>) \<longleftrightarrow> formula \<phi> \<and> formula \<psi>"
  by (cases "(\<phi>,\<psi>)" rule: form_and.cases, auto simp: form_and.simps)

lemma formula_or[simp]: "formula (\<phi> \<or>\<^sub>f \<psi>) \<longleftrightarrow> formula \<phi> \<and> formula \<psi>"
  by (cases "(\<phi>,\<psi>)" rule: form_or.cases, auto simp: form_or.simps)

lemma formula_not[simp]: "formula (\<not>\<^sub>f \<phi>) \<longleftrightarrow> formula \<phi>" by (induct \<phi>; auto)

lemma formula_all[simp]: "formula (form_all \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. formula \<phi>)"
  by (induct \<phi>s, auto)

lemma formula_ex[simp]: "formula (form_ex \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. formula \<phi>)"
  by (induct \<phi>s, auto)

lemma formula_cnf_or[simp]: "formula \<phi> \<Longrightarrow> formula \<psi> \<Longrightarrow> formula (\<phi> \<or>\<^sub>c\<^sub>f \<psi>)"
  by (cases \<phi>; cases \<psi>, auto)

lemma formula_cnf_ex[simp]: "(\<forall>\<phi> \<in> set \<phi>s. formula \<phi>) \<Longrightarrow> formula (form_cnf_ex \<phi>s)"
  by (induct \<phi>s, auto)

lemma formula_flatten[simp]: "formula \<phi> \<Longrightarrow> formula (flatten \<phi>)"
  by (induct \<phi> rule: flatten.induct, auto simp: Let_def)

lemma formula_simplify[simp]: "formula (simplify \<phi>) \<longleftrightarrow> formula \<phi>"
  by (induct \<phi> rule: simplify.induct, auto)

lemma isLit_negate[simp]: "isLit (\<not>\<^sub>f f) = isLit f" by (cases f, auto)

lemma is_conj_lits_negate[simp]: "is_conj_lits (\<not>\<^sub>f f) = is_clause f"
  by (cases f, auto simp: is_clause.simps is_conj_lits.simps)

lemma is_cnf_form_and[simp]: "is_cnf f \<Longrightarrow> is_cnf g \<Longrightarrow> is_cnf (f \<and>\<^sub>f g)"
  by (cases "(f,g)" rule: form_and.cases; auto simp: is_cnf.simps form_and.simps)

lemma is_clause_form_or[simp]: "is_clause f \<Longrightarrow> is_clause g \<Longrightarrow> is_clause (f \<or>\<^sub>f g)"
  by (cases "(f,g)" rule: form_or.cases; auto simp: is_clause.simps form_or.simps)

lemma is_cnf_cnf_form_or[simp]: "is_cnf f \<Longrightarrow> is_cnf g \<Longrightarrow> is_cnf (f \<or>\<^sub>c\<^sub>f g)"
  by (cases f; cases g; auto simp: is_cnf.simps form_and.simps)

lemma is_cnf_form_True[simp]: "is_cnf True\<^sub>f"
  by (simp add: is_cnf.simps)

lemma is_cnf_form_all[simp]: "(\<And> f. f \<in> set fs \<Longrightarrow> is_cnf f) \<Longrightarrow> is_cnf (form_all fs)"
  by(induct fs, auto)

lemma is_cnf_form_cnf_ex[simp]: "(\<And> f. f \<in> set fs \<Longrightarrow> is_cnf f) \<Longrightarrow> is_cnf (form_cnf_ex fs)"
  by(induct fs, auto, auto simp: is_cnf.simps is_clause.simps)

lemma is_cnf_Conjunction[simp]: "is_cnf (Conjunction fs) = (\<forall> f \<in> set fs. is_clause f)"
  by (auto simp: is_cnf.simps)

lemma is_clause_Disjunction[simp]: "is_clause (Disjunction fs) = (\<forall> f \<in> set fs. isLit f)"
  by (auto simp: is_clause.simps)

lemma is_cnf_flatten[simp]:
  "is_cnf (flatten (\<phi> :: ('f,'v,'t) exp formula))"
  by (induct \<phi> rule: flatten.induct, auto intro!: is_cnf_form_all is_cnf_form_cnf_ex)


subsection \<open>Valuation\<close>

context fixes \<alpha> :: "'assignment" begin

  fun satisfies :: "'atom formula \<Rightarrow> bool" where
    "satisfies (Atom a) \<longleftrightarrow> eval_true \<alpha> a"
  | "satisfies (NegAtom a) \<longleftrightarrow> \<not> eval_true \<alpha> a"
  | "satisfies (Conjunction \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. satisfies \<phi>)"
  | "satisfies (Disjunction \<phi>s) \<longleftrightarrow> (\<exists>\<phi> \<in> set \<phi>s. satisfies \<phi>)"

  lemma satisfiesI[intro]:
    "eval_true \<alpha> a \<Longrightarrow> satisfies (Atom a)"
    "\<not> eval_true \<alpha> a \<Longrightarrow> satisfies (NegAtom a)"
    "(\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> satisfies \<phi>) \<Longrightarrow> satisfies (Conjunction \<phi>s)"
    "\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> satisfies \<phi> \<Longrightarrow> satisfies (Disjunction \<phi>s)" by auto

  lemma form_True[simp]: "satisfies True\<^sub>f" by auto

  lemma satisfies_NegAtom[simp]: "satisfies (NegAtom a) \<longleftrightarrow> \<not> satisfies (Atom a)" by simp

  lemma satisfies_and[simp]: "satisfies (\<phi> \<and>\<^sub>f \<psi>) \<longleftrightarrow> satisfies \<phi> \<and> satisfies \<psi>"
    by (cases "(\<phi>,\<psi>)" rule:form_and.cases, auto simp: form_and.simps)

  lemma satisfies_or[simp]: "satisfies (\<phi> \<or>\<^sub>f \<psi>) \<longleftrightarrow> satisfies \<phi> \<or> satisfies \<psi>"
    by (cases "(\<phi>,\<psi>)" rule:form_or.cases, auto simp: form_or.simps)

  lemma satisfies_not[simp]: "satisfies (\<not>\<^sub>f \<phi>) \<longleftrightarrow> \<not> satisfies \<phi>"
    by (induct \<phi>, auto)

  lemma satisfies_all[simp]:
    "satisfies (form_all \<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set \<phi>s. satisfies \<phi>)" by (induct \<phi>s, auto)

  lemma satisfies_ex[simp]:
    "satisfies (form_ex \<phi>s) \<longleftrightarrow> (\<exists>\<phi> \<in> set \<phi>s. satisfies \<phi>)" by (induct \<phi>s, auto)
end

notation satisfies (infix "\<Turnstile>" 40)


subsection \<open>Language\<close>

definition Language where "Language \<phi> = {\<alpha> \<in> Assignments. \<alpha> \<Turnstile> \<phi>}"
notation Language ("\<L>") (* this allows the notation available in sublocales *)

lemma Language_dom [dest]: assumes "\<alpha> \<in> \<L> \<phi>" shows "assignment \<alpha>"
  using assms by (auto simp: Language_def)

lemma Language_simps[simp]:
  "\<L> False\<^sub>f = {}"
  "\<L> True\<^sub>f = Assignments"
  "\<L> (\<phi> \<and>\<^sub>f \<psi>) = \<L> \<phi> \<inter> \<L> \<psi>"
  "\<L> (\<phi> \<or>\<^sub>f \<psi>) = \<L> \<phi> \<union> \<L> \<psi>"
  "\<L> (NegAtom a) = Assignments - \<L> (Atom a)"
  "\<L> (Conjunction (\<phi>#\<phi>s)) = \<L> \<phi> \<inter> \<L> (Conjunction \<phi>s)"
  "\<L> (Disjunction (\<phi>#\<phi>s)) = \<L> \<phi> \<union> \<L> (Disjunction \<phi>s)" by (auto simp: Language_def)

lemma Language_Conjunction[simp]: "\<L> (Conjunction \<phi>s) = Assignments \<inter> (\<Inter>\<phi> \<in> set \<phi>s. \<L> \<phi>)" by (induct \<phi>s, auto)

lemma Language_Disjunction[simp]: "\<L> (Disjunction \<phi>s) = (\<Union>\<phi> \<in> set \<phi>s. \<L> \<phi>)" by (induct \<phi>s, auto)

lemma Language_not[simp]: "\<L> (\<not>\<^sub>f \<phi>) = Assignments - \<L> \<phi>" by (induct \<phi>, auto)

lemma Language_all[simp]: "\<L> (form_all \<phi>s) = Assignments \<inter> (\<Inter>\<phi> \<in> set \<phi>s. \<L> \<phi>)" by (induct \<phi>s, auto)

lemma Language_ex[simp]: "\<L> (form_ex \<phi>s) = (\<Union>\<phi> \<in> set \<phi>s. \<L> \<phi>)" by (induct \<phi>s, auto)

lemma all_conjuncts[simplified,simp]: "\<L> (form_all (conjuncts \<phi>)) = \<L> \<phi>" by (cases \<phi>, auto)
lemma formula_conjuncts[simplified,simp]: "(\<forall>\<phi>' \<in> set (conjuncts \<phi>). formula \<phi>') = formula \<phi>" by (cases \<phi>, auto)

lemma ex_disjuncts[simplified,simp]: "\<L> (form_ex (disjuncts \<phi>)) = \<L> \<phi>" by (cases \<phi>, auto) 
lemma formula_disjuncts[simplified,simp]: "(\<forall>\<phi>' \<in> set (disjuncts \<phi>). formula \<phi>') = formula \<phi>" by (cases \<phi>, auto)

lemma Language_cnf_form_or[simp]: "\<L> (\<phi> \<or>\<^sub>c\<^sub>f \<psi>) = \<L> \<phi> \<union> \<L> \<psi>"
  by (cases \<phi>; cases \<psi>, auto)

lemma Language_cnf_ex[simp]: "\<L> (form_cnf_ex \<phi>s) = (\<Union>\<phi> \<in> set \<phi>s. \<L> \<phi>)" by (induct \<phi>s, auto)

lemma Langage_flatten[simp]: "\<L> (flatten \<phi>) = \<L> \<phi>"
  by (induct \<phi> rule: flatten.induct, auto simp: Let_def)

lemma Language_simplify[simp]: "\<L> (simplify \<phi>) = \<L> \<phi>"
  by (induct \<phi> rule: simplify.induct, auto)

lemma satisfies_Language: assumes "assignment \<alpha>" shows "\<alpha> \<Turnstile> \<phi> \<longleftrightarrow> \<alpha> \<in> \<L> \<phi>"
  using assms by (auto simp: Language_def)

definition implies :: "'atom formula \<Rightarrow> 'atom formula \<Rightarrow> bool" where
  "implies \<phi> \<psi> \<equiv> \<forall>\<alpha>. assignment \<alpha> \<longrightarrow> \<alpha> \<Turnstile> \<phi> \<longrightarrow> \<alpha> \<Turnstile> \<psi>"

notation implies (infix "\<Longrightarrow>\<^sub>f" 41)

lemma impliesI[intro]:
  assumes "\<And> \<alpha>. assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi> \<Longrightarrow> \<alpha> \<Turnstile> \<psi>"
  shows "\<phi> \<Longrightarrow>\<^sub>f \<psi>" using assms by (auto simp: implies_def)

lemma impliesD[dest]:
  assumes "\<phi> \<Longrightarrow>\<^sub>f \<psi>"
  shows "assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi> \<Longrightarrow> \<alpha> \<Turnstile> \<psi>"
  using assms by (auto simp: implies_def)

lemma impliesE[elim]:
  assumes "\<phi> \<Longrightarrow>\<^sub>f \<psi>" "(\<And>\<alpha>. assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi> \<Longrightarrow> \<alpha> \<Turnstile> \<psi>) \<Longrightarrow> P"
  shows P using assms by (auto simp: implies_def)

lemma implies_Language[simp]: "(\<phi> \<Longrightarrow>\<^sub>f \<psi>) \<longleftrightarrow> \<L> \<phi> \<subseteq> \<L> \<psi>"
  by (auto simp add: implies_def satisfies_Language)

definition equivalent where "equivalent \<phi> \<psi> \<equiv> \<phi> \<Longrightarrow>\<^sub>f \<psi> \<and> \<psi> \<Longrightarrow>\<^sub>f \<phi>"
notation equivalent (infix "\<Longleftrightarrow>\<^sub>f" 40)

lemma equivalentI[intro]: assumes "\<phi> \<Longrightarrow>\<^sub>f \<psi>" and "\<psi> \<Longrightarrow>\<^sub>f \<phi>" shows "\<phi> \<Longleftrightarrow>\<^sub>f \<psi>"
  using assms by (auto simp: equivalent_def)

lemma equivalentE[elim]: assumes "\<phi> \<Longleftrightarrow>\<^sub>f \<psi>" and "(\<phi> \<Longrightarrow>\<^sub>f \<psi>) \<Longrightarrow> (\<psi> \<Longrightarrow>\<^sub>f \<phi>) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: equivalent_def)

lemma equivalent_Language[simp]: "\<phi> \<Longleftrightarrow>\<^sub>f \<psi> \<longleftrightarrow> \<L> \<phi> = \<L> \<psi>" by auto

definition valid where
  "(valid \<phi>) = (\<forall> \<alpha>. assignment \<alpha> \<longrightarrow> \<alpha> \<Turnstile> \<phi>)"

notation valid ("\<Turnstile>\<^sub>f _" [40]40)

lemma validI[intro]:
  assumes "\<And> \<alpha>. assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi>"
  shows "\<Turnstile>\<^sub>f \<phi>" using assms by (auto simp: valid_def)

lemma validD[dest]:
  assumes "\<Turnstile>\<^sub>f \<phi>"
  shows "assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi>"
  using assms by (auto simp: valid_def)

lemma valid_Language:
  "\<Turnstile>\<^sub>f \<phi> \<longleftrightarrow> \<L> \<phi> = Assignments" by (auto simp: satisfies_Language)

lemma valid_simplify [simp]: "\<Turnstile>\<^sub>f simplify \<phi> \<longleftrightarrow> \<Turnstile>\<^sub>f \<phi>"
  by (simp add: valid_Language)

lemma valid_flatten [simp]: "\<Turnstile>\<^sub>f flatten \<phi> \<longleftrightarrow> \<Turnstile>\<^sub>f \<phi>"
  by (simp add: valid_Language)

lemma valid_implies_trans [trans]:
  assumes "\<Turnstile>\<^sub>f \<phi>" and "\<phi> \<Longrightarrow>\<^sub>f \<psi>" shows "\<Turnstile>\<^sub>f \<psi>"
  using assms by (auto simp: valid_Language)

lemma valid_equivalent_trans [trans]:
  assumes "\<Turnstile>\<^sub>f \<phi>" and "\<phi> \<Longleftrightarrow>\<^sub>f \<psi>" shows "\<Turnstile>\<^sub>f \<psi>"
  using assms by (auto simp: valid_Language)

lemma implies_trans [trans]:
  assumes "\<phi> \<Longrightarrow>\<^sub>f \<psi>" and "\<psi> \<Longrightarrow>\<^sub>f \<rho>" shows "\<phi> \<Longrightarrow>\<^sub>f \<rho>"
  using assms by auto

lemma implies_equivalent_trans [trans]:
  assumes "\<phi> \<Longrightarrow>\<^sub>f \<psi>" and "\<psi> \<Longleftrightarrow>\<^sub>f \<rho>" shows "\<phi> \<Longrightarrow>\<^sub>f \<rho>"
  using assms by auto

lemma equivalent_implies_trans [trans]:
  assumes "\<phi> \<Longleftrightarrow>\<^sub>f \<psi>" and "\<psi> \<Longrightarrow>\<^sub>f \<rho>" shows "\<phi> \<Longrightarrow>\<^sub>f \<rho>"
  using assms by (auto dest: implies_trans)

end

locale showsl_formula =
  fixes showsl_atom :: "'a \<Rightarrow> showsl"
begin
fun showsl_formula :: "'a formula \<Rightarrow> showsl" where
  "showsl_formula (Atom a) = showsl_atom a"
| "showsl_formula (NegAtom a) = showsl (STR ''! ('') o showsl_atom a o showsl (STR '')'')"
| "showsl_formula (Conjunction fs) = (let ss = map showsl_formula fs in
     showsl_list_gen id (STR ''True'') (STR ''Conj['') (STR '', '') (STR '']'') ss)" 
| "showsl_formula (Disjunction fs) = (let ss = map showsl_formula fs in
     showsl_list_gen id (STR ''False'') (STR ''Disj['') (STR '', '') (STR '']'') ss)" 
end


subsection \<open>Formulas over terms\<close>

fun vars_formula :: "('f,'v) term formula \<Rightarrow> 'v set"
where "vars_formula (Atom a) = vars_term a"
    | "vars_formula (NegAtom a) = vars_term a"
    | "vars_formula (Conjunction \<phi>s) = (\<Union>(vars_formula ` set \<phi>s))"
    | "vars_formula (Disjunction \<phi>s) = (\<Union>(vars_formula ` set \<phi>s))"

fun vars_formula_list :: "('f,'v) term formula \<Rightarrow> 'v list"
where "vars_formula_list (Atom a) = vars_term_list a"
    | "vars_formula_list (NegAtom a) = vars_term_list a"
    | "vars_formula_list (Conjunction \<phi>s) = concat (map vars_formula_list \<phi>s)"
    | "vars_formula_list (Disjunction \<phi>s) = concat (map vars_formula_list \<phi>s)"

fun in_vars_formula :: "'v \<Rightarrow> ('f,'v) term formula \<Rightarrow> bool"
where "in_vars_formula x (Atom a) = (x \<in> set (vars_term_list a))"
    | "in_vars_formula x (NegAtom a) = (x \<in> set (vars_term_list a))"
    | "in_vars_formula x (Conjunction \<phi>s) = (\<exists> \<phi> \<in> set \<phi>s. in_vars_formula x \<phi>)" 
    | "in_vars_formula x (Disjunction \<phi>s) = (\<exists> \<phi> \<in> set \<phi>s. in_vars_formula x \<phi>)" 

lemma in_vars_formula[code_unfold]: "(x \<in> vars_formula \<phi>) = in_vars_formula x \<phi>" 
  by (induct \<phi>, auto)

lemma vars_formula_list: "vars_formula \<phi> = set (vars_formula_list \<phi>)"
  by (induct \<phi>, auto)

lemma vars_formula_set_formula: "vars_formula \<phi> = \<Union> (vars_term ` set_formula \<phi>)"
  by (induct \<phi>, auto)

abbreviation rename_vars_formula :: "('v \<Rightarrow> 'w) \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> ('f,'w,'t) exp formula"
where "rename_vars_formula r cls \<equiv> map_formula (rename_vars r) cls"

adhoc_overloading rename_vars \<rightleftharpoons> rename_vars_formula

lemma rename_vars_formula_comp[simp]:
  "rename_vars f (rename_vars g (\<phi>::('f,'v,'t) exp formula)) = rename_vars (f \<circ> g) \<phi>"
   by (cases \<phi>, auto simp: formula.map_comp o_def)


locale prelogic =
  pre_sorted_algebra where type_fixer = type_fixer
  for type_fixer :: "('f\<times>'t\<times>'d) itself"
  and Bool_types :: "'t set"
  and to_bool :: "'d \<Rightarrow> bool"
begin

  definition "is_bool e \<equiv> (\<exists>b \<in> Bool_types. e :\<^sub>f b)"

  lemma is_bool_simps[simp]: "is_bool (Var x) = (snd x \<in> Bool_types)"
   "is_bool (Fun f es) = (\<exists>b \<in> Bool_types. Fun f es :\<^sub>f b)" by (auto simp: is_bool_def)

  abbreviation "BOOL_EXP \<equiv> Collect is_bool"

  sublocale formula is_bool assignment "\<lambda>\<alpha> t. to_bool (\<lbrakk>t\<rbrakk>\<alpha>)".

  lemma Language_atom[simp]: "\<L> (Atom e) = { \<alpha> \<in> Assignments. to_bool (\<lbrakk>e\<rbrakk>\<alpha>) }" by (auto simp: Language_def)

  lemma is_bool_imp_expression[simp]: "is_bool e \<Longrightarrow> expression e" unfolding is_bool_def by auto

  lemma formula_rename_vars[simp]: "formula (rename_vars r e) = formula e"
  proof (induct e)
    case (Atom x)
    then show ?case by (cases x, auto)
  next
    case (NegAtom x)
    then show ?case by (cases x, auto)
  qed auto

  lemma formula_rename_vars_map[simp]:
    "list_all formula (map (rename_vars r) l) = list_all formula l"
    using formula_rename_vars unfolding list_all_def by auto

  lemma eval_with_fresh_var[simp]: "xx \<notin> vars_term e \<Longrightarrow> \<lbrakk>e\<rbrakk> (\<alpha>(xx:=a)) = \<lbrakk>e\<rbrakk> \<alpha>" by auto

  lemma satisfies_with_fresh_var[simp]:
    assumes fv: "xx \<notin> vars_formula \<phi>"
    shows "\<alpha>(xx:=a) \<Turnstile> \<phi> \<longleftrightarrow> \<alpha> \<Turnstile> \<phi>" by (insert fv, induct \<phi>, auto)

  lemma satisfies_rename_vars:
    assumes r: "\<And> x t. \<alpha> (x,t) = \<beta> (r x, t)"
    shows "\<beta> \<Turnstile> (rename_vars r \<phi>) \<longleftrightarrow> \<alpha> \<Turnstile> \<phi>"
    by (induct \<phi>, auto simp: eval_rename_vars[of \<alpha>, OF r])

  definition satisfiable where "satisfiable \<phi> = (\<exists> \<alpha>. assignment \<alpha> \<and> \<alpha> \<Turnstile> \<phi>)" 

end

fun ground_formula where
  "ground_formula (Atom a) = ground a" 
| "ground_formula (NegAtom a) = ground a" 
| "ground_formula (Disjunction fs) = (\<forall> f \<in> set fs. ground_formula f)" 
| "ground_formula (Conjunction fs) = (\<forall> f \<in> set fs. ground_formula f)" 

locale logic = prelogic + sorted_algebra


subsection \<open>Checking validity\<close>

type_synonym ('s,'f,'v,'t) logic_checker =
  "'s \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> showsl check"

definition trivial_checker where
  "trivial_checker lits = (case partition is_Atom lits of
     (as, nas) \<Rightarrow> let pos = map get_Atom as; neg = map get_Atom nas
    in (\<exists> a \<in> set pos. a \<in> set neg))"

definition trivial_clause_checker where "trivial_clause_checker f = (case f of Disjunction lits \<Rightarrow> trivial_checker lits)" 

lemma trivial_checker:
  assumes "\<And> l. l \<in> set lits \<Longrightarrow> isLit l" and "trivial_checker lits"
  shows "\<exists> a. Atom a \<in> set lits \<and> NegAtom a \<in> set lits"
proof -
  obtain as nas where part: "partition is_Atom lits = (as,nas)" by force
  from assms[unfolded trivial_checker_def part split, simplified]
  obtain a where a: "a \<in> set as" "get_Atom a \<in> get_Atom ` set nas" by auto
  from partition_filter_conv[of is_Atom lits, unfolded part]
  have id: "as = filter is_Atom lits" "nas = filter (\<lambda> x. \<not> is_Atom x) lits" by (auto simp: o_def)
  from a(1)[unfolded id] have "is_Atom a" and mem: "a \<in> set lits" by auto
  then obtain aa where aa: "a = Atom aa" by (cases a, auto)
  from a(2)[unfolded aa] obtain na where na: "get_Atom na = aa" "na \<in> set nas" by auto
  from na(2)[unfolded id] assms(1) have "\<not> is_Atom na" "isLit na" "na \<in> set lits" by auto
  with na have "NegAtom aa \<in> set lits" by (cases na, auto)
  with mem aa show ?thesis by auto
qed

fun get_disjunctions where
  "get_disjunctions (Disjunction phis) = concat (map get_disjunctions phis)" 
| "get_disjunctions x = [x]"

fun get_conjunctions where
  "get_conjunctions (Conjunction phis) = concat (map get_conjunctions phis)" 
| "get_conjunctions x = [x]"

definition check_trivial_implication where
  "check_trivial_implication \<phi> \<psi> = 
      (\<forall> phi \<in> set (get_disjunctions \<phi>). let c_phis = get_conjunctions phi in  
       \<exists> psi \<in> set (get_disjunctions \<psi>). \<forall> c_psi \<in> set (get_conjunctions psi). c_psi \<in> set c_phis)" 

fun trivial_formula where
  "trivial_formula (Disjunction \<phi>s) = list_ex trivial_formula \<phi>s"
| "trivial_formula (Conjunction \<phi>s) = list_all trivial_formula \<phi>s"
| "trivial_formula _ = False"

context prelogic
begin

lemma get_disjunctions: "(\<alpha> \<Turnstile> form_ex (get_disjunctions \<phi>)) = (\<alpha> \<Turnstile> \<phi>)"
  by (induct \<phi>, auto)

lemma get_conjunctions: "(\<alpha> \<Turnstile> form_all (get_conjunctions \<phi>)) = (\<alpha> \<Turnstile> \<phi>)"
  by (induct \<phi>, auto)

lemma check_trivial_implication:
  assumes "check_trivial_implication \<phi> \<psi>" shows "\<phi> \<Longrightarrow>\<^sub>f \<psi>"
proof
  fix \<alpha>
  assume "\<alpha> \<Turnstile> \<phi>" 
  then have "\<alpha> \<Turnstile> form_ex (get_disjunctions \<phi>)" unfolding get_disjunctions .
  then obtain phi where phi: "phi \<in> set (get_disjunctions \<phi>)" and sat: "\<alpha> \<Turnstile> phi" by auto
  from assms[unfolded check_trivial_implication_def Let_def, rule_format, OF phi]
  obtain psi where psi: "psi \<in> set (get_disjunctions \<psi>)"
    and conj: "\<And> c_psi. c_psi\<in>set (get_conjunctions psi) \<Longrightarrow> c_psi \<in> set (get_conjunctions phi)" by auto
  {
    fix c_psi
    assume "c_psi \<in> set (get_conjunctions psi)" 
    then have mem: "c_psi \<in> set (get_conjunctions phi)" using conj by auto
    from sat[folded get_conjunctions[of _ phi]] mem have "\<alpha> \<Turnstile> c_psi" by auto
  }
  then have "\<alpha> \<Turnstile> psi" using get_conjunctions[of _ psi] by auto
  then show "\<alpha> \<Turnstile> \<psi>" using psi get_disjunctions[of _ \<psi>] by auto
qed

lemma trivial_formula:
  assumes "trivial_formula \<phi>" shows "\<Turnstile>\<^sub>f \<phi>"
  by (insert assms, induct \<phi>, auto simp: list_all_iff list_ex_iff valid_Language)

lemma trivial_clause_checker:
  assumes "is_clause \<phi>" and "trivial_clause_checker \<phi>" shows "\<Turnstile>\<^sub>f \<phi>"
proof -
  from assms obtain lits where phi: "\<phi> = Disjunction lits" and lits: "\<And> l. l \<in> set lits \<Longrightarrow> isLit l"
    using is_clause.cases by blast
  from assms[unfolded trivial_clause_checker_def phi] have triv: "trivial_checker lits" by auto
  from trivial_checker[OF lits this] obtain a where a: "Atom a \<in> set lits" "NegAtom a \<in> set lits" by auto
  from split_list[OF a(1)] obtain l1 l2 where lits: "lits = l1 @ Atom a # l2" by auto
  from a(2) lits have "NegAtom a \<in> set (l1 @ l2)" by auto
  from split_list[OF this] obtain l3 l4 where l12: "l1 @ l2 = l3 @ NegAtom a # l4" by auto
  have "set lits = insert (Atom a) (set (l1 @ l2))" unfolding lits by auto
  also have "\<dots> = insert (Atom a) (insert (NegAtom a) (set l3 \<union> set l4))" unfolding l12 by auto
  finally show ?thesis unfolding phi by auto
qed

end


locale pre_logic_checker =
  prelogic where type_fixer = "TYPE('f\<times>'t\<times>'d)" +
  showsl_formula showsl_atom
  for type_fixer :: "('f \<times> 'v :: showl \<times> 't \<times> 'd \<times> 's :: {default,showl}) itself"
  and showsl_atom :: "('f,'v,'t) exp \<Rightarrow> showsl"
  and logic_checker :: "('s,'f,'v,'t) logic_checker"
  and normalize_lit :: "bool \<Rightarrow> ('f,'v,'t) exp \<Rightarrow> ('f,'v,'t) exp formula"
  and normalized_lit :: "bool \<Rightarrow> ('f,'v,'t) exp \<Rightarrow> bool"
begin

fun normalized_Lit where
  "normalized_Lit (Atom e) = normalized_lit True e" 
| "normalized_Lit (NegAtom e) = normalized_lit False e" 
| "normalized_Lit _ = False" 

definition is_normalized_clause where 
  "is_normalized_clause f = (case f of Disjunction ls \<Rightarrow> Ball (set ls) normalized_Lit
     | _ \<Rightarrow> False)" 

fun normalize_lits where
  "normalize_lits (Conjunction \<phi>s) = Conjunction (map normalize_lits \<phi>s)"
| "normalize_lits (Disjunction \<phi>s) = Disjunction (map normalize_lits \<phi>s)"
| "normalize_lits (NegAtom \<phi>) = normalize_lit False \<phi>"
| "normalize_lits (Atom \<phi>) = normalize_lit True \<phi>"

fun normalized_formula where
  "normalized_formula (Conjunction fs) = (\<forall> f \<in> set fs. normalized_formula f)"
| "normalized_formula (Disjunction fs) = (\<forall> f \<in> set fs. normalized_formula f)"
| "normalized_formula (Atom a) = normalized_lit True a"
| "normalized_formula (NegAtom a) = normalized_lit False a"

lemma normalized_formula_and: "normalized_formula f \<Longrightarrow> normalized_formula g \<Longrightarrow> normalized_formula (f \<and>\<^sub>f g)"
  by (induct f g rule: form_and.induct, auto simp: form_and.simps)

lemma normalized_formula_form_all: "(\<And> f. f \<in> set fs \<Longrightarrow> normalized_formula f) \<Longrightarrow> normalized_formula (form_all fs)"
  by (induct fs, auto simp: normalized_formula_and)

lemma normalized_formula_or: "normalized_formula f \<Longrightarrow> normalized_formula g \<Longrightarrow> normalized_formula (f \<or>\<^sub>f g)"
  by (induct f g rule: form_or.induct, auto simp: form_or.simps)

lemma normalized_formula_cnf_form_or: "normalized_formula f \<Longrightarrow> normalized_formula g \<Longrightarrow> normalized_formula (f \<or>\<^sub>c\<^sub>f g)"
  by (induct f g rule: cnf_form_or.induct, auto intro: normalized_formula_or)

lemma normalized_formula_form_cnf_ex: "(\<And> f. f \<in> set fs \<Longrightarrow> normalized_formula f) \<Longrightarrow> normalized_formula (form_cnf_ex fs)"
  by (induct fs, auto simp: normalized_formula_cnf_form_or)

lemma normalized_formula_flatten: "normalized_formula f \<Longrightarrow> normalized_formula (flatten f)"
  by (induct f, auto intro!: normalized_formula_form_all normalized_formula_form_cnf_ex)


definition "check_valid_formula h \<phi> \<equiv>
  (case flatten \<phi> of Conjunction \<phi>s \<Rightarrow> check_allm (
     \<lambda> \<phi>. try (check (trivial_clause_checker \<phi>) (STR ''trivial clause checker failed'')) catch (\<lambda> _. 
       case flatten (normalize_lits \<phi>) of Conjunction \<phi>s \<Rightarrow> check_allm (logic_checker h) \<phi>s)) \<phi>s)
  <+? (\<lambda>s. showsl_lit (STR ''problem in checking validity of formula '') o showsl_formula \<phi> o showsl_nl o s)"

fun is_or_and_shape where
  "is_or_and_shape (Disjunction [\<phi>1,Conjunction [\<phi>2,\<phi>3]]) = True"
| "is_or_and_shape _ = False"

fun is_conj_shape where
  "is_conj_shape [hint1,hint2] (Conjunction [\<phi>1,\<phi>2]) = True"
| "is_conj_shape _ _ = False"

fun is_disj_shape where
  "is_disj_shape (hint1#hints) (Disjunction [Conjunction [\<phi>1,\<phi>2], Conjunction [\<phi>3,\<phi>4]]) = True"
| "is_disj_shape _ _ = False"

end

locale logic_checker =
  logic where type_fixer = "TYPE(_)" + pre_logic_checker +
  assumes logic_checker:
    "\<And>h \<phi>. isOK(logic_checker h \<phi>) \<Longrightarrow> formula \<phi> \<Longrightarrow> is_normalized_clause \<phi> \<Longrightarrow> \<Turnstile>\<^sub>f \<phi>"
    and normalize_lit_normalizes: "is_bool e \<Longrightarrow> formula (normalize_lit b e) \<and> normalized_formula (normalize_lit b e)"
    and normalized_lit_equivalent: "is_bool e \<Longrightarrow> assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> normalize_lit b e \<longleftrightarrow> (if b then id else Not) (\<alpha> \<Turnstile> Atom e)"
begin

lemma normalized_formula_normalize_lits: "formula f \<Longrightarrow> normalized_formula (normalize_lits f)"
  by (induct f, insert normalize_lit_normalizes, auto)

lemma formula_normalize_lits: "formula f \<Longrightarrow> formula (normalize_lits f)"
  by (induct f, insert normalize_lit_normalizes, auto)

lemma Language_normalize_lits: "formula f \<Longrightarrow> \<L> (normalize_lits f) = \<L> f"
  by (induct f, auto, insert normalized_lit_equivalent, auto simp:  Language_def)

lemma check_valid_formula:
  assumes ok: "isOK(check_valid_formula h \<phi>)" and \<phi>: "formula \<phi>"
  shows "\<Turnstile>\<^sub>f \<phi>"
proof-
  from \<phi> have form: "formula (flatten \<phi>)" by auto
  from is_cnf_flatten[of \<phi>] have "is_cnf (flatten \<phi>)" .
  then obtain \<phi>s where *: "flatten \<phi> = Conjunction \<phi>s" "\<And> \<phi>\<^sub>i. \<phi>\<^sub>i \<in> set \<phi>s \<Longrightarrow> is_clause \<phi>\<^sub>i" by (cases, auto)
  from form have form: "\<And>\<psi>. \<psi> \<in> set \<phi>s \<Longrightarrow> formula \<psi>" by (auto simp: *)
  {
    fix \<psi>
    assume **: "\<psi> \<in> set \<phi>s" 
    note form = form[OF **]
    note clause = *(2)[OF **]
    let ?\<psi> = "normalize_lits \<psi>" 
    from is_cnf_flatten[of ?\<psi>] have "is_cnf (flatten ?\<psi>)" .
    then obtain \<chi>s where 1: "flatten ?\<psi> = Conjunction \<chi>s" "\<And> \<phi>\<^sub>i. \<phi>\<^sub>i \<in> set \<chi>s \<Longrightarrow> is_clause \<phi>\<^sub>i" by (cases, auto)
    from formula_normalize_lits[OF form] have form': "\<And>\<psi>. \<psi> \<in> set \<chi>s \<Longrightarrow> formula \<psi>" 
      using 1 formula_flatten by force
    from ok[unfolded check_valid_formula_def *, simplified, rule_format, OF **, unfolded 1, simplified]
    consider (Triv) "trivial_clause_checker \<psi>" | (lc) "\<forall>x\<in>set \<chi>s. isOK (logic_checker h x)" by auto
    then have "\<Turnstile>\<^sub>f \<psi>" 
    proof (cases)
      case lc
      {
        fix \<chi>
        assume chi: "\<chi> \<in> set \<chi>s" 
        with lc have ok: "isOK(logic_checker h \<chi>)" by auto
        from 1(2)[OF chi] have "is_clause \<chi>" .
        moreover have "normalized_formula \<chi>" 
          using normalized_formula_flatten[OF normalized_formula_normalize_lits[OF form], unfolded 1] chi by auto
        ultimately
        have "is_normalized_clause \<chi>" unfolding is_normalized_clause_def
        proof (induct \<chi>, auto, goal_cases)
          case (1 fs f)
          then show ?case by (cases f, force+)
        qed
        from logic_checker[OF ok form'[OF chi] this] 
        have "\<Turnstile>\<^sub>f \<chi>" .
      } 
      then have "\<Turnstile>\<^sub>f flatten ?\<psi>" unfolding 1 by (simp add: valid_def)
      also have "\<dots> \<Longleftrightarrow>\<^sub>f \<psi>" by (simp add: Language_normalize_lits form)
      finally show ?thesis by simp
    next
      case Triv
      from trivial_clause_checker[OF clause this] show ?thesis . 
    qed
  }
  then have "\<Turnstile>\<^sub>f form_all \<phi>s" by (auto simp: valid_Language)
  also have "... \<Longleftrightarrow>\<^sub>f flatten \<phi>" by (auto simp add: *)
  finally show ?thesis by simp
qed

end

type_synonym ('f,'v,'t) definability_checker = "'v \<Rightarrow> 't \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> showsl check"

locale pre_definability_checker =
  prelogic where type_fixer = "TYPE('f\<times>'t\<times>'d)"
  for type_fixer :: "('f\<times>'v\<times>'t\<times>'d) itself"
  and definability_checker :: "('f,'v,'t) definability_checker"

locale definability_checker = pre_definability_checker +
  assumes definability_checker:
    "\<And>x ty \<phi>. isOK (definability_checker x ty \<phi>) \<Longrightarrow> assignment \<alpha> \<Longrightarrow> \<exists>a \<in> Values_of_type ty. \<alpha>((x,ty):=a) \<Turnstile> \<phi>"

lemmas [code] =
  prelogic.is_bool_def
  pre_sorted_algebra.has_type.simps
  formula.formula.simps
  showsl_formula.showsl_formula.simps
  pre_logic_checker.check_valid_formula_def
  pre_logic_checker.normalize_lits.simps
  pre_logic_checker.is_or_and_shape.simps
  pre_logic_checker.is_disj_shape.simps
  pre_logic_checker.is_conj_shape.simps

end
