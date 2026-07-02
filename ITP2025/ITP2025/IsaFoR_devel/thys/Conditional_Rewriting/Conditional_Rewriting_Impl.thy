(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012, 2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Conditional_Rewriting_Impl
imports
  Conditional_Rewriting
  TRS.Trs_Impl_More
begin

(*TODO: move*)
lemma check_eq_Inr [termination_simp]: "check b e = Inr y \<longleftrightarrow> b"
by (cases b) (auto simp: check_def)

type_synonym ('f, 'v) crules = "('f, 'v) crule list"

definition "showsl_eq = showsl_rule' showsl showsl (STR '' ->* '')"

definition "showsl_conditions = showsl_sep showsl_eq (showsl_lit (STR '', ''))"

definition "showsl_crule cr = showsl_rule (fst cr) \<circ>
    (if snd cr = [] then id else 
     showsl_lit (STR '' | '') \<circ> showsl_conditions (snd cr))"

definition "showsl_crules ctrs = showsl_list_gen showsl_crule (STR '''') (STR '''') (STR ''\<newline>'') (STR '''') ctrs \<circ> showsl_nl"

definition "showsl_ctrs R = showsl_lit (STR ''CTRS:\<newline>\<newline>'') \<circ> showsl_crules R"

definition "showsl_coverlap \<rho>\<^sub>1 \<rho>\<^sub>2 p =
  showsl_lit (STR ''overlap of conditional rules '') \<circ> showsl_crule \<rho>\<^sub>1 \<circ> showsl_lit (STR '' and '') \<circ> showsl_crule \<rho>\<^sub>2 \<circ>
  showsl_lit (STR '' at position '') \<circ> showsl_pos p"

definition check_type3 :: "('f :: showl, 'v :: showl) crules \<Rightarrow> showsl check"
where
  "check_type3 R = do {
    check_allm (\<lambda>cr. check_subseteq (vars_term_list (snd (fst cr))) (vars_term_list (fst (fst cr)) @ vars_trs_list (snd cr))
     <+? (\<lambda>x. showsl_lit (STR ''variable '') \<circ> showsl x
            \<circ> showsl_lit (STR '' occurs only in right-hand side of rule '') \<circ> showsl_crule cr \<circ> showsl_nl)) R
  } <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not of type 3\<newline>'') \<circ> e)"

lemma check_type3 [simp]:
  "isOK (check_type3 R) = type3 (set R)"
  unfolding check_type3_def type3_def by force

definition X_impl :: "('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list"
 where "X_impl cr i = 
  concat (vars_term_list (fst (fst cr)) # (map (vars_term_list \<circ> snd) (take i (snd cr)) ))"

lemma X_impl [simp]:
  "set (X_impl cr i) = X_vars cr i" 
unfolding X_impl_def X_vars_def by force

definition Y_impl :: "('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list"
 where "Y_impl cr i = 
  vars_term_list (snd (fst cr)) @ vars_term_list (snd ((snd cr) ! i)) @ (vars_trs_list (drop (Suc i) (snd cr)))"

lemma Y_impl: 
 "set (Y_impl cr i) = Y_vars cr i" 
 unfolding Y_impl_def Y_vars_def by force

definition check_dctrs :: "('f :: showl, 'v :: showl) crules \<Rightarrow> showsl check"
where
  "check_dctrs R = do {
    check_allm 
     (\<lambda>cr.
      check_allm
       (\<lambda>i.
        check_subseteq (vars_term_list (fst (snd cr ! i))) (X_impl cr i)
         <+? (\<lambda>x. showsl_lit (STR ''variable '') \<circ> showsl x \<circ> showsl_lit (STR '' in condition '')
                \<circ> showsl_rule (snd cr ! i) \<circ> showsl_lit (STR '' of rule '') 
                \<circ> showsl_crule cr \<circ> showsl_lit (STR ''violates DCTRS condition\<newline>''))
       ) [0..<length (snd cr)]
     ) R 
  } <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not deterministic\<newline>'') \<circ> e)"

lemma check_dctrs [simp]:
  "isOK (check_dctrs R) = dctrs (set R)"
by (auto simp add: check_dctrs_def dctrs_def atLeast0LessThan)

definition check_wf_ctrs :: "('f :: showl, 'v :: showl) crules \<Rightarrow> showsl check"
where
  "check_wf_ctrs R = do {
    check_varcond_no_Var_lhs (map fst R);
    check_dctrs R;
    check_type3 R
  } <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not well-formed\<newline>'') \<circ> e)"

lemma check_wf_ctrs [simp]:
  "isOK (check_wf_ctrs R) = wf_ctrs (set R)"
by (force simp: check_wf_ctrs_def wf_ctrs_def)

definition funs_crule_list :: "('f, 'v) crule \<Rightarrow> 'f list"
where
  "funs_crule_list r = add_funs_rule (fst r) (funs_trs_list (snd r))"

lemma funs_crule_list_sound [simp]:
  "set (funs_crule_list r) = funs_crule r"
  by (simp add: funs_crule_list_def funs_crule_def)

definition funs_ctrs_list :: "('f, 'v) crule list \<Rightarrow> 'f list"
where
  "funs_ctrs_list trs = concat (map funs_crule_list trs)"

lemma funs_ctrs_list_sound [simp]:
  "set (funs_ctrs_list r) = funs_ctrs (set r)"
  by (simp add: funs_ctrs_list_def funs_ctrs_def)

abbreviation "terms_of_crule \<rho> \<equiv> (clhs \<rho> # crhs \<rho> # terms_of_rules (snd \<rho>))"

definition "match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 = do {
  ts \<leftarrow> zip_option (terms_of_crule \<rho>\<^sub>2) (terms_of_crule \<rho>\<^sub>1);
  match_list Var ts
}"

abbreviation "term_of_crule \<rho> \<equiv> Fun (SOME f. True) (clhs \<rho> # crhs \<rho> # terms_of_rules (snd \<rho>))"

lemma match_crule_alt_def:
  "match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 = match (term_of_crule \<rho>\<^sub>1) (term_of_crule \<rho>\<^sub>2)"
by (cases "zip_option (terms_of_crule \<rho>\<^sub>1) (terms_of_crule \<rho>\<^sub>2)")
   (auto simp: match_crule_def match_def match_list_def decompose_def split: option.splits)

definition check_properly_oriented :: "('f :: showl, 'v :: showl) crules \<Rightarrow> showsl check"
where
  "check_properly_oriented R =
    check_dctrs (filter (\<lambda>((l, r), cs). \<not> vars_term r \<subseteq> vars_term l) R)
    <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not properly oriented\<newline>'') \<circ> e)"

lemma check_properly_oriented [simp]:
  "isOK (check_properly_oriented R) = properly_oriented (set R)"
by (simp add: check_properly_oriented_def properly_oriented_def X_vars_def dctrs_def) (fastforce)

definition check_extended_properly_oriented :: "('f :: showl, 'v ::showl) crules \<Rightarrow> showsl check"
where
  "check_extended_properly_oriented R =
    check (extended_properly_oriented (set R))
      (showsl_lit (STR ''the given CTRS is not extended properly oriented\<newline>''))"

lemma check_extended_properly_oriented [simp]:
  "isOK (check_extended_properly_oriented R) = extended_properly_oriented (set R)"
by (simp add: check_extended_properly_oriented_def)

definition check_Ru_NF :: 
  "('f :: {compare_order,showl}, 'v :: showl) term \<Rightarrow> ('f, 'v) crules \<Rightarrow> showsl check"
where
  "check_Ru_NF s R = check
    (is_NF_trs (map fst R) s)
    (showsl_lit (STR ''the term '') \<circ> showsl s \<circ> showsl_lit (STR '' is not an Ru normal form\<newline>''))"

lemma check_Ru_NF [simp]:
  "isOK (check_Ru_NF s R) \<longleftrightarrow> s \<in> NF (rstep (Ru (set R)))"
by (simp add: check_Ru_NF_def Ru_def)

definition check_constructor_term ::
  "('f :: showl, 'v :: showl) term \<Rightarrow> ('f, 'v) crules \<Rightarrow> showsl check"
where
  "check_constructor_term s R = check
    (funas_term s \<subseteq> funas_ctrs (set R) - set (defined_list (map fst R)))
    (showsl_lit (STR ''the term '') \<circ> showsl s \<circ> showsl_lit (STR '' is not a constructor term\<newline>''))"

lemma check_constructor_term [simp]:
  "isOK (check_constructor_term s R) =
    (funas_term s \<subseteq> funas_ctrs (set R) - { f. defined (Ru (set R)) f })"
by (simp add: check_constructor_term_def Ru_def)

definition check_right_stable :: "('f :: {compare_order,showl}, 'v :: showl) crules \<Rightarrow> showsl check"
where
  "check_right_stable R = check_allm (\<lambda>r.
    check_allm (\<lambda>i. do {
      let t\<^sub>i = snd (snd r ! i);
      check_disjoint
        (vars_term_list (fst (fst r)) @
        (concat (map (\<lambda>(s, t). vars_term_list s) (take (Suc i) (snd r)))) @
        (concat (map (\<lambda>(s, t). vars_term_list t) (take i (snd r)))))
        (vars_term_list t\<^sub>i)
      <+? (\<lambda>x. showsl_lit (STR ''variable '') \<circ> showsl x \<circ> showsl_lit (STR '' in rhs of condition '') \<circ>
               showsl i \<circ> showsl_lit (STR '' is not fresh\<newline>''));
      choice [(check_linear_term t\<^sub>i \<then> check_constructor_term t\<^sub>i R),
        (check_ground_term t\<^sub>i \<then> check_Ru_NF t\<^sub>i R)] <+? showsl_sep id showsl_nl
    }
    ) [0..< length (snd r)]
  ) R
  <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not right stable\<newline>'') \<circ> e)"

lemma check_right_stable [simp]:
  "isOK (check_right_stable R) = right_stable (set R)"
unfolding check_right_stable_def
using [[simproc del: list_to_set_comprehension]]
by (simp add: right_stable_def Let_def atLeast0LessThan case_prod_beta) (blast)

datatype ('f, 'v) cstep_proof =
  Cstep_step "('f, 'v) crule" pos "('f, 'v) subst"
    (cstep_src : "('f, 'v) term")
    (cstep_trg : "('f, 'v) term")
    "('f, 'v) cstep_proof list list"

lemma [termination_simp]:
  "i < length xs \<Longrightarrow> size_list size (xs ! i) < size_list (size_list size) xs"
proof (induct xs arbitrary: i)
  case (Cons x xs)
  then show ?case by (cases i) (auto simp add: less_Suc_eq trans_less_add2)
qed simp

definition
  "check_crule_variants r r' = do {
    let rs = fst r # conds r;
    let rs' = fst r' # conds r';
    check (match_rules rs rs' \<noteq> None \<and> match_rules rs' rs \<noteq> None)
      (showsl_crule r \<circ> showsl_lit (STR '' and '') \<circ> showsl_crule r' 
       \<circ> showsl_lit (STR '' are not variants of each other\<newline>''))
  }"

lemma check_crule_variants [elim!]:
  assumes "isOK (check_crule_variants r r')"
  obtains p where "p \<bullet> r = r'"
using assms
by (cases r rule: crule_cases; cases r' rule: crule_cases)
   (auto simp: check_crule_variants_def eqvt dest: match_rules_imp_variants)

definition
  "check_variant_in_ctrs R r =
    check_exm (check_crule_variants r) R (showsl_sep id id)
    <+? (\<lambda>_. showsl_lit (STR ''rule '') \<circ> showsl_crule r \<circ> showsl_lit (STR '' is not a variant of any rule in:\<newline>'') \<circ>
             showsl_ctrs R)"

lemma check_variant_in_ctrs:
  assumes "isOK (check_variant_in_ctrs R r)"
  obtains p where "p \<bullet> r \<in> set R"
  using assms
  by (cases r rule: crule_cases) (force simp: check_variant_in_ctrs_def eqvt)

fun check_cstep and check_csteps
where
  "check_cstep R (Cstep_step ((l, r), cs) p \<sigma> s t pss) = do {
    check_variant_in_ctrs R ((l, r), cs);
    check (length pss = length cs) (showsl_lit (STR ''mismatch between number of conditions and number of rewrite sequences''));
    check (s = replace_at s p (l \<cdot> \<sigma>)) (showsl s \<circ> showsl_lit (STR '' does not contain an instance of '') \<circ> showsl l);
    check (t = replace_at s p (r \<cdot> \<sigma>)) (showsl t \<circ> showsl_lit (STR '' does not contain an instance of '') \<circ> showsl r);
    check_allm (\<lambda>i. check_csteps R (fst (cs ! i) \<cdot> \<sigma>) (snd (cs ! i) \<cdot> \<sigma>) (pss ! i)) [0..<length cs]
  }"
| "check_csteps R s t [] = check (s = t)
    (showsl_lit (STR ''empty rewrite sequence but source '') \<circ> showsl s \<circ> showsl_lit (STR '' and target '')
      \<circ> showsl t \<circ> showsl_lit (STR '' differ''))"
| "check_csteps R s t [p] = do {
    check (cstep_src p = s) (showsl (cstep_src p) \<circ> showsl_lit (STR '' does not match the source '') \<circ> showsl s);
    check (cstep_trg p = t) (showsl (cstep_trg p) \<circ> showsl_lit (STR '' does not match the target '') \<circ> showsl t);
    check_cstep R p
  }"
| "check_csteps R s t (p # ps) = do {
    check (cstep_src p = s) (showsl (cstep_src p) \<circ> showsl_lit (STR '' does not match the source '') \<circ> showsl s);
    check_cstep R p;
    check_csteps R (cstep_trg p) t ps
  }"

lemma
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) crule list"
  shows check_cstep: "isOK (check_cstep R p) \<Longrightarrow> (cstep_src p, cstep_trg p) \<in> cstep (set R)"
    and check_csteps: "isOK (check_csteps R s t ps) \<Longrightarrow> (s, t) \<in> (cstep (set R))\<^sup>*"
proof (induct R p and R s t ps rule: check_cstep_check_csteps.induct)
  case (1 R l r cs p \<sigma> s t pss)
  from 1 obtain \<pi> where *: "\<pi> \<bullet> ((l, r), cs) \<in> set R" by (auto elim: check_variant_in_ctrs)
  from 1 have "x < length cs \<Longrightarrow>
          (fst (cs ! x) \<cdot> \<sigma>, snd (cs ! x) \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*" for x
    by (auto simp: check_eq_Inr)
  then have **: "(a, b) \<in> set cs \<Longrightarrow> (a \<cdot> \<sigma>, b \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*" for a b
    by (metis fst_conv in_set_idx snd_conv)
  from 1 show ?case using *
    apply (auto simp: check_eq_Inr)
    apply (intro cstepI [of "\<pi> \<bullet> l" "\<pi> \<bullet> r" "\<pi> \<bullet> cs" "set R" "sop (-\<pi>) \<circ>\<^sub>s \<sigma>" s "ctxt_of_pos_term p s"])
    by (auto simp: ** eqvt)
qed (auto simp: check_eq_Inr)

lemma check_cstep_eq_Inr:
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) crule list"
  shows "check_cstep R p = Inr () \<Longrightarrow> (cstep_src p, cstep_trg p) \<in> cstep (set R)"
using check_cstep [of R p] by (auto elim!: check_variant_in_ctrs)

lemma check_csteps':
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) crule list"
  shows "isOK (check_csteps R s t ps) \<Longrightarrow>
    (if ps = [] then s = t else s = cstep_src (ps ! 0) \<and> t = cstep_trg (last ps)) \<and>
    (\<forall>i<length ps. (cstep_src (ps ! i), cstep_trg (ps ! i)) \<in> cstep (set R) \<and>
      (i < length ps - 1 \<longrightarrow> cstep_trg (ps ! i) = cstep_src (ps ! Suc i)))"
apply (induct R s t ps arbitrary: rule: check_cstep_check_csteps.induct(2))
apply simp
apply (auto simp: isOK_def check_eq_Inr check_cstep_eq_Inr check_csteps split: if_splits sum.splits)
apply (metis check_cstep_eq_Inr less_Suc0 less_antisym nth_Cons_0 nth_Cons_Suc)
apply (metis (mono_tags, lifting) One_nat_def Suc_pred check_cstep_eq_Inr less_Suc0 not_less_eq nth_Cons')
apply (case_tac i)
apply auto
done

lemma conds_sat_rel_perm:
  fixes cs :: "('f, 'v::infinite) rules" and \<pi> :: "'v perm"
  assumes "\<forall>\<sigma>. (\<forall>(u, v) \<in> set (\<pi> \<bullet> cs). (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*) \<longrightarrow> (\<pi> \<bullet> s \<cdot> \<sigma>, \<pi> \<bullet> t \<cdot> \<sigma>) \<in> S"
  shows "\<forall>\<sigma>. (\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*) \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S"
proof (intro allI impI)
  fix \<sigma>
  assume "\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  with assms [THEN spec, of "sop (-\<pi>) \<circ>\<^sub>s \<sigma>"]
    have "(\<pi> \<bullet> s \<cdot> (sop (-\<pi>) \<circ>\<^sub>s \<sigma>), \<pi> \<bullet> t \<cdot> (sop (-\<pi>) \<circ>\<^sub>s \<sigma>)) \<in> S" by (force simp: eqvt)
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S" by auto
qed

 
definition check_feasibility where 
  "check_feasibility R cs (\<sigma> :: (_,'v :: {infinite,showl})subst) prfs = do {
     check (length cs = length prfs) (showsl_lit (STR ''# conditions != # rewrite sequences''));
     check_allm (\<lambda> ((s,t),p). check_csteps R (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) p) (zip cs prfs);
     return ()
   }" 

lemma check_feasibility: assumes ok: "isOK(check_feasibility R cs \<sigma> prfs)" 
  shows "conds_sat (set R) cs \<sigma>" 
  unfolding conds_sat_iff
proof (intro ballI, clarify)
  note ok = ok[unfolded check_feasibility_def, simplified]
  fix s t
  assume "(s,t) \<in> set cs" 
  then obtain p where "((s,t),p) \<in> set (zip cs prfs)" 
    using ok by (meson in_set_impl_in_set_zip1)
  with ok have "isOK(check_csteps R (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) p)" by auto
  from check_csteps[OF this]
  show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*" .
qed 
  

end
