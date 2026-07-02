(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Equational_Reasoning_Impl
  imports
    Equational_Reasoning
    Completion
    First_Order_Rewriting.Trs_Impl
    Check_Joins
begin

definition "showsl_eqs \<equiv> showsl_trs' showsl showsl (STR ''equational system:'') (STR '' = '')"
definition "showsl_eq \<equiv> showsl_rule' showsl showsl (STR '' = '')"
definition showsl_ln :: "nat \<Rightarrow> showsl" where
  "showsl_ln i \<equiv> showsl_nl \<circ> showsl i \<circ> showsl_lit (STR '': '')"

function
  eq_proof_lines :: "('f:: showl, 'v:: showl) eq_proof \<Rightarrow> nat \<Rightarrow> (showsl \<times> nat \<times> ('f, 'v) rule)"
and eq_proofs_lines :: "('f:: showl, 'v:: showl) eq_proof list \<Rightarrow> nat \<Rightarrow> (showsl \<times> nat list \<times> ('f, 'v) term list \<times> ('f, 'v) term list)"
where
  "eq_proof_lines (Refl s) i = (showsl_ln (Suc i) \<circ> showsl_eq (s, s) \<circ> showsl_lit (STR '' [refl]''), Suc i, s, s)"
| "eq_proof_lines (Sym p) i = (
    let (s, i', l, r) = eq_proof_lines p i in
    (s \<circ> showsl_ln (Suc i') \<circ> showsl_eq (r, l) \<circ> showsl_lit (STR '' [sym '') \<circ> showsl i' \<circ> showsl_lit (STR '']''), Suc i', r, l))"
| "eq_proof_lines (Trans p1 p2) i = (
    let (s1, i1, s, t) = eq_proof_lines p1 i in
    let (s2, i2, u, v) = eq_proof_lines p2 i1 in
    (s1 \<circ> s2 \<circ>
      showsl_ln (Suc i2) \<circ> showsl_eq (s, v) \<circ> showsl_lit (STR '' [trans '') \<circ> showsl i1 \<circ> showsl_lit (STR '', '') \<circ> showsl i2 \<circ> showsl_lit (STR '']''), Suc i2, s, v))"
| "eq_proof_lines (Assm (l, r) \<sigma>) i = (
    let eq = (l \<cdot> \<sigma>, r \<cdot> \<sigma>) in
    (showsl_ln (Suc i) \<circ> showsl_eq eq \<circ> showsl_lit (STR '' [assm '') \<circ> showsl_eq (l, r) \<circ> showsl_lit (STR '']''), Suc i, eq))"
| "eq_proof_lines (Cong f ps) i = (
    let (s, is, ls, rs) = eq_proofs_lines ps i in
    let eq = (Fun f ls, Fun f rs) in
    let i' = last is in
    let is = butlast is in
    (s \<circ> showsl_ln (Suc i') \<circ> showsl_eq eq \<circ> showsl_list_gen showsl (STR '' [cong]'') (STR '' [cong '') (STR '', '') (STR '']'') is, Suc i', eq))"
| "eq_proofs_lines [] i = (id, [i], [], [])"
| "eq_proofs_lines (p#ps) i = (
    let (s1, i', l, r) = eq_proof_lines p i in
    let (s2, is, ls, rs) = eq_proofs_lines ps i' in
    (s1 \<circ> s2, i'#is, l#ls, r#rs))"
  by (pat_completeness) auto
termination by (lexicographic_order)

abbreviation showsl_eq_proof where "showsl_eq_proof p \<equiv> fst (eq_proof_lines p 0)"

type_synonym ('f, 'v) subsumption_proof = "(('f, 'v) equation \<times> ('f, 'v) term list) list"

fun
  check_subsumptions_guided :: "('f :: showl, 'v :: showl) equation list \<Rightarrow> ('f, 'v) subsumption_proof \<Rightarrow> showsl check"
where "check_subsumptions_guided E [] = succeed"
    | "check_subsumptions_guided E ((e, seq) # convs) = do {
         check_conversion_sequence E (fst e) (snd e) seq 
             <+? (\<lambda> s. showsl_lit (STR ''problem in conversion for equation '') \<circ> showsl_eq e \<circ> showsl_nl \<circ> s);
         check_subsumptions_guided (e # E) convs
       }"

lemma check_subsumptions_guided:
  assumes ok: "isOK (check_subsumptions_guided E convs)"
  shows "subsumes (set E) (fst ` set convs)"
    unfolding subsumes_via_rule_conversion
    using ok
proof (induct convs arbitrary: E)
  case Nil show ?case by simp
next
  case (Cons ec convs)
  obtain s t conv where ec: "ec = ((s,t),conv)" by (cases ec, force)
  note Cons = Cons[unfolded ec]
  from Cons(2) have rec: "isOK(check_subsumptions_guided ((s,t) # E) convs)" 
    and one: "isOK(check_conversion_sequence E s t conv)" by auto
  from check_conversion_sequence[OF one] have one: "(s,t) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*" .
  {
    fix l r
    assume "(l,r) \<in> fst ` set convs"
    with Cons(1)[OF rec] have "(l,r) \<in> (rstep (set ((s,t) # E)))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    then have "(l,r) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
    proof (induct)
      case (step r u)
      from step(2) have "(r,u) \<in> (rstep {(s,t)})\<^sup>\<leftrightarrow> \<or> (r,u) \<in> (rstep (set E))\<^sup>\<leftrightarrow>"
        unfolding estep_sym_closure_conv using rstep_union[of "{(s,t)}^<->" "(set E)^<->"]
        by auto
      then have "(r,u) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
      proof
        assume step: "(r,u) \<in> (rstep {(s,t)})\<^sup>\<leftrightarrow>"
        have "subsumes (set E) {(s,t)}"
          unfolding subsumes_via_rule_conversion using one by auto
        then show ?thesis unfolding subsumes_def eq_theory_is_esteps
          using step unfolding conversion_def by auto
      qed auto
      with step(3) show ?case by auto
    qed auto
  }
  then show ?case unfolding ec using one by force
qed

definition check_subsumption_guided :: "('f :: showl, 'v :: showl) equation list \<Rightarrow> ('f,'v)equation list \<Rightarrow> ('f, 'v) subsumption_proof \<Rightarrow> showsl check"
where  "check_subsumption_guided E E' convs \<equiv> do {
    check_subseteq E (map fst convs)
      <+? (\<lambda>r. showsl_lit (STR ''could not find conversion for equation '') \<circ> showsl_eq r);
    check_subsumptions_guided E' convs
  }"

lemma check_subsumption_guided:
  assumes ok: "isOK (check_subsumption_guided E E' convs)"
  shows "subsumes (set E') (set E)"
proof -
  note ok = ok[unfolded check_subsumption_guided_def]
  from ok have subset: "set E \<subseteq> fst ` set convs" and
    ok: "isOK (check_subsumptions_guided E' convs)" by auto
  from check_subsumptions_guided[OF ok] subset 
  show ?thesis  
    unfolding subsumes_via_rule_conversion by blast
qed

definition check_single_subsumption :: "('f :: showl, 'v :: showl) equation \<Rightarrow> ('f,'v)equation list \<Rightarrow> ('f, 'v) subsumption_proof \<Rightarrow> showsl check"
where  "check_single_subsumption eq E convs \<equiv> do {
    check (eq \<in> set (map fst convs)) (showsl_lit (STR ''could not find conversion for equation '') \<circ> showsl_eq eq);
    check_subsumptions_guided E convs
  }"

lemma check_single_subsumption:
  assumes ok: "isOK (check_single_subsumption eq E convs)"
  shows "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  note ok = ok[unfolded check_single_subsumption_def]
  from ok have mem: "eq \<in> fst ` set convs" and
    ok: "isOK (check_subsumptions_guided E convs)" by auto
  from check_subsumptions_guided[OF ok] mem
  show ?thesis  
    unfolding subsumes_via_rule_conversion by force
qed

definition check_convertible_instance :: "('f :: showl, 'v :: showl) equation \<Rightarrow> ('f,'v)equation list \<Rightarrow> ('f, 'v) subsumption_proof \<Rightarrow> showsl check"
where  "check_convertible_instance eq E convs \<equiv> do {
    check_exm (\<lambda>c. check (instance_rule (fst c) eq) (showsl_lit (STR ''not an instance of '') \<circ> showsl_eq eq)) convs (\<lambda>_. showsl_lit (STR '' no instance found''));
    check_subsumptions_guided E convs
  }"

lemma check_convertible_instance:
  assumes ok: "isOK (check_convertible_instance (s,t) E convs)"
  shows "\<exists>\<sigma>. (s\<cdot>\<sigma>, t\<cdot>\<sigma>) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  note ok = ok[unfolded check_convertible_instance_def]
  from ok obtain c where inst: "fst c \<in> fst ` set convs" "instance_rule (fst c) (s,t)"
    and ok: "isOK (check_subsumptions_guided E convs)" by fastforce
  obtain u v where uv:"fst c = (u,v)" by fastforce
  from inst obtain \<sigma> where \<sigma>: "u = s \<cdot> \<sigma> \<and> v = t \<cdot> \<sigma>" unfolding uv instance_rule_def by auto
  note sub = check_subsumptions_guided[OF ok, unfolded subsumes_via_rule_conversion, rule_format, of "fst c"]
  with \<sigma> inst(1) show ?thesis unfolding uv by force
qed

lemma check_join_NF_conversion: 
  assumes ok: "isOK (check_join_NF R s t)"
  shows "(s,t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule set_mp[OF join_imp_conversion check_join_NF_sound[OF ok]])

definition
  check_subsumption_NF :: "('f:: showl, 'v:: showl) equation list \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_subsumption_NF E R \<equiv>  do {
    check_allm (\<lambda> e. check_join_NF R (fst e) (snd e)
      <+? (\<lambda>s. showsl_lit (STR ''could not join equation '') \<circ> showsl_eq e \<circ> showsl_nl \<circ> s)) E
  }"

lemma check_subsumption_NF:
  assumes ok: "isOK (check_subsumption_NF E R)"
  shows "subsumes (set R) (set E)"
proof -
  note ok = ok[unfolded check_subsumption_NF_def, simplified]
  show ?thesis
    unfolding subsumes_via_rule_conversion
  proof (clarify)
    fix s t
    assume "(s,t) \<in> set E"
    with ok have "isOK (check_join_NF R s t)" by auto
    from check_join_NF_conversion[OF this]
    show "(s, t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" .
  qed
qed

definition
  check_subsumption :: "('f:: showl, 'v:: showl) equation list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) subsumption_proof option \<Rightarrow> showsl check"
where
  "check_subsumption E R convs_o \<equiv>
  (case convs_o of
    None \<Rightarrow> check_subsumption_NF E R
  | Some convs \<Rightarrow> check_subsumption_guided E R convs)"

lemma check_subsumption:
  assumes ok: "isOK (check_subsumption E R convs_o)"
  shows "subsumes (set R) (set E)"
proof -
  note ok = ok[unfolded check_subsumption_def]
  show ?thesis
  proof (cases convs_o)
    case None
    show ?thesis 
      by (rule check_subsumption_NF, insert None ok, auto)
  next
    case (Some convs)
    show ?thesis 
      by (rule check_subsumption_guided, insert Some ok, auto)
  qed
qed

end
