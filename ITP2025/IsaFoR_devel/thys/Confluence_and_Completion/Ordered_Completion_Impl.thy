(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2016 - 2019)
License: LGPL (see file COPYING.LESSER)
*)
theory Ordered_Completion_Impl
  imports
    Ordered_Completion
    TRS.Trs_Impl_More
    TRS.Q_Restricted_Rewriting_Impl
    Ord.KBO_More
    Ord.KBO_Impl
    Ord.Reduction_Order_Impl
    Ord.RPO_More
    Equational_Reasoning_Impl
    Vickrey_Clarke_Groves.Partitions
    Certification_Monads.Strict_Sum
    Auxx.Multiset2
    Weighted_Path_Order.Relations
    TRS.More_Abstract_Rewriting
begin

(* NOTE: there are many predicates called less, but these are actually gt (>)! *)

hide_const (open) Ramsey.choice
hide_const (open) Strict_Sum.error
hide_const (open) Strict_Sum.return
hide_const (open) Strict_Sum.bind

datatype ('f, 'v) oc_irule =
  OC_Deduce "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"
  | OC_Orientl "('f, 'v) term" "('f, 'v) term"
  | OC_Orientr "('f, 'v) term" "('f, 'v) term"
  | OC_Delete "('f, 'v) term"
  | OC_Compose "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"
  | OC_Simplifyl "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"
  | OC_Simplifyr "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"
  | OC_Collapse "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"

definition "sym_list xs = List.union xs (map (\<lambda>(x, y). (y, x)) xs)"

lemma set_sym_list [simp]: "set (sym_list xs) = (set xs)\<^sup>\<leftrightarrow>" by (auto simp: sym_list_def)

definition check_rstep_p
  where
    "check_rstep_p c \<rho> p s t =
      (if p \<notin> set (poss_list t) then error (showsl (STR ''no step possible at this position''))
       else
         let (l, r) = \<rho> in
         (case match_list Var [(l, s |_ p), (r, t |_ p)] of
              None \<Rightarrow> error (showsl (STR ''rule does not match''))
            | Some \<sigma> \<Rightarrow>
              if t = replace_at s p (r \<cdot> \<sigma>) then c (l \<cdot> \<sigma>) (r \<cdot> \<sigma>)
              else error (showsl (STR ''result does not match''))))"

definition check_step_rule
  where
    "check_step_rule c \<rho> s t =
      check_exm (\<lambda>p. check_rstep_p c \<rho> p s t) (poss_list s)
        (\<lambda>_. (showsl_lit (STR '' is not a reduct with respect to '') \<circ> showsl (fst \<rho>) \<circ> (showsl_lit (STR '' -> '')) \<circ> showsl (snd \<rho>)))"

lemma check_step_rule:
  assumes ok: "isOK (check_step_rule chk (l,r) s t)" 
  shows "\<exists>C \<sigma> p. s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> isOK (chk (l \<cdot> \<sigma>) (r \<cdot> \<sigma>))"
proof -
  from ok[unfolded check_step_rule_def case_prod_beta isOK_update_error isOK_existsM]
    obtain p where ok_p:"isOK (check_rstep_p chk (l,r) p s t)" "p \<in> poss s" by auto
  let ?p = "\<lambda> \<sigma>.(if t = replace_at s p (r \<cdot> \<sigma>) then chk (l \<cdot> \<sigma>) (r \<cdot> \<sigma>)
                 else (error undefined))"
  let ?ml = "match_list Var [(l, s |_ p), (r, t |_ p)]"
  from ok_p[unfolded check_rstep_p_def] obtain \<sigma> where \<sigma>:"?ml = Some \<sigma>" "isOK(?p \<sigma>)" 
    by (cases ?ml, auto)
  from match_list_sound[OF \<sigma>(1)] have at_p:"l \<cdot> \<sigma> = s |_ p" "r \<cdot> \<sigma> = t |_ p" by auto
  from \<sigma>(2) have rlcheck:"isOK(chk (l \<cdot> \<sigma>) (r \<cdot> \<sigma>))" and t:"t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>"
    unfolding split by auto
  let ?C = "ctxt_of_pos_term p s"
  from at_p ctxt_supt_id[OF ok_p(2)] t have s:"s = ?C\<langle>l \<cdot> \<sigma>\<rangle>"  and t:"t = ?C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from s t rlcheck show ?thesis by force
qed

fun check_step
  where
    "check_step c [] s t =
      error (showsl_lit (STR ''no step from '') \<circ> showsl s \<circ> showsl_lit (STR '' to '') \<circ> showsl t \<circ> showsl_lit (STR '' found\<newline>''))"
  | "check_step c (e # E) s t =
      choice [check_step_rule c e s t, check_step c E s t] <+? showsl_sep id showsl_nl"

declare check_step.simps[code]

lemma check_step:
  assumes ok: "isOK (check_step chk es s t)"
  shows "\<exists> C \<sigma> p l r. (l,r) \<in> set es \<and> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> isOK (chk (l \<cdot> \<sigma>) (r \<cdot> \<sigma>))"
  using assms
proof (induct es)
  case (Cons e es)
  then obtain l r where e:"e = (l,r)" by force
  note mono = ordstep_mono[OF _ subset_refl, of _ "set (e # es)"]
  from Cons show ?case proof(cases "isOK(check_step_rule chk (l,r) s t)")
    case True
    with e check_step_rule [OF this] mono [of "set [e]"] show ?thesis by auto
  next
    case False
    with Cons(2)[unfolded check_step.simps] e have "isOK (check_step chk es s t)" by auto
    with Cons(1) mono show ?thesis by auto
  qed
qed simp

abbreviation "check_rstep \<equiv> check_step (\<lambda> _ _. succeed)"

lemma check_rstep [dest!]:
  assumes "isOK (check_rstep R s t)" 
  shows "(s, t) \<in> rstep (set R)"
  using rstepI and check_step [OF assms] by auto

definition "find_variant_in_trs r R =
  firstM (check_variants_rule r) R <+? (showsl_sep id showsl_nl)"

lemma find_variant_in_trs_return [elim!]:
  assumes "find_variant_in_trs r R = return r'"
  obtains p where "r' \<in> set R" and "r' = p \<bullet> r"
  using assms by (auto simp: find_variant_in_trs_def dest!: firstM_return)

lemma check_first_variant_trs [elim!]:
  assumes "isOK (find_variant_in_trs r R)"
  obtains r' where "find_variant_in_trs r R = return r'"
  using assms by auto

locale oc_ops =
  fixes check_ord :: "('f::showl, 'v::showl) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
begin

abbreviation "check_ordstep \<equiv> check_step check_ord"

abbreviation "check_mem_eq eq E \<equiv>
  check (eq \<in> set E) (showsl eq \<circ> showsl_lit (STR '' is not an available equation''))"

abbreviation "check_mem_rl \<rho> R \<equiv>
  check (\<rho> \<in> set R) ( showsl_rule \<rho> \<circ> showsl_lit (STR '' is not an available rule''))"

abbreviation "check_oriented \<equiv> check_allm (\<lambda>(l, r). check_ord l r)"

fun check_step
  where
    "check_step (E, R) (OC_Deduce s t u) = do {
      let S = R @ sym_list E;
      check_rstep S s t <+? (\<lambda>str. showsl_lit (STR '' no step from '') \<circ> showsl s \<circ> showsl_lit (STR '' to '') \<circ> showsl t \<circ> showsl_nl \<circ> str);
      check_rstep S s u <+? (\<lambda>str. showsl_lit (STR '' no step from '') \<circ> showsl s \<circ> showsl_lit (STR '' to '') \<circ> showsl u \<circ> showsl_nl \<circ> str);
      return ((t, u) # E, R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in deduce step '') \<circ> showsl t \<circ> showsl_lit (STR '' <- '') \<circ> showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl u \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Orientl s t) = do {
      check_ord s t;
      st \<leftarrow> find_variant_in_trs (s, t) E;
      return (removeAll st E, (s, t) # R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in orientl step for '') \<circ> showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl t \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Orientr s t) = do {
      check_ord t s;
      st \<leftarrow> find_variant_in_trs (s, t) E;
      return (removeAll st E, (t, s) # R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in orientr step for '') \<circ> showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl t \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Delete s) = do {
      ss \<leftarrow> find_variant_in_trs (s, s) E;
      return (removeAll ss E, R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in delete step for '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl s \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Compose s t u) = do {
      st \<leftarrow> find_variant_in_trs (s, t) R;
      let R'' = removeAll st R;
      check_ordstep (R'' @ (sym_list E)) t u  <+? (\<lambda>str. showsl_lit (STR '' no ordstep from '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> showsl u \<circ> showsl_nl \<circ> str);
      return (E, (s, u) # R'')
    } <+? (\<lambda>str. showsl_lit (STR ''error in compose step from '') \<circ> showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> 
                                                         showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl u \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Simplifyl s t u) = do {
      st \<leftarrow> find_variant_in_trs (s, t) E;
      let E'' = removeAll st E;
      check_ordstep (R @ (sym_list E'')) s u  <+? (\<lambda>str. showsl_lit (STR '' no ordstep from '') \<circ> showsl s \<circ> showsl_lit (STR '' to '') \<circ> showsl u \<circ> showsl_nl \<circ> str);
      return ((u, t) # E'', R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in simplifyl step from '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> 
                                                           showsl u \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Simplifyr s t u) = do {
      st \<leftarrow> find_variant_in_trs (s, t) E;
      let E'' = removeAll st E;
      check_ordstep (R @ sym_list E'') t u  <+? (\<lambda>str. showsl_lit (STR '' no ordstep from '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> showsl u \<circ> showsl_nl \<circ> str);
      return ((s, u) # E'', R)
    } <+? (\<lambda>str. showsl_lit (STR ''error in simplifyr step from '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ>
                                                           showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl u \<circ> showsl_nl \<circ> str)"
  | "check_step (E, R) (OC_Collapse s t u) = do {
      ts \<leftarrow> find_variant_in_trs (t, s) R;
      let R'' = removeAll ts R;
      check_ordstep (R'' @ (sym_list E)) t u  <+? (\<lambda>str. showsl_lit (STR '' no ordstep from '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> showsl u \<circ> showsl_nl \<circ> str);
      return ((u, s) # E, R'')
    } <+? (\<lambda>str. showsl_lit (STR ''error in collapse step from '') \<circ> showsl s \<circ> showsl_lit (STR '' -> '') \<circ> showsl t \<circ> showsl_lit (STR '' to '') \<circ> 
                                                          showsl u \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_nl \<circ> str)"

fun check_oc
  where
    "check_oc (E, R) (E', R') [] = do {
      let err = (\<lambda>f x y. f x \<circ> showsl_lit (STR ''\<newline>is not a variant of\<newline>'') \<circ> f y);
      check_variants_trs E E' <+? (\<lambda>_. err showsl_eqs E E');
      check_variants_trs E' E <+? (\<lambda>_. err showsl_eqs E E');
      check_variants_trs R R' <+? (\<lambda>_. err showsl_trs R R');
      check_variants_trs R' R <+? (\<lambda>_. err showsl_trs R R')
    }"
  | "check_oc (E, R) (E', R') (x # xs) = do {
      (E'', R'') \<leftarrow> check_step (E, R) x;
      check_oc (E'', R'') (E', R') xs
    }"

end
lemmas [code] = oc_ops.check_step.simps
lemmas [code] = oc_ops.check_oc.simps
    
locale oc_spec =
  ordered_completion_inf less + (* TODO: s > t should read s is greater than t, not less than! *)
  oc_ops check_ord
  for less :: "('a:: showl, string) term \<Rightarrow> ('a, string) term \<Rightarrow> bool" (infix "\<succ>" 50)
    and check_ord :: "('a, string) term \<Rightarrow> ('a, string) term \<Rightarrow> showsl check" +
  assumes check_ord [simp]: "isOK (check_ord s t) \<longleftrightarrow> s \<succ> t"
begin

lemma check_ordstep:
  assumes "isOK (check_ordstep R s t)"
  shows "(s, t) \<in> ordstep {\<succ>} (set R)"
  using ordstep.intros [of _ _ "set R"] and check_step [OF assms] by auto

lemma check_ordstep_return [dest!]:
  assumes "check_ordstep R s t = return u"
  shows "(s, t) \<in> ordstep {\<succ>} (set R)"
  using assms and check_ordstep by auto
    
lemma check_oriented:
  "isOK (check_oriented rs) \<Longrightarrow> (set rs) \<subseteq> {\<succ>}"
  by auto

lemma check_step_return:
  assumes "check_step (E, R) step = return (E', R')" and "set R \<subseteq> {\<succ>}"
  shows "oKB' (set E, set R) (set E', set R')"
  using assms
proof -
  let ?R = "set R" and ?E = "set E"
  {fix s t RR EE \<pi>
    assume a:"(s, t) \<in> ordstep {\<succ>} (RR \<union> EE\<^sup>\<leftrightarrow>)" "RR \<subseteq> ?R"
    from ordstep_permute_litsim[OF a(1), of "RR \<union> EE\<^sup>\<leftrightarrow>"] have "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ordstep {\<succ>} (RR \<union> EE\<^sup>\<leftrightarrow>)" by auto
    with ostep_iff_ordstep assms(2) a(2) have "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ostep EE RR" by blast
  }
  note ostep = this
  show ?thesis proof(cases step)
    case (OC_Deduce s t u)
    note ok = assms[unfolded this check_step.simps Let_def]
    then have ids:"R' = R" "E' = (t, u) # E" by auto
    from ok have "isOK(check_rstep (R @ sym_list E) s t) \<and> isOK(check_rstep (R @ sym_list E) s u)" by (simp, force)
    with check_rstep have rsteps:"(s, t) \<in> rstep (?R \<union> ?E\<^sup>\<leftrightarrow>)" "(s, u) \<in> rstep (?R \<union> ?E\<^sup>\<leftrightarrow>)" by auto
    from oKB'.deduce[OF this, of 0] show ?thesis unfolding ids by auto
  next
    case (OC_Orientl s t)
    then show ?thesis
      using assms
      apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      assume a:"step = OC_Orientl s t" "s \<succ> t" "(\<pi> \<bullet> s,\<pi> \<bullet> t) \<in> ?E"
      with a(2) have "\<pi> \<bullet> s \<succ> \<pi> \<bullet> t" using less_set_permute by blast
      from oKB'.orientl[OF this a(3), of _ "-\<pi>"]
      show "oKB' (?E, ?R) (?E - {(\<pi> \<bullet> s,\<pi> \<bullet> t)}, insert (s,t) ?R)" by auto
    qed
  next
    case (OC_Orientr s t)
    then show ?thesis
      using assms
      apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      assume a:"step = OC_Orientr s t" "t \<succ> s" "(\<pi> \<bullet> s,\<pi> \<bullet> t) \<in> ?E"
      with a(2) have "\<pi> \<bullet> t \<succ> \<pi> \<bullet> s" using less_set_permute by blast
      from oKB'.orientr[OF this a(3), of _ "-\<pi>"]
      show "oKB' (?E, ?R) (?E - {(\<pi> \<bullet> s,\<pi> \<bullet> t)}, insert (t,s) ?R)" by auto
    qed
  next
    case (OC_Delete s)
    then show ?thesis using assms oKB'.delete by (auto simp: rule_pt.permute_prod.simps)
  next
    case (OC_Compose s t u)
    then show ?thesis using assms
      apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      let ?Rm = "?R - {(\<pi> \<bullet> s, \<pi> \<bullet> t)}"
      assume a:"(t, u) \<in> ordstep {\<succ>} (?Rm \<union> (set E')\<^sup>\<leftrightarrow>)" "(\<pi> \<bullet> s,\<pi> \<bullet> t) \<in> ?R"
      from ostep[OF a(1)] have "(\<pi> \<bullet> t, \<pi> \<bullet> u) \<in> ostep (set E') ?Rm" by blast
      from oKB'.compose[OF this a(2), of "-\<pi>"]
      show "oKB' (set E', ?R) (set E', insert (s, u) ?Rm)" by force
    qed
  next
    case (OC_Simplifyl s t u)
    then show ?thesis using assms
      apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      let ?Em = "?E - {(\<pi> \<bullet> s, \<pi> \<bullet> t)}"
      assume a:"(s, u) \<in> ordstep {\<succ>} (set R' \<union> ?Em\<^sup>\<leftrightarrow>)" "(\<pi> \<bullet> s,\<pi> \<bullet> t) \<in> ?E" "R = R'"
      from ostep[OF a(1)] a(3) have "(\<pi> \<bullet> s, \<pi> \<bullet> u) \<in> ostep ?Em ?R" by blast
      from oKB'.simplifyl[OF this a(2), of "-\<pi>"] a(3)
      show "oKB' (set E, set R') (insert (u, t) ?Em, set R')" by force
    qed
  next
    case (OC_Simplifyr s t u)
    then show ?thesis using assms
      apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      let ?Em = "?E - {(\<pi> \<bullet> s, \<pi> \<bullet> t)}"
      assume a:"(t, u) \<in> ordstep {\<succ>} (set R' \<union> ?Em\<^sup>\<leftrightarrow>)" "(\<pi> \<bullet> s,\<pi> \<bullet> t) \<in> ?E" "R = R'"
      from ostep[OF a(1)] a(3) have "(\<pi> \<bullet> t, \<pi> \<bullet> u) \<in> ostep ?Em ?R" by blast
      from oKB'.simplifyr[OF this a(2), of "-\<pi>"] a(3)
      show "oKB' (set E, set R') (insert (s, u) ?Em, set R')" by force
    qed
  next
    case (OC_Collapse s t u)
    then show ?thesis using assms apply (auto simp: Let_def rule_pt.permute_prod.simps elim!: bindE)
    proof -
      fix \<pi>
      let ?Rm = "?R - {(\<pi> \<bullet> t, \<pi> \<bullet> s)}"
      assume a:"(t, u) \<in> ordstep {\<succ>} (?Rm \<union> ?E\<^sup>\<leftrightarrow>)" "(\<pi> \<bullet> t,\<pi> \<bullet> s) \<in> ?R"
      from ostep[OF a(1)] have "(\<pi> \<bullet> t, \<pi> \<bullet> u) \<in> ostep ?E ?Rm" by blast
      from oKB'.collapse[OF this a(2), of "-\<pi>"]
      show "oKB' (set E, set R) (insert (u, s) ?E, ?Rm)" by force
    qed
  qed
qed


lemma oKB'_less:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
proof -
  have [dest]: "(x, y) \<in> R \<Longrightarrow> x \<succ> y" for x y using \<open>R \<subseteq> {\<succ>}\<close> by auto
  note assms(1)
  moreover
  { fix s t \<pi> assume "s \<succ> t"
    then have "\<pi> \<bullet> s \<succ> \<pi> \<bullet> t" using less_set_permute by auto }
  moreover
  { fix s t u \<pi> assume "(t, u) \<in> rstep (R - {(s, t)})" and "(s, t) \<in> R"
    then have "s \<succ> u" by (induct t u) (blast intro: subst ctxt dest: trans)
    then have "\<pi> \<bullet> s \<succ> \<pi> \<bullet> u" using less_set_permute by auto }
  moreover
  { fix s t u \<pi> assume "(t, u) \<in> ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)" and "(s, t) \<in> R"
    then have "s \<succ> u" by (cases) (auto dest: trans ctxt)
    then have "\<pi> \<bullet> s \<succ> \<pi> \<bullet> u" using less_set_permute by auto }
  ultimately show ?thesis by (cases, (fastforce simp: ostep_def)+)
qed

lemma oKB'_rtrancl_less:
  assumes "oKB'\<^sup>*\<^sup>* (E, R) (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
  using assms by (induct "(E, R)" "(E', R')" arbitrary: E' R') (auto dest!: oKB'_less)

lemma oKB_ER_permuted:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "E \<union> R \<subseteq> Id \<union> E' \<union> R' \<union> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow> \<union> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow> O (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>"
  using assms
proof -
  from ostep_imp_rstep_sym have orstep:"\<And>s t.(s, t) \<in> ostep E' R' \<Longrightarrow> (s, t) \<in> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>" by blast
  let ?step2 = "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow> O (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>"
  show ?thesis using assms
  proof (cases)
    case (simplifyl s u t \<pi>)
    then have su:"(s, u) \<in> ostep E' R'"
      by (intro ostep_mono [THEN subsetD, OF _ _ simplifyl(3)]) auto
    from simplifyl have "(\<pi> \<bullet> u, \<pi> \<bullet> t) \<in> E'" by auto
    from rstep_rule[OF this] have "(u,t) \<in> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>" using rstep_permute_iff by blast
    with orstep[OF su] have "(s, t) \<in> ?step2" by blast
    then show ?thesis unfolding simplifyl by blast
  next
    case (simplifyr t u s \<pi>)
    then have tu:"(t, u) \<in> ostep E' R'"
      by (intro ostep_mono [THEN subsetD, OF _ _ simplifyr(3)]) auto
    from simplifyr have "(\<pi> \<bullet> s, \<pi> \<bullet> u) \<in> E'" by auto
    from rstep_rule[OF this] have "(s, u) \<in> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>" using rstep_permute_iff by blast
    with orstep[OF tu] have "(s, t) \<in> ?step2" unfolding simplifyr by blast
    then show ?thesis unfolding simplifyr by blast
  next
    case (orientl s t \<pi>)
    have "(s,t) \<in> (rstep R')" unfolding orientl using rstep_permute_iff
      by (metis UnI2 rstep_rule rstep_union singletonI)
    then show ?thesis using orientl by (auto simp: rstep_simps)
  next
    case (orientr s t \<pi>)
    have "(s,t) \<in> (rstep R')" unfolding orientr using rstep_permute_iff
      by (metis UnI2 rstep_rule rstep_union singletonI)
    then show ?thesis using orientr by (auto simp: rstep_simps)
  next
    case (compose t u s \<pi>)
    then have tu:"(t, u) \<in> ostep E' R'"
      by (intro ostep_mono [THEN subsetD, OF _ _ compose(3)]) auto
    from compose have "(\<pi> \<bullet> s, \<pi> \<bullet> u) \<in> R'" by auto
    from rstep_rule[OF this] have "(s, u) \<in> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>" using rstep_permute_iff by blast
    with orstep[OF tu] have "(s, t) \<in> ?step2" by blast
    then show ?thesis unfolding compose by blast
  next
    case (collapse t u s \<pi>)
    then have tu:"(t, u) \<in> ostep E' R'"
      by (intro ostep_mono [THEN subsetD, OF _ _ collapse(3)]) auto
    from collapse have "(\<pi> \<bullet> u, \<pi> \<bullet> s) \<in> E'" by auto
    from rstep_rule[OF this] have "(u,s) \<in> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>" using rstep_permute_iff by blast
    with orstep[OF tu] have "(t, s) \<in> ?step2" by auto
    then show ?thesis unfolding collapse by blast
  qed auto
qed

lemma oKB_ER_permuted_rev:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "E' \<union> R' \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow> \<union> (rstep (E \<union> R))\<^sup>\<leftrightarrow> O (rstep (E \<union> R))\<^sup>\<leftrightarrow>"
proof -
  from ostep_imp_rstep_sym have orstep:"\<And>s t.(s, t) \<in> ostep E R \<Longrightarrow> (s, t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" by blast
  let ?step2 = "(rstep (E \<union> R))\<^sup>\<leftrightarrow> O (rstep (E \<union> R))\<^sup>\<leftrightarrow>"
show ?thesis using assms
proof (cases)
  case (simplifyl s u t \<pi>)
  have "(s, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ simplifyl(3)]) auto
  with simplifyl(4) orstep have "(u, t) \<in> ?step2" by fast
  then show ?thesis unfolding simplifyl by auto
next
  case (simplifyr t u s \<pi>)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ simplifyr(3)]) auto
  with simplifyr(4) orstep have "(s, u) \<in> ?step2" by fast
  then show ?thesis unfolding simplifyr by auto
next
  case (deduce u s t \<pi>)
  then have "(u, s) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" "(u, t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" by auto
  then have "(s, t) \<in> ?step2" by blast
  with deduce show ?thesis by auto
next
  case (collapse t u s \<pi>)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ collapse(3)]) auto
  with collapse(4) orstep have "(u, s) \<in> ?step2" by fast
  then show ?thesis unfolding collapse by auto
next
  case (compose t u s \<pi>)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ compose(3)]) auto
  with compose(4) orstep have "(s, u) \<in> ?step2" by fast
  then show ?thesis unfolding compose by auto
qed auto
qed

lemma oKB_permuted_rstep_subset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "rstep (E \<union> R) \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?C = "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  have 1:"rstep (Id \<union> E' \<union> R') \<subseteq> ?C" by fast
  have 2:"rstep ((rstep (E' \<union> R'))\<^sup>\<leftrightarrow>) \<subseteq> ?C" by fast
  from relcomp_mono[OF 2 2] have 3:"(rstep (E' \<union> R'))\<^sup>\<leftrightarrow> O (rstep (E' \<union> R'))\<^sup>\<leftrightarrow> \<subseteq> ?C"
    unfolding conversion_O_conversion by auto
  from rstep_mono[OF 3] rstep_rstep have 3:"rstep ((rstep (E' \<union> R'))\<^sup>\<leftrightarrow> O (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>) \<subseteq> ?C"
    using conversion_O_conversion
    by (metis relcomp_mono[OF 2 2] conversion_O_conversion rstep_relcomp_idemp1 rstep_simps(5))
  show ?thesis using oKB_ER_permuted [OF oKB, THEN rstep_mono]
  unfolding rstep_union[of _ "_ O _"] rstep_union[of _ "( _)\<^sup>\<leftrightarrow>"] 
  using 1 2 3 by blast
qed

lemma oKB_conversion_permuted_subset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using conversion_mono [OF oKB_permuted_rstep_subset [OF assms]] by auto

lemma oKB_permuted_rstep_subset_rev:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "rstep (E' \<union> R') \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?C = "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  have 1:"rstep ((rstep (E \<union> R))\<^sup>\<leftrightarrow>) \<subseteq> ?C" by fast
  from relcomp_mono[OF 1 1] have 2:"(rstep (E \<union> R))\<^sup>\<leftrightarrow> O (rstep (E \<union> R))\<^sup>\<leftrightarrow> \<subseteq> ?C"
    unfolding conversion_O_conversion by auto
  from rstep_mono[OF 2] rstep_rstep have 3:"rstep ((rstep (E \<union> R))\<^sup>\<leftrightarrow> O (rstep (E \<union> R))\<^sup>\<leftrightarrow>) \<subseteq> ?C"
    using conversion_O_conversion
    by (metis relcomp_mono[OF 1 1] conversion_O_conversion rstep_relcomp_idemp1 rstep_simps(5))
  from oKB_ER_permuted_rev[OF assms, THEN rstep_mono] show ?thesis
    unfolding rstep_union[of _ "_ O _"] using 1 3 by blast
qed

lemma oKB_conversion_permuted_subset_rev:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using conversion_mono [OF oKB_permuted_rstep_subset_rev [OF assms]] by auto

lemma oKB_step_conversion_permuted:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
  shows "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKB_conversion_permuted_subset[OF assms] oKB_conversion_permuted_subset_rev[OF assms] by auto

lemma oKB_steps_conversion_permuted:
  assumes "oKB'\<^sup>*\<^sup>* (E, R) (E', R')"
  shows "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  by (induct "(E, R)" "(E', R')" arbitrary: E' R')
    (force dest!: oKB_step_conversion_permuted)+

lemma oKB_steps_conversion_FGROUND:
  assumes "oKB'\<^sup>*\<^sup>* (E, R) (E', R')"
  shows "FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*) = FGROUND F ((rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*)"
  unfolding FGROUND_def using oKB_steps_conversion_permuted[OF assms] by auto

lemma E_ord_ordstep:"rstep (E_ord (\<succ>) E) = ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)"
proof(rule, rule)
  fix s t
  assume "(s,t) \<in> rstep (E_ord (\<succ>) E)"
  from rstepE[OF this] obtain l r C \<tau> \<sigma> where lr:"(l,r) \<in> E\<^sup>\<leftrightarrow>" and ts:"l\<cdot>\<tau> \<succ> r\<cdot>\<tau>" "s = C\<langle>l\<cdot>\<tau>\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<tau>\<cdot>\<sigma>\<rangle>"
    unfolding E_ord_def mem_Collect_eq
    by (metis (no_types, lifting) Pair_inject)
  from ts subst[OF ts(1)] have ts:"l\<cdot>(\<tau> \<circ>\<^sub>s \<sigma>) \<succ> r\<cdot>(\<tau> \<circ>\<^sub>s \<sigma>)" "s = C\<langle>l\<cdot>(\<tau> \<circ>\<^sub>s \<sigma>)\<rangle>" "t = C\<langle>r\<cdot>(\<tau> \<circ>\<^sub>s \<sigma>)\<rangle>"
    unfolding subst_subst_compose by auto
  show "(s,t) \<in> ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)" unfolding ordstep.simps
    by(rule exI[of _ l],rule exI, rule exI,rule exI, rule exI[of _ "\<tau> \<circ>\<^sub>s \<sigma>"], insert lr ts, auto)
next
  show "ordstep {\<succ>} (E\<^sup>\<leftrightarrow>) \<subseteq> rstep (E_ord (\<succ>) E)"
  proof
    fix s t
    assume "(s, t) \<in> ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)"
    then obtain l r C \<tau> where lr:"(l,r) \<in> E\<^sup>\<leftrightarrow>" and ts:"l\<cdot>\<tau> \<succ> r\<cdot>\<tau>" "s = C\<langle>l\<cdot>\<tau>\<rangle>" "t = C\<langle>r\<cdot>\<tau>\<rangle>" unfolding ordstep.simps by auto
    then have "(l\<cdot>\<tau>,r\<cdot>\<tau>) \<in> E_ord (\<succ>) E" unfolding E_ord_def by auto
    with lr show "(s, t) \<in> rstep (E_ord (\<succ>) E)" unfolding ts by auto
  qed
qed

lemma FGROUND_rstep_FGROUND_ostep:
  assumes "R \<subseteq> {\<succ>}"
    and fgtotal: "\<And>s t. fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
    and funas_less:"funas_trs {\<succ>} \<subseteq> F"
    and funas_ER:"funas_trs E \<union> funas_trs R \<subseteq> F"
  shows "FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*) = FGROUND F ((ostep E R)\<^sup>\<leftrightarrow>\<^sup>*)"
proof(rule, rule)
  fix s t
  assume "(s,t) \<in> FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*)"
  then have fs:"funas_term s \<subseteq> F" "funas_term t \<subseteq> F" and g:"fground F s" "fground F t" "(s,t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding FGROUND_def fground_def by auto
  from fgterm_conv_FGROUND_conv[OF _ g] funas_ER have fgconv:"(s, t) \<in> (FGROUND F (rstep (E \<union> R)))\<^sup>\<leftrightarrow>\<^sup>*"
    by auto
  interpret fgtotal_reduction_order by (insert fgtotal funas_less, standard, auto)
  from FGROUND_rstep_ordstep[of R E] have "FGROUND F (rstep (R \<union> E\<^sup>\<leftrightarrow>)) \<subseteq> (FGROUND F (ostep E R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding ostep_def E_ord_ordstep[symmetric] rstep_union by auto
  then have "FGROUND F (rstep (E \<union> R)) \<subseteq> (FGROUND F (ostep E R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding rstep_union FGROUND_def by auto
  from conversion_mono[OF this] have "(FGROUND F (rstep (E \<union> R)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F (ostep E R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_conversion_idemp by auto
  with fgconv have "(s,t) \<in> (FGROUND F (ostep E R))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with conversion_mono[OF FGROUND_subset] have "(s,t) \<in> (ostep E R)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with fs g show "(s,t) \<in> FGROUND F ((ostep E R)\<^sup>\<leftrightarrow>\<^sup>*)" unfolding FGROUND_def fground_def by auto
next
  note ostep_conv = ostep_iff_ordstep[OF assms(1), symmetric]
  from ordstep_imp_rstep[of _ _ "{\<succ>}" "R \<union> _\<^sup>\<leftrightarrow>", unfolded ostep_conv] have 1:"ostep E R \<subseteq> rstep (R \<union> E\<^sup>\<leftrightarrow>)" by auto
  have "rstep (R \<union> E\<^sup>\<leftrightarrow>) \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with 1 have "ostep E R \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  from conversion_mono[OF this] have "(ostep E R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_conversion_idemp by auto
  then show "FGROUND F ((ostep E R)\<^sup>\<leftrightarrow>\<^sup>*) \<subseteq> FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*)" unfolding FGROUND_def by auto
qed

(*
lemma oKB_permuted_funas:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi> (E', R')"
    and R_less:"R \<subseteq> {\<succ>}"
    and funas_less:"funas_trs {\<succ>} \<subseteq> F"
    and funas:"funas_trs (E \<union> R) \<subseteq> F"
  shows "funas_trs (E' \<union> R') \<subseteq> F"
proof -
  from compatible_rstep_imp_less[OF R_less] SN_less[THEN SN_subset] have "SN (rstep R)" by blast
  from rstep_preserves_funas_terms[OF _ _ _ SN_rstep_imp_wf_trs[OF this]] assms(4) have
    "\<And>s t. funas_term s \<subseteq> F \<Longrightarrow> (s, t) \<in> rstep R \<Longrightarrow> funas_term t \<subseteq> F" by auto
  with funas_ordstep[OF _ funas_less] have
    fostep:"\<And>s t. (s, t) \<in> ostep E R \<Longrightarrow> funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F"
    unfolding ostep_def by blast
  from assms(1) show ?thesis proof(cases)
  case (simplifyl s u t \<pi>)
  have ostep:"(s, u) \<in> ostep E R" by (intro ostep_mono [THEN subsetD, OF _ _ simplifyl(3)]) auto
  from funas simplifyl(4) have "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" by auto
  with simplifyl(4) fostep[OF ostep] show ?thesis by auto
next
  case (simplifyr t u s \<pi>)
  have ostep:"(t, u) \<in> ostep E R" by (intro ostep_mono [THEN subsetD, OF _ _ simplifyr(3)]) auto
  from funas simplifyr(4) have "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" by auto
  with simplifyr(4) fostep[OF ostep] show ?thesis by auto
next
  case (deduce u s t \<pi>)
  then have "(u, s) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" "(u, t) \<in> (rstep (E \<union> R))\<^sup>\<leftrightarrow>" by auto
  then have "(s, t) \<in> ?step2" by blast
  with deduce show ?thesis by auto
next
  case (collapse t u s \<pi>)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ collapse(3)]) auto
  with collapse(4) orstep have "(u, s) \<in> ?step2" by fast
  then show ?thesis unfolding collapse by auto
next
  case (compose t u s \<pi>)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ compose(3)]) auto
  with compose(4) orstep have "(s, u) \<in> ?step2" by fast
  then show ?thesis unfolding compose by auto
qed auto*)

lemma oKB'_rtrancl_FGROUND_conversion:
  assumes "oKB'\<^sup>*\<^sup>* (E, R) (E', R')"
    and R:"R \<subseteq> {\<succ>}"
    and fgtotal: "\<And>s t. fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
    and funas_less:"funas_trs {\<succ>} \<subseteq> F"
    and funas_ER:"funas_trs E' \<union> funas_trs R' \<subseteq> F"
  shows "FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*) = FGROUND F ((ostep E' R')\<^sup>\<leftrightarrow>\<^sup>*)"
proof -
  from assms oKB'_rtrancl_less have "R' \<subseteq> {\<succ>}" by auto
  note step = FGROUND_rstep_FGROUND_ostep[OF this fgtotal funas_less]
  from oKB_steps_conversion_FGROUND[OF assms(1)] step funas_ER show ?thesis by auto
qed

lemma oKB'_correct:
  assumes run:"oKB'\<^sup>*\<^sup>* (E, R) (E', R')"
  and cps: "\<And>r r' p \<mu> u v. ooverlap {\<succ>} (R' \<union> (E')\<^sup>\<leftrightarrow>) r r' p \<mu> u v \<Longrightarrow> fground_joinable F {\<succ>} (R' \<union> (E')\<^sup>\<leftrightarrow>) u v"
  and R:"R \<subseteq> {\<succ>}"
  and fgtotal: "\<And>s t. fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
  and funas_less:"funas_trs {\<succ>} \<subseteq> F"
  and funas_ER:"funas_trs E' \<union> funas_trs R' \<subseteq> F"
  and ro:"reduction_order less"
  and fgtotal: "\<And>s t. fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
  and funas_less:"funas_trs {\<succ>} \<subseteq> F"
  shows "CR (FGROUND F (ordstep {\<succ>} (R' \<union> E'\<^sup>\<leftrightarrow>))) \<and> (FGROUND F ((rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*) = FGROUND F ((ostep E' R')\<^sup>\<leftrightarrow>\<^sup>*))"
proof-
  let ?R = "R' \<union> (E')\<^sup>\<leftrightarrow>"
  from R oKB'_rtrancl_less[OF run] have "R' \<subseteq> {\<succ>}" by auto
  hence R_sym:"\<And>s t. (s, t) \<in> ?R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> ?R" by auto
  interpret fgtotal_reduction_order_inf less F using fgtotal funas_less ro by (unfold_locales, auto)
  note gcr = ground_joinable_ooverlaps_implies_GCR[OF cps, OF _ R_sym]
  with oKB'_rtrancl_FGROUND_conversion[OF run R fgtotal funas_less funas_ER] show ?thesis by simp
qed

lemma check_oc:
  assumes ok: "isOK (check_oc (E, R) (E', R') xs)" and R:"isOK (check_oriented R)"
  shows "\<exists>E'' R''. oKB'\<^sup>*\<^sup>* (set E, set R) (set E'', set R'') \<and> set R'' \<doteq> set R' \<and> set E''\<doteq> set E'"
proof -
  from check_oriented[OF R] have R: "set R \<subseteq> {\<succ>}" by auto
  with ok show ?thesis
  proof (induct xs arbitrary: E R)
    case Nil
    with check_variants_trs have "set R \<doteq> set R'" "set E \<doteq> set E'"
      unfolding Litsim_Trs.subsumable_trs.litsim_def Litsim_Trs.subsumeseq_trs_def by auto
    with Nil show ?case by blast
  next
    case (Cons x xs)
    then obtain E'' and R'' where 1: "check_step (E, R) x = return (E'', R'')"
      and 2: "isOK (check_oc (E'', R'') (E', R') xs)" by auto
    note step = check_step_return[OF 1 Cons(3)]
    from step[THEN oKB'_less] Cons(3) have less:"set R'' \<subseteq> {\<succ>}" by auto
    from Cons.hyps [OF 2 less] obtain E\<^sub>\<pi> R\<^sub>\<pi> where
      *:"oKB'\<^sup>*\<^sup>* (set E'', set R'') (set E\<^sub>\<pi>, set R\<^sub>\<pi>) \<and> set R\<^sub>\<pi> \<doteq> set R' \<and> set E\<^sub>\<pi> \<doteq> set E'" by auto
    show ?case by (rule exI[of _ E\<^sub>\<pi>], rule exI[of _ R\<^sub>\<pi>], insert step *, auto)
  qed
qed

end


locale oc_spec_extension = 
oc:oc_spec less1 check_ord1 +
oc':oc_spec less2 check_ord2
for less1 less2 :: "('a:: showl, string) term \<Rightarrow> ('a, string) term \<Rightarrow> bool" and
    check_ord1 check_ord2  check_ord :: "('a, string) term \<Rightarrow> ('a, string) term \<Rightarrow> showsl check" +
assumes less_extension:"\<And>s t. less1 s t \<Longrightarrow> less2 s t"
begin

lemma ostep:"(s,t) \<in> oc.ostep E R \<Longrightarrow> (s,t) \<in> oc'.ostep E R"
  unfolding oc.ostep_def oc'.ostep_def Un_iff ordstep.simps
  using less_extension by fast

lemma oKB'_step:
  assumes "oc.oKB' (E,R) (E',R')"
  shows "oc'.oKB' (E,R) (E',R')"
  using assms
proof(cases)
  case (deduce s t u p)
  show ?thesis unfolding deduce
    using deduce(3) deduce(4) oc'.oKB'.deduce by blast
next
  case (orientl s t p)
  show ?thesis unfolding orientl
    using less_extension[OF orientl(3)] orientl(4) oc'.oKB'.orientl by blast
next
  case (orientr t s p)
  show ?thesis unfolding orientr
    using less_extension[OF orientr(3)] orientr(4) oc'.oKB'.orientr by blast
next
  case (delete s)
  show ?thesis unfolding delete using delete(3) oc'.oKB'.delete by blast
next
  case (compose t u s p)
  show ?thesis unfolding compose
    using ostep[OF compose(3)] compose(4) oc'.oKB'.compose by blast
next
  case (simplifyl s u t p)
  show ?thesis unfolding simplifyl
    using ostep[OF simplifyl(3)] simplifyl(4) oc'.oKB'.simplifyl by blast
next
  case (simplifyr t u s p)
  show ?thesis unfolding simplifyr
    using ostep[OF simplifyr(3)] simplifyr(4) oc'.oKB'.simplifyr by blast
next
  case (collapse t u s p)
  show ?thesis unfolding collapse
    using ostep[OF collapse(3)] collapse(4) oc'.oKB'.collapse by blast
qed

lemma oKB'_steps:
  assumes "oc.oKB'\<^sup>*\<^sup>* (E,R) (E',R')"
  shows "oc'.oKB'\<^sup>*\<^sup>* (E,R) (E',R')"
  using assms
  by (induct "(E, R)" "(E', R')" arbitrary: E' R')
     (force dest!: oKB'_step)+
end

locale gcr_ops =
  fixes xvar yvar :: "'v::{showl, infinite} \<Rightarrow> 'v"
    and check_joinable :: "('f:: showl, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
    and check_instance :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
begin

definition "check_ooverlap E R \<rho>\<^sub>1 \<rho>\<^sub>2 p =
  (case mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) of
    None \<Rightarrow> succeed
  | Some (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow>
    let s = replace_at (fst \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (snd \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1)  in
    let t = snd \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2 in
    choice [
      check_instance E R s t <+? (\<lambda>e. showsl_lit (STR ''CP '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_lit (STR '' not an instance of an equation'') \<circ> e),
      check_joinable E R s t <+? (\<lambda>e. showsl_lit (STR ''CP '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_lit (STR '' is not joinable'') \<circ> e)
    ] <+? showsl_sep id showsl_nl)"

text \<open>Check extended critical pairs.\<close>
definition
  "check_ECPs E R =
    (let E' = sym_list E; S = List.union R E' in
    check_allm (\<lambda>\<rho>\<^sub>2. let l\<^sub>2 = fst \<rho>\<^sub>2 in check_allm (\<lambda>\<rho>\<^sub>1. check_allm (\<lambda>p.
      check_ooverlap E' R \<rho>\<^sub>1 \<rho>\<^sub>2 p) (fun_poss_list l\<^sub>2)) S) S)"

end

lemmas [code] =
  gcr_ops.check_ooverlap_def gcr_ops.check_ECPs_def

definition "Rules E R = List.union R (sym_list E)"

lemma set_Rules [simp]: "set (Rules E R) = set R \<union> (set E)\<^sup>\<leftrightarrow>" by (auto simp: Rules_def)

locale gcr_spec =
  gcr_ops xvar yvar check_joinable check_instance +
  fgtotal_reduction_order_inf less UNIV
  for xvar :: "'v::{showl, infinite} \<Rightarrow> 'v"
  and yvar :: "'v \<Rightarrow> 'v"
  and check_joinable :: "('f:: showl, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  and check_instance :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  and less :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<succ>" 50) (* TODO: should read as gt *)
  and F :: "('f \<times> nat) list" +
  assumes joinable: "set R \<subseteq> {\<succ>} \<Longrightarrow> isOK (check_joinable E R s t) \<Longrightarrow>
      (s, t) \<in> (ordstep {\<succ>} (set (Rules E R)))\<^sup>\<down>"
    and "instance": "isOK (check_instance E R s t) \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> set (Rules E R) \<and> s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma>"
    and ren: "inj xvar" "inj yvar" "range xvar \<inter> range yvar = {}"
begin

lemma check_ECPs_ooverlap:
  assumes "isOK (check_ECPs E R)"
    and "ooverlap {\<succ>} (set (Rules E R)) r r' p \<mu> s t"
    and R: "set R \<subseteq> {\<succ>}"
  shows "(s, t) \<in> (ordstep {\<succ>} (set (Rules E R)))\<^sup>\<down> \<or>
    (\<exists>l r \<sigma>. (l, r) \<in> (set (Rules E R))\<^sup>\<leftrightarrow> \<and> s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma>)"
proof -
  let ?R = "set (Rules E R)"
  from assms(2) obtain \<pi>\<^sub>1 and \<pi>\<^sub>2 where rules': "\<pi>\<^sub>1 \<bullet> r \<in> ?R" "\<pi>\<^sub>2 \<bullet> r' \<in> ?R"
    and disj: "vars_rule r \<inter> vars_rule r' = {}"
    and p': "p \<in> fun_poss (fst r')"
    and mgu': "mgu (fst r) (fst r' |_ p) = Some \<mu>"
    and "\<not> (snd r \<cdot> \<mu> \<succ> fst r \<cdot> \<mu>)" "\<not> (snd r' \<cdot> \<mu> \<succ> fst r' \<cdot> \<mu>)"
    and t: "t = snd r' \<cdot> \<mu>"
    and s: "s = replace_at (fst r' \<cdot> \<mu>) p (snd r \<cdot> \<mu>)"
    unfolding ooverlap_def by fast
  define \<rho>\<^sub>1 and \<rho>\<^sub>2 where "\<rho>\<^sub>1 = \<pi>\<^sub>1 \<bullet> r" and "\<rho>\<^sub>2 = \<pi>\<^sub>2 \<bullet> r'"
  have p: "p \<in> fun_poss (fst \<rho>\<^sub>2)"
    and "\<rho>\<^sub>1 \<in> ?R" and "\<rho>\<^sub>2 \<in> ?R"
    using p' and rules' by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def rule_pt.fst_eqvt [symmetric])
  with assms have *: "isOK (check_ooverlap (sym_list E) R \<rho>\<^sub>1 \<rho>\<^sub>2 p)" by (auto simp: check_ECPs_def)
      
  have "(fst r' |_ p) \<cdot> \<mu> = fst r \<cdot> \<mu>" using mgu' [THEN mgu_sound] by (auto simp: is_imgu_def)
  then have "(fst r' |_ p) \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2) \<circ> Rep_perm \<pi>\<^sub>2) =
    fst r \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1) \<circ> Rep_perm \<pi>\<^sub>1)"
    by (simp add: o_assoc [symmetric] Rep_perm_add [symmetric] Rep_perm_0)
  then have "fst \<rho>\<^sub>2 |_ p \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2)) = fst \<rho>\<^sub>1 \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1))"
    using p [THEN fun_poss_imp_poss]
    by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def permute_term_subst_apply_term [symmetric] eqvt)
  from mgu_var_disjoint_generic_complete [OF ren this[symmetric]] obtain \<mu>\<^sub>1 \<mu>\<^sub>2 \<delta>
    where mgu: "mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    and **: "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>1) = \<mu>\<^sub>1 \<circ>\<^sub>s \<delta>" "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>2) = \<mu>\<^sub>2 \<circ>\<^sub>s \<delta>" by blast

  have "vars_term (fst r) \<subseteq> vars_rule r" and "vars_term (fst r' |_ p) \<subseteq> vars_rule r'"
    using p' [THEN fun_poss_imp_poss, THEN vars_term_subt_at] by (auto simp: vars_defs)
  from mgu_imp_mgu_var_disjoint [OF mgu' ren disj this finite_vars_rule finite_vars_rule, of \<pi>\<^sub>1 \<pi>\<^sub>2]
  obtain \<mu>' and \<pi>
    where left: "\<forall>x\<in>vars_rule r. \<mu> x = (sop \<pi>\<^sub>1 \<circ>\<^sub>s (\<mu>' \<circ> xvar) \<circ>\<^sub>s sop (- \<pi>)) x" (is "\<forall>x\<in>_. \<mu> x = ?\<pi>\<^sub>1 x")
      and right: "\<forall>x\<in>vars_rule r'. \<mu> x = (sop \<pi>\<^sub>2 \<circ>\<^sub>s (\<mu>' \<circ> yvar) \<circ>\<^sub>s sop (- \<pi>)) x" (is "\<forall>x\<in>_. \<mu> x = ?\<pi>\<^sub>2 x")
      and "mgu (\<pi>\<^sub>1 \<bullet> (fst r) \<cdot> (Var \<circ> xvar)) (\<pi>\<^sub>2 \<bullet> (fst r' |_ p) \<cdot> (Var \<circ> yvar)) = Some \<mu>'"
    by blast
  then have "mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) = Some (\<mu>' \<circ> xvar, \<mu>' \<circ> yvar)"
    and \<mu>\<^sub>1: "\<mu>\<^sub>1 = \<mu>' \<circ> xvar" and \<mu>\<^sub>2: "\<mu>\<^sub>2 = \<mu>' \<circ> yvar"
    using p' [THEN fun_poss_imp_poss] and mgu
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def mgu_var_disjoint_generic_def 
    by (auto simp: map_vars_term_eq mgu_var_disjoint_generic_def \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt)

  let ?t = "snd \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2"
  let ?t' = "snd r' \<cdot> \<mu>"
  let ?s = "replace_at (fst \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2) p (snd \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1)"
  let ?s' = "replace_at (fst r' \<cdot> \<mu>) p (snd r \<cdot> \<mu>)"
 
  have "fst r' \<cdot> \<mu> = fst r' \<cdot> ?\<pi>\<^sub>2" and snd_r: "snd r' \<cdot> \<mu> = snd r' \<cdot> ?\<pi>\<^sub>2"
    using right unfolding term_subst_eq_conv by (auto simp: vars_defs)
  then have 1: "fst \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 = \<pi> \<bullet> (fst r' \<cdot> \<mu>)"
    and t': "?t' = -\<pi> \<bullet> ?t" by (auto simp: \<mu>\<^sub>2 \<rho>\<^sub>2_def eqvt)
  
  have "snd r \<cdot> \<mu> = snd r \<cdot> ?\<pi>\<^sub>1"
    using left unfolding term_subst_eq_conv by (auto simp: vars_defs)
  then have 2: "snd \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 = \<pi> \<bullet> (snd r \<cdot> \<mu>)" by (auto simp: \<mu>\<^sub>1 \<rho>\<^sub>1_def eqvt)
  then have s': "?s' = -\<pi> \<bullet> ?s"
    using p' [THEN fun_poss_imp_poss]
    unfolding 1 by (auto simp: eqvt)
  from snd_r have 2: "snd \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 = \<pi> \<bullet> (snd r' \<cdot> \<mu>)" by (auto simp: \<mu>\<^sub>2 \<rho>\<^sub>2_def eqvt)

  consider (join) "isOK (check_joinable (sym_list E) R ?s ?t)"
    | (inst) "isOK (check_instance (sym_list E) R ?s ?t)"
    using * and mgu unfolding check_ooverlap_def by (auto simp: check_ooverlap_def)
  then show ?thesis
  proof (cases)
    case join
    from joinable [OF R join] have "(?s, ?t) \<in> (ordstep {\<succ>} ?R)\<^sup>\<down>" by simp
    from join_subst [OF subst_closed_ordstep [OF subst_closed_less] this, of "sop (-\<pi>)"]
    have "(s, t) \<in> (ordstep {\<succ>} ?R)\<^sup>\<down>"
      using p [THEN fun_poss_imp_poss]
      unfolding s t s' using term_pt.permute_flip [OF 1] term_pt.permute_flip [OF 2]
      by (simp add: eqvt [symmetric])
    then show ?thesis by blast
  next
    case inst
    from "instance" [OF inst] obtain u and v and \<sigma>
      where uv: "(u, v) \<in> ?R\<^sup>\<leftrightarrow>" and "?s = u \<cdot> \<sigma>" and "?t = v \<cdot> \<sigma>" by auto
    then have "?s' = u \<cdot> (\<sigma> \<circ>\<^sub>s (sop (- \<pi>)))"
      and "?t' = v \<cdot> (\<sigma> \<circ>\<^sub>s (sop (- \<pi>)))" by (auto simp: s' t')
    with uv show ?thesis unfolding s t by blast
  qed
qed

lemma check_ECPs:
  assumes R: "set R \<subseteq> {\<succ>}" and ok: "isOK (check_ECPs E R)"
  shows "GCR (ordstep {\<succ>} (set (Rules E R)))"
proof -
  have [simp]:"\<And>R. FGROUND UNIV R = GROUND R" unfolding FGROUND_def GROUND_def fground_def by simp
  { fix s t assume "(s, t) \<in> set (Rules E R)"
    with R have "s \<succ> t \<or> (t, s) \<in> set (Rules E R)" by auto }
  then show ?thesis
    using check_ECPs_ooverlap [OF ok _ R] GCR_ordstep by fastforce
qed
end

definition "check_joinable R s t =
  (case (compute_rstep_NF R s, compute_rstep_NF R t) of
    (Some u, Some v) \<Rightarrow> check (u = v) (showsl_lit (STR ''normal forms differ''))
  | _ \<Rightarrow> error (showsl_lit (STR ''error: check_joinable'')))"
  
lemma check_joinable:
  assumes "isOK (check_joinable R s t)"
  shows "(s, t) \<in> (rstep (set R))\<^sup>\<down>"
  using assms
  by (auto simp: check_joinable_def split: option.splits dest: compute_rstep_NF_sound)

definition "check_rule_instance r r' =
  (case match_list Var [(fst r', fst r), (snd r', snd r)] of
    Some _ \<Rightarrow> succeed
  | None \<Rightarrow> error (showsl_lit (STR ''rules do not match'')))"
  
lemma check_rule_instance [simp]:
  "isOK (check_rule_instance (l, r) (l', r')) \<longleftrightarrow> (\<exists>\<sigma>. l = l' \<cdot> \<sigma> \<and> r = r' \<cdot> \<sigma>)"
  by (auto simp: check_rule_instance_def split: option.splits dest!: match_list_sound match_list_complete)

definition "check_instance E s t =
  check_exm (check_rule_instance (s, t)) E (showsl_sep id showsl_nl)"
  
lemma check_instance [simp]:
   "isOK (check_instance E s t) \<longleftrightarrow> (\<exists>l r \<sigma>. (l, r) \<in> set E \<and> s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma>)"
  by (auto simp: check_instance_def) (insert check_rule_instance, blast+)

context oc_spec
begin

lemma gcr_spec:
  assumes "gtotal_reduction_order (\<succ>)"
  shows "gcr_spec x_var y_var (\<lambda>_. check_joinable) (\<lambda>E _. check_instance E) (\<succ>)"
proof -
  interpret gtotal_reduction_order "(\<succ>)" by fact
  interpret gcr_spec x_var y_var
    "(\<lambda>_. check_joinable)" "(\<lambda>E _. check_instance E)"
    apply (unfold_locales)
        apply (drule check_joinable)
        apply (rule join_mono [THEN subsetD, of "rstep (set R)" "ordstep {\<succ>} (set (Rules E R))" for E R])
         apply (simp add: ordstep_Un ordstep_rstep_conv subst_closed_less)
        apply assumption
       apply force+
    done
  show ?thesis ..
qed

end

definition "check_ECPs =
  gcr_ops.check_ECPs x_var y_var (\<lambda>_. check_joinable) (\<lambda>E _. check_instance E)"

definition "check_FGCR ro F E R = do {
  redord.valid ro;
  check_subseteq (funas_trs_list (List.union E R)) F
    <+? (\<lambda>f. showsl_lit (STR ''the function symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' does not occur in the TRS\<newline>''));
  check_ECPs E R
}"

lemma check_FGCR:
  fixes F :: "('f::{showl,compare_order} \<times> nat) list" and r
  defines "ro \<equiv> create_KBO_redord r F"
  assumes "isOK (check_FGCR ro F E R)"
    and R: "set R \<subseteq> {(s, t). redord.less ro s t}"
  shows "CR (FGROUND (set F) (ordstep ({(s, t). redord.less ro s t}) (set (Rules E R))))"
proof -
  let ?F = "set F"
  let ?R = "set (Rules E R)"

  define less :: "('f, string) term \<Rightarrow> ('f, string) term \<Rightarrow> bool" and c :: "'f"
    where
      "less = redord.less ro" and
      "c = redord.min_const ro"

  have valid: "isOK (redord.valid ro)"
    and ecps: "isOK (check_ECPs E R)"
    and F: "funas_trs ?R \<subseteq> ?F"
    using assms by (auto simp: check_FGCR_def)

  from KBO_redord.valid [OF valid [unfolded ro_def]] obtain less'
    where ro: "reduction_order less"
      and c: "(c, 0) \<in> ?F"
      and fground: "\<forall>s t. fground ?F s \<and> fground ?F t \<longrightarrow> s = t \<or> less s t \<or> less t s"
      and ro': "gtotal_reduction_order less'"
      and subset: "\<forall>s t. less s t \<longrightarrow> less' s t"
      and min: "\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun c [])"
    by (auto simp: less_def c_def ro_def)

  interpret ro: reduction_order less by fact
  interpret ro': gtotal_reduction_order less' by fact

  have R: "set R \<subseteq> ro'.less_set" using R and subset by (auto simp: less_def)

  have *: "{(x, y). less x y} \<subseteq> ro'.less_set" using subset by auto

  interpret oc: oc_spec less' "\<lambda>s t. check (less' s t) (showsl_lit (STR ''''))" by (unfold_locales) simp
  interpret gcr: gcr_spec x_var y_var "(\<lambda>_. check_joinable)" "(\<lambda>E _. check_instance E)" less'
    using oc.gcr_spec [OF ro'] .

  have "isOK (gcr.check_ECPs E R)" using ecps by (auto simp: check_ECPs_def)
  then have "GCR (ordstep ro'.less_set ?R)" by (rule gcr.check_ECPs [OF R])
  then show ?thesis using ro'.GCR_imp_CR_FGROUND [OF * ro fground min c F] by (simp add: less_def)
qed

definition "check_FGCR_run ro F E\<^sub>0 R\<^sub>0 E R steps = do {
  let check_ord = (\<lambda>s t. check (redord.less ro s t) (showsl_lit (STR ''term pair cannot be oriented'')));
  oc_ops.check_oriented check_ord R\<^sub>0;
  oc_ops.check_oc check_ord (E\<^sub>0, R\<^sub>0) (E, R) steps <+? (\<lambda>s. showsl_lit (STR ''the oKB run could not be reconstructed\<newline>\<newline>'') \<circ> s);
  check_FGCR ro F E R <+? (\<lambda>s. showsl_lit (STR ''ground confluence could not be verified\<newline>\<newline>'') \<circ> s)
}"

lemma check_FGCR_run:
  fixes F :: "('f::{showl,compare_order} \<times> nat) list"
    and E :: "(('f, char list) term \<times> ('f, char list) term) list"
    and r
  defines "ro \<equiv> create_KBO_redord r F"
  assumes "isOK (check_FGCR_run ro F E\<^sub>0 R\<^sub>0 E R steps)"
  shows "CR (FGROUND (set F) (ordstep ({(s, t). redord.less ro s t}) (set (Rules E R)))) \<and>
    equivalent (set E\<^sub>0 \<union> set R\<^sub>0) (set E \<union> set R)"
proof -
  let ?F = "set F"
  let ?ER = "set (Rules E R)"

  define less :: "('f, string) term \<Rightarrow> ('f, string) term \<Rightarrow> bool" and c :: "'f"
    where
      "less = redord.less ro" and
      "c = redord.min_const ro"

  from assms have FGCR: "isOK (check_FGCR ro F E R)" by (auto simp: check_FGCR_run_def)

  have valid: "isOK (redord.valid ro)"
    and ecps: "isOK (check_ECPs E R)"
    and F: "funas_trs ?ER \<subseteq> ?F"
    using FGCR by (auto simp: check_FGCR_def)

  from KBO_redord.valid [OF valid [unfolded ro_def]] obtain less'
    where ro: "reduction_order less"
      and c: "(c, 0) \<in> ?F"
      and fground: "\<forall>s t. fground ?F s \<and> fground ?F t \<longrightarrow> s = t \<or> less s t \<or> less t s"
      and ro': "gtotal_reduction_order less'"
      and subset: "\<forall>s t. less s t \<longrightarrow> less' s t"
    by (auto simp: less_def c_def ro_def)

  interpret ro: reduction_order less by fact
  interpret ro': gtotal_reduction_order less' by fact

  define check_ord where "check_ord = (\<lambda>s t. check (less s t) (showsl_lit (STR ''term pair cannot be oriented'')))"
  have check_ord: "\<And>s t. isOK (check_ord s t) \<longleftrightarrow> less s t" unfolding check_ord_def by auto
  define check_ord' where "check_ord' = (\<lambda>s t. check (less' s t) (showsl_lit (STR ''term pair cannot be oriented'')))"
  have check_ord': "\<And>s t. isOK (check_ord' s t) \<longleftrightarrow> less' s t" unfolding check_ord'_def by auto

  interpret oc: oc_spec less check_ord by (insert check_ord, unfold_locales) simp
  interpret oc': oc_spec less' check_ord' by (insert check_ord', unfold_locales) simp

  have oc_ok: "isOK (oc.check_oc (E\<^sub>0, R\<^sub>0) (E, R) steps)" and
       oriented_ok: "isOK (oc.check_oriented R\<^sub>0)"
    using assms[unfolded check_FGCR_run_def] unfolding check_ord_def less_def by force+

  note run = oc.check_oc[OF this]
  let ?variant_trs = "\<lambda> R R'. \<forall>r\<in>set R :: (_,_) trs. \<exists>p. p \<bullet> r \<in> set R'"
  from run obtain E\<^sub>\<pi> R\<^sub>\<pi> where run\<^sub>\<pi>:"oc.oKB'\<^sup>*\<^sup>* (set E\<^sub>0, set R\<^sub>0) (set E\<^sub>\<pi>, set R\<^sub>\<pi>)" and
    vs:"set R\<^sub>\<pi> \<doteq> set R" "set E\<^sub>\<pi> \<doteq> set E" by auto
  note litsim = Litsim_Trs.subsumable_trs.litsim_def[unfolded Litsim_Trs.subsumeseq_trs_def]
  note oriented = oc.check_oriented[OF oriented_ok]
  with run\<^sub>\<pi>[THEN oc.oKB'_rtrancl_less] vs(1) have "set R \<subseteq> ro.less_set"
    using oc.less_set_permute litsim by (meson oc.R_less_litsim_R_less subsumable_trs.litsim_sym)
    
  with check_FGCR[OF FGCR [unfolded ro_def]] have CR:"CR (FGROUND ?F (ordstep {(s, t). less s t} ?ER))"
    using less_def by (auto simp: ro_def)

  from vs have "set E\<^sub>\<pi> \<union> set R\<^sub>\<pi> \<doteq> set E \<union> set R" using litsim by (simp add: litsim_union)
  note rstep_eq = litsim_rstep_eq[OF this]
  note equiv = oc.oKB_steps_conversion_permuted[OF run\<^sub>\<pi>]
  with CR less_def show ?thesis
    unfolding equivalent_def rstep_eq by (simp add: equiv)
qed

text \<open>
We say that the system @{term E},@{term R} is a ground-complete rewrite system for the
equational system @{term E\<^sub>0} with respect to the reduction order @{term less} iff the
respective equational theories are the same and ordered rewriting with @{term E},@{term R},
and @{term less} is confluent on ground terms.
\<close>

datatype 'f reduction_order_input =
    RPO_Input "'f status_prec_repr"
  | KBO_Input "'f prec_weight_repr"

definition "precw_w0_sig precw_w0 \<equiv> map fst (fst precw_w0)"

definition
  ordered_completed_rewrite_system :: "('f::compare_order, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f reduction_order_input \<Rightarrow> bool"
where
  "ordered_completed_rewrite_system E\<^sub>0 E R ord \<equiv>
   case ord of KBO_Input precw \<Rightarrow>
     let (p,w,w0,lcs,scf) = prec_weight_repr_to_prec_weight_funs precw in
     let less = \<lambda> s t. fst (kbo.kbo w w0 (scf_repr_to_scf scf) (\<lambda>f. f \<in> set lcs) (\<lambda> f g. fst (p f g)) (\<lambda> f g. snd (p f g)) s t) in
     equivalent E\<^sub>0 (E \<union> R) \<and> CR (FGROUND (set (precw_w0_sig precw)) (ordstep {(s, t). less s t} (E\<^sup>\<leftrightarrow> \<union> R)))"

(* extend to more powerful criterion by Martin/Nipkow *)
locale moc_ops =
  fixes check_ord :: "('f::showl, 'v::showl) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
  and least :: "'f"
begin

definition ext_subst where "ext_subst \<sigma> l =
  (\<lambda>x. if x \<in> set (vars_term_impl l) then \<sigma> x else Fun least [])"

fun mord_rewrite :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
  "mord_rewrite R s = concat (map (\<lambda> (l, r). concat (map (\<lambda> p.
    (case match (s |_ p) l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow>
      let \<sigma>' = ext_subst \<sigma> l in
      if check_ord (l \<cdot> \<sigma>') (r \<cdot> \<sigma>') then [replace_at s p (r \<cdot> \<sigma>')] else [])) (poss_list s))) R)"

definition first_mord_rewrite                         
  where "first_mord_rewrite R s \<equiv> case mord_rewrite R s of Nil \<Rightarrow> None | Cons t _ \<Rightarrow> Some t"

definition compute_mordstep_NF where "compute_mordstep_NF R s \<equiv> compute_NF (first_mord_rewrite R) s"

definition "check_instance_joinable E R s t =
  (case (compute_mordstep_NF (E @ R) s, compute_mordstep_NF (E @ R) t) of
    (Some u, Some v) \<Rightarrow>
      choice [check (u = v) (showsl_lit (STR ''normal forms differ'')), check_rstep E u v]
        <+? showsl_sep id showsl_nl
  | _ \<Rightarrow> error (showsl (STR ''error: check_instance_joinable'')))"
end

lemmas [code] =
  moc_ops.ext_subst_def
  moc_ops.mord_rewrite.simps
  moc_ops.first_mord_rewrite_def
  moc_ops.compute_mordstep_NF_def
  moc_ops.check_instance_joinable_def

locale moc_spec = moc_ops less least
  for less :: "('f::showl, 'v::showl) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" (infix "\<succ>" 50)
  and least :: "'f" +
  fixes F :: "('f \<times> nat) set"
  assumes least:"\<forall>t. (fground F t \<longrightarrow> t = Fun least [] \<or> t \<succ> Fun least [])"
begin

abbreviation all_less where  "all_less \<equiv> {(x, y). x \<succ> y}"

lemma rewrite_mordstep_sound:
  assumes "t \<in> set (mord_rewrite R s)"
  shows "(s, t) \<in> mordstep least all_less (set R)"
proof -
  from assms 
  have "\<exists> l r p \<sigma> \<sigma>'. (l,r) \<in> set R \<and> p \<in> poss s \<and> match (s|_p) l = Some \<sigma> \<and> \<sigma>' = ext_subst \<sigma> l
                      \<and> t = (ctxt_of_pos_term p s)\<langle>r\<cdot>\<sigma>'\<rangle> \<and> less (l\<cdot>\<sigma>') (r\<cdot>\<sigma>')" 
    by (simp, unfold Let_def, force)
  from this obtain l r p \<sigma> \<sigma>' where *:
    "(l,r) \<in> set R" "match (s|_p) l = Some \<sigma>" "\<sigma>' = ext_subst \<sigma> l"
     "less (l\<cdot>\<sigma>') (r\<cdot>\<sigma>')" and c:"p \<in> poss s" "t = (ctxt_of_pos_term p s)\<langle>r\<cdot>\<sigma>'\<rangle>"
    by auto
  hence "l \<cdot> \<sigma> = s|_p" using match_sound by auto
  with *(3) term_subst_eq_conv[of l \<sigma> \<sigma>'] have match:"l \<cdot> \<sigma>' = s|_p" unfolding ext_subst_def by simp
  from * have ord:"(l\<cdot>\<sigma>', r\<cdot>\<sigma>') \<in> all_less" by auto
  have least:"\<forall>x\<in>vars_term r - vars_term l. \<sigma>' x = Fun least []"
    unfolding *(3) unfolding ext_subst_def[of \<sigma>] using set_insert_vars_term_vars_term by auto
  from mordstep.intros[OF *(1) ord _ c(2) least, of s] match ctxt_supt_id[OF c(1)] show ?thesis by auto
qed

lemma compute_mordstep_NF_sound':
  assumes res: "compute_mordstep_NF R s = Some t"
  shows "(s, t) \<in> (mordstep least all_less (set R))\<^sup>*" using res[unfolded compute_mordstep_NF_def]
proof (rule compute_NF_sound)
  fix s t
  assume a:"first_mord_rewrite R s = Some t"
  note a = this[unfolded first_mord_rewrite_def]
  have "\<exists>ts. mord_rewrite R s = t # ts"
    proof(cases "mord_rewrite R s")
    case Nil
    with a[unfolded Nil] show ?thesis by force
  next
    case (Cons u us)
    with a[unfolded Cons, simplified] show ?thesis by blast
  qed
  then obtain ts where "mord_rewrite R s = t # ts" by auto
  hence t: "t \<in> set (mord_rewrite R s)" by simp
  from rewrite_mordstep_sound[OF this] mordstep_ordstep show "(s,t) \<in> mordstep least all_less (set R)" by fast
qed

lemma compute_mordstep_NF_sound:
  assumes res: "compute_mordstep_NF R s = Some t"
  shows "(s, t) \<in> (ordstep all_less (set R))\<^sup>*"
  using compute_mordstep_NF_sound'[OF assms] rtrancl_mono[OF mordstep_ordstep] by fast

lemma check_instance_joinable:
  assumes "isOK(check_instance_joinable E R s t)"
  shows "(s, t) \<in> ((ordstep all_less (set (E @ R)))\<^sup>* O (rstep (set E))\<^sup>= O ((ordstep all_less (set (E @ R)))\<inverse>)\<^sup>*)"
proof -
  let ?R = "ordstep all_less (set (E @ R))" 
  note assms = assms[unfolded check_instance_joinable_def]
  hence "\<exists>u v. compute_mordstep_NF (E @ R) s = Some u \<and> compute_mordstep_NF (E @ R) t = Some v \<and> (u = v \<or> isOK(check_rstep E u v))"
    by (cases "compute_mordstep_NF (E @ R) s", simp, cases "compute_mordstep_NF (E @ R) t", auto)
  then obtain u v where u:"compute_mordstep_NF (E @ R) s = Some u"
    and v:"compute_mordstep_NF (E @ R) t = Some v" 
    and join:"u = v \<or> isOK(check_rstep E u v)" by force
  from compute_mordstep_NF_sound[OF u] compute_mordstep_NF_sound[OF v] have su:"(s, u) \<in> ?R\<^sup>*" and tv:"(t, v) \<in> ?R\<^sup>*" by auto
  from tv rtrancl_converse have vt:"(v,t) \<in> (?R\<inverse>)\<^sup>*" by blast
  from join check_rstep have "(u,v) \<in> (rstep (set E))\<^sup>=" by fast
  with su vt show ?thesis unfolding relcomp.simps by metis
qed

lemma check_instance_joinable':
  assumes "isOK(check_instance_joinable E R s t)"
  shows "(s, t) \<in> (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from assms check_instance_joinable
  have "(s, t) \<in> ((ordstep all_less (set (E @ R)))\<^sup>* O (rstep (set E))\<^sup>= O ((ordstep all_less (set (E @ R)))\<inverse>)\<^sup>*)" by auto
  then obtain u v where
    su: "(s, u) \<in> (ordstep all_less (set (E @ R)))\<^sup>*" and
    uv: "(u, v) \<in> (rstep (set E))\<^sup>=" and
    vt: "(v, t) \<in> ((ordstep all_less (set (E @ R)))\<inverse>)\<^sup>*"
    by auto
  then have
    su: "(s, u) \<in> (rstep (set (E @ R)))\<^sup>*" and
    uv: "(u, v) \<in> (rstep (set (E @ R)))\<^sup>*" and
    vt: "(v, t) \<in> ((rstep (set (E @ R)))\<inverse>)\<^sup>*"
    using ordstep_imp_rstep[of _ _ all_less "(set (E @ R))"]
          rtrancl_mono[of "ordstep all_less (set (E @ R))" "rstep (set (E @ R))"]
          ordstep_imp_rstep[of _ _ all_less "(set (E @ R))\<inverse>"]
          rtrancl_mono[of "(ordstep all_less (set (E @ R)))\<inverse>" "(rstep (set (E @ R)))\<inverse>"]
    unfolding subset_iff apply auto by blast
  then have
    su: "(s, u) \<in> (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*" and 
    uv: "(u, v) \<in> (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*" and
    vt: "(v, t) \<in>  (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*"
      apply auto by (metis conversionI' rtrancl_converseD sym_esteps_pair)
  then have "(s, t) \<in> (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>* O (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>* O (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*"
    by blast
  then show ?thesis by simp
qed

lemma mord_rewrite_complete:
  assumes "(s, t) \<in> mordstep least all_less (set R)" 
  shows "t \<in> set (mord_rewrite R s)"
proof -
  from assms obtain  l r C \<sigma> where
    step:"(l, r) \<in> set R" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>"
    "\<forall>x\<in>vars_term r - vars_term l. \<sigma> x = Fun least []" unfolding mordstep.simps by auto
  let ?p = "hole_pos C"
  from subt_at_hole_pos step(2) have "l \<cdot> \<sigma> = s |_ (hole_pos C)" by auto
  from Matching.match_complete'[OF this] obtain \<tau> where
    \<tau>:"Matching.match (s |_ ?p) l = Some \<tau>" "\<forall>x\<in>vars_term l. \<sigma> x = \<tau> x" by auto
  have l:"l \<cdot> ext_subst \<tau> l = l \<cdot> \<sigma>"
    unfolding ext_subst_def by (rule term_subst_eq, insert \<tau>(2), auto)
  have r:"r \<cdot> ext_subst \<tau> l = r \<cdot> \<sigma>"
    unfolding ext_subst_def by (rule term_subst_eq, insert \<tau>(2) step(5), auto)
  from step(4) have less:"l \<cdot> ext_subst \<tau> l \<succ> r \<cdot> ext_subst \<tau> l" unfolding l r by auto
  with step(3) r have *:"t \<in> set (case (Matching.match (s |_ ?p) l) of None \<Rightarrow> []
      | Some \<sigma> \<Rightarrow> (let \<sigma>' = ext_subst \<sigma> l in (if l \<cdot> \<sigma>' \<succ> r \<cdot> \<sigma>' then [(ctxt_of_pos_term ?p s)\<langle>r \<cdot> \<sigma>'\<rangle>] else [])))"
    unfolding \<tau>(1) Let_def by (simp, unfold step(2) ctxt_of_pos_term_hole_pos, simp)
  from step hole_pos_poss have p:"?p \<in> poss s" by auto
  with * step(1) show ?thesis unfolding mord_rewrite.simps by fastforce
qed

lemma compute_mordstep_NF_complete:
  assumes res: "compute_mordstep_NF R s = Some t"
    and *: "all_less \<subseteq> {(x, y). less' x y}"
    and ro:"reduction_order less"
    and rox:"reduction_order less'"
    and fground: "\<forall>s t. Reduction_Order.fground F s \<and> Reduction_Order.fground F t \<longrightarrow> s = t \<or> less s t \<or> less t s"
    and min: "\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun least [])"
    and F: "(least, 0) \<in> F" "funas_trs (set R) \<subseteq> F" and Ft:"Reduction_Order.fground F t"
  shows "t \<in> NF (GROUND (ordstep all_less (set R)))"
proof -
  let ?fground = "Reduction_Order.fground"
  let ?mordstep = "mordstep least all_less (set R)"
  from res[unfolded compute_mordstep_NF_def]
  have "t \<in> NF (FGROUND F ?mordstep)" proof(rule compute_NF_complete)
    fix s
    assume "first_mord_rewrite R s = None"
    from this[unfolded first_mord_rewrite_def] have empty: "mord_rewrite R s = []" 
      by (cases "mord_rewrite R s", auto)
    hence empty:"\<And>t. t \<notin> set (mord_rewrite R s)" by auto
    have "s \<in> NF ?mordstep"
      by (rule, insert mord_rewrite_complete[of s _ R] empty, blast)
    with NF_anti_mono[of "FGROUND F ?mordstep" ?mordstep ] show NF:"s \<in> NF (FGROUND F ?mordstep)"
      using FGROUND_def by auto
  qed
  note nf' = reduction_order.suborder_mordstep_NF[OF rox * ro fground min F Ft this]
  with NF_anti_mono[OF GROUND_mono[OF ordstep_mono[OF subset_refl *, of "set R"]]] show ?thesis
    by blast
qed
end

\<comment> \<open>All possible ways to insert a single element into a list\<close>
fun inserts :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
    "inserts x [] = [[x]]"
  | "inserts x (y # ys) = (x # y # ys) # map ((#) y) (inserts x ys)"

\<comment> \<open>\<open>ins xs y zs\<close> holds if \<open>xs\<close> results from inserting \<open>y\<close> into \<open>zs\<close> at an arbitrary position.\<close>
inductive ins :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    "x = y \<Longrightarrow> ins (y # ys) x ys"
  | "y = z \<Longrightarrow> ins ys x zs \<Longrightarrow> ins (y # ys) x (z # zs)"

lemma ins_Cons [simp]:
  "ins (y # ys) x (y # zs) \<longleftrightarrow> ins ys x zs"
  by (auto elim: ins.cases intro: ins.intros)

lemma in_set_inserts_iff:
  "ys \<in> set (inserts x zs) \<longleftrightarrow> ins ys x zs"
  by (induct zs arbitrary: ys) (auto intro: ins.intros elim: ins.cases)

lemma ins_mset [simp]:
  assumes "ins ys x zs"
  shows "mset ys = add_mset x (mset zs)"
  using assms by (induct) auto

lemma ins_remove1I:
  assumes "x \<in> set xs"
  shows "ins xs x (remove1 x xs)"
  using assms by (induct xs) (auto intro: ins.intros)

lemma mset_insE:
  assumes "mset xs = add_mset y (mset ys)"
  obtains zs where "mset zs = mset ys" and "ins xs y zs"
  using assms
proof (induct xs arbitrary: ys thesis)
  case (Cons x xs)
  show ?case
  proof (cases "x = y")
    assume "x = y"
    then show ?thesis using Cons by (auto intro: ins.intros)
  next
    case False
    with Cons.prems have *: "mset (x # remove1 y xs) = mset ys" and "y \<in> set xs"
      by (auto simp: diff_union_swap) (meson in_multiset_in_set insert_noteq_member)
    then show ?thesis
      by (intro Cons.prems(1) [OF *]) (auto intro: ins_remove1I)
  qed
qed simp

fun perms :: "'a list \<Rightarrow> 'a list list"
  where
    "perms [] = [[]]"
  | "perms (x#xs) = concat (map (inserts x) (perms xs))"

lemma perms [simp]:
  "set (perms xs) = {ys. mset ys = mset xs}"
  by (induct xs) (fastforce simp: in_set_inserts_iff elim: mset_insE)+

lemma maximal_element:
  assumes "Relation.total_on (X::'a set) rel" and "wf rel" and "X \<noteq> {}"
  shows "\<exists>x \<in> X. (\<forall>y \<in> X. x \<noteq> y \<longrightarrow> (x,y) \<in> rel)"
proof -
  from assms(2)[unfolded wf_iff_no_infinite_down_chain] have wf:"\<nexists>f. \<forall>i. (f (Suc i), f i) \<in> rel"
    by auto
  let ?P = "\<lambda>x y. y \<in> X \<and> x \<noteq> y \<and> (y,x) \<in> rel"
  { assume "\<forall>x \<in> X. (\<exists>y \<in> X. x \<noteq> y \<and> (x, y) \<notin> rel)"
    with assms(1) Relation.total_on_def have a:"\<And>x. x \<in> X \<Longrightarrow> (\<exists>y. ?P x y)" by metis
    from assms(3) obtain x where x:"x \<in> X" by blast
    let ?smaller = "(\<lambda>x. SOME y. ?P x y)"
    define f where "f n = (?smaller ^^ n) x" for n
    have in_X:"f n \<in> X" for n proof(induct n, simp add: f_def x)
      case (Suc n)
      define y where "y \<equiv> (?smaller ^^ n) x"
      from Suc[unfolded f_def, folded y_def, THEN a[of y]] show ?case
        unfolding f_def using someI_ex[of "?P y"] y_def
        by (meson a assms(2) wfE_min)
    qed
    have "(f (Suc i), f i) \<in> rel" for i proof(induct i, simp add: someI_ex[OF a[OF x]] f_def)
      case (Suc i)
      define yy where "yy \<equiv> ?smaller ((?smaller ^^ i) x)"
      hence "yy = f (Suc i)" unfolding f_def by auto
      with in_X have "yy \<in> X" by auto
      from someI_ex[OF a[OF this]] show ?case
        unfolding f_def funpow.simps(2) comp_def yy_def[symmetric] by simp
    qed
    with assms(2) wf_iff_no_infinite_down_chain have False by blast
  }
  thus ?thesis by auto
qed

definition "order_set_of_perm p = {(x,y) | x y. \<exists>i j. i < j \<and> j < length p \<and> p ! i = x \<and> p ! j = y}"

primrec order_set_of_permx where
  "order_set_of_permx [] = {}"
| "order_set_of_permx (x # xs) = set (map (\<lambda>y. (x,y)) xs) \<union> order_set_of_permx xs"

export_code order_set_of_permx

lemma order_set_of_permx:"order_set_of_perm p = order_set_of_permx p"
proof(induct p, simp add:order_set_of_perm_def)
  case (Cons x xs)
  { fix y z
    assume a:"(y,z) \<in> order_set_of_perm (x # xs)"
    then obtain i j where ij:"i < j" "j < length (x # xs)" "(x # xs) ! i = y" "(x # xs) ! j = z"
      unfolding order_set_of_perm_def by blast
    then obtain k where j:"j = Suc k" by (cases j, auto)
    with ij have xs_k:"xs ! k = z" "k < length xs" by auto
    have "(y,z) \<in> order_set_of_permx (x # xs)" proof (cases "i = 0")
      case True
      with ij have yx:"y = x" by auto
      then show ?thesis unfolding order_set_of_permx.simps using xs_k by auto
    next
      case False
      then obtain m where i:"i = Suc m" by (cases i, auto)
      with ij j have xs_m:"xs ! m = y" "m < k" by auto
      with xs_k have mk:"m < k" "k < length xs" "xs ! m = y" "xs ! k = z" by auto
      hence "(y,z) \<in> order_set_of_perm xs" unfolding order_set_of_perm_def by auto
      then show ?thesis using Cons by auto
    qed
  } note lr = this
  { fix y z
    assume a:"(y,z) \<in> order_set_of_permx (x # xs)"
    have "(y,z) \<in> order_set_of_perm (x # xs)" proof (cases "(y,z) \<in> order_set_of_permx xs")
      case True
      with Cons have "(y,z) \<in> order_set_of_perm xs" by auto
      then obtain i j where ij:"i < j" "j < length xs" "xs ! i = y" "xs ! j = z"
        unfolding order_set_of_perm_def by blast
      hence "Suc i < Suc j" "Suc j < length (x # xs)" "(x # xs) ! (Suc i) = y" "(x # xs) ! (Suc j) = z"
        by auto
      then show ?thesis unfolding order_set_of_perm_def by blast
    next
      case False
      with a have dec:"y = x" "z \<in> set xs" unfolding order_set_of_permx.simps by auto
      then obtain j where "j < length xs" "xs ! j = z" unfolding set_conv_nth by auto
      with dec have "0 < Suc j \<and> Suc j < length (x # xs) \<and> (x # xs) ! 0 = y \<and> (x # xs) ! (Suc j) = z" by simp
      then show ?thesis unfolding order_set_of_perm_def by blast
    qed
  }
  with lr show ?case by auto
qed


lemma all_perms_all_total_wf_rels:
  assumes "distinct xs" and "\<And>p. p \<in> set (perms xs) \<Longrightarrow> P (order_set_of_perm p)"
  shows "\<And>ord. (Relation.total_on (set xs) ord \<Longrightarrow> wf (ord\<inverse>) \<Longrightarrow> trans ord \<Longrightarrow> P (ord \<restriction> (set xs)))"
proof -
  { fix ord
    assume total:"Relation.total_on (set xs) ord" and wf:"wf (ord\<inverse>)" and trans:"trans ord"
    from total have "\<exists>p. set xs = set p \<and> sorted_wrt (\<lambda>x y. (x,y) \<in> ord) p \<and> distinct p"
    proof(induct "length xs" arbitrary: xs rule: less_induct)
      case less
      show ?case proof (cases "length xs")
        case 0
        show ?thesis by (rule exI[of _ "[]"], insert 0, auto)
      next
        case (Suc n)
        hence ne:"set xs \<noteq> {}" by auto
        from less(2) total_on_converse have "Relation.total_on (set xs) (ord\<inverse>)" by auto
        from maximal_element[OF this wf ne] obtain x where
          x:"x \<in> set xs" "\<forall>y\<in>set xs. x \<noteq> y \<longrightarrow> (y, x) \<in> ord" by auto
        let ?ys = "removeAll x xs"
        have len:"length ?ys < length xs" using length_removeAll_less[OF x(1)] by force
        have subset:"set ?ys \<subseteq> set xs" by auto
        have "\<And>X Y. Y \<subseteq> X \<Longrightarrow> Relation.total_on X ord \<Longrightarrow> Relation.total_on Y ord"
          unfolding Relation.total_on_def by auto
        with less(2) subset have "Relation.total_on (set ?ys) ord" by metis
        from less(1)[OF len this] obtain p where
          p:"set ?ys = set p" "sorted_wrt (\<lambda>x y. (x, y) \<in> ord) p" "distinct p" by auto
        from set_removeAll have no_x:"x \<notin> set ?ys" by simp
        with p(1) x(2) have x_gt:"\<forall>y\<in>set p. (y, x) \<in> ord" by force
        with p(2) have sorted:"sorted_wrt (\<lambda>x y. (x, y) \<in> ord) (p @ [x])"
          by (simp add: sorted_wrt_append)
        from no_x p have distinct:"distinct (p @ [x])" by auto
        show ?thesis by (rule exI[of _ "p @ [x]"], insert sorted distinct p(1) x(1), auto)
      qed
    qed
    then obtain p where p:"set xs = set p" "sorted_wrt (\<lambda>x y. (x,y) \<in> ord) p" "distinct p" by auto
    with set_eq_iff_mset_eq_distinct assms(1) have "mset xs = mset p" by auto
    with perms have p_perms:"p \<in> set (perms xs)" by auto
    have restr:"ord \<restriction> (set xs) = {(x, y). \<exists>i < length p. \<exists>j < length p. x = p ! i \<and> y = p ! j \<and> (x, y) \<in> ord}"
      unfolding p(1) in_set_conv_nth Abstract_Rewriting.restrict_def by auto
    note p_sorted = p(2)[unfolded sorted_wrt_iff_nth_less, rule_format]
    note acyclic = wf_acyclic[OF wf, unfolded acyclic_converse, unfolded acyclic_def]
    have "\<And>i j. (i < j \<and> j < length p) = (i<length p \<and> j<length p \<and> (p ! i, p ! j) \<in> ord)" proof
      fix i j
      assume "i < j \<and> j < length p"
      with p_sorted show "i < length p \<and> j < length p \<and> (p ! i, p ! j) \<in> ord" by auto
    next
      fix i j
      assume a:"i < length p \<and> j < length p \<and> (p ! i, p ! j) \<in> ord"
      { assume leq:"j \<le> i"
        from a have ij:"(p ! i, p ! j) \<in> ord" by auto
        with acyclic leq have lt:"j < i" by (cases "i = j", auto)
        from p_sorted[OF this] a trans[unfolded trans_def, rule_format, OF ij] acyclic have False by auto
      }
      with a show "i < j \<and> j < length p" by force
    qed
    then have "order_set_of_perm p = ord \<restriction> (set xs)" unfolding order_set_of_perm_def restr by auto 
    with p_perms have "\<exists>\<pi>. \<pi> \<in> set (perms xs) \<and> order_set_of_perm \<pi> = ord \<restriction> set xs" by auto
  }
  with assms(2) show "\<And>ord. (Relation.total_on (set xs) ord \<Longrightarrow> wf (ord\<inverse>) \<Longrightarrow> trans ord \<Longrightarrow> P (ord \<restriction> (set xs)))" by metis
qed

definition "equiv_of_partitioning ps = {(x,y) | x y. \<exists>p \<in> ps. x \<in> p \<and> y \<in> p}"

definition "partitioning_of_equiv X rel = {rel `` {x} |x. x \<in> X}"

declare equiv_of_partitioning_def[code]

lemma partitioning_of_equiv_non_overlapping:
  assumes equiv:"equiv X rel" and "p \<in> partitioning_of_equiv X rel"
  and "q \<in> partitioning_of_equiv X rel" and inter:"p \<inter> q \<noteq> {}"
  shows "p = q"
proof -
  from assms obtain x y where xy:"p = rel `` {x}" "q = rel `` {y}" "x \<in> X" "y \<in> X"
    unfolding partitioning_of_equiv_def by auto
  with inter obtain z where "(x,z) \<in> rel" "(y,z) \<in> rel" by auto
  with equiv[unfolded equiv_def sym_def trans_def] have "(x,y) \<in> rel" by blast
  with equiv_class_eq[OF equiv this] xy show "p = q" by auto
qed

lemma all_partitions_all_equiv_rels:
  assumes "\<And>p. p \<in> all_partitions X \<Longrightarrow> P (equiv_of_partitioning p)"
  shows "\<And>rel. (equiv X rel \<Longrightarrow> P rel)"
proof -
  fix rel
  assume equiv:"equiv X rel"
  hence [simp]:"rel \<restriction> X = rel" unfolding equiv_def refl_on_def by auto
  let ?ps = "partitioning_of_equiv X rel"
  { fix x y
    assume "(x,y) \<in> equiv_of_partitioning ?ps"
    then obtain p where "p \<in> ?ps" "x \<in> p \<and> y \<in> p" unfolding equiv_of_partitioning_def by blast
    from this equiv_class_eq_iff[OF equiv] have "(x,y) \<in> rel"
      unfolding partitioning_of_equiv_def restrict_def mem_Collect_eq by blast
  } note subset = this
  { fix x y
    assume "(x,y) \<in> rel \<restriction> X"
    with equiv have "x \<in> rel `` {x}" and "y \<in> rel `` {x}" and "x \<in> X"
      unfolding equiv_def refl_on_def by auto
    then have "(x,y) \<in> equiv_of_partitioning ?ps"
      unfolding equiv_of_partitioning_def mem_Collect_eq partitioning_of_equiv_def by auto
  }
  with subset have ps_to_rel:"equiv_of_partitioning ?ps = rel" by auto
  from equiv[unfolded equiv_def refl_on_def] have nonempty:"\<And>p. p \<in> ?ps \<Longrightarrow> p \<noteq> {}" and Un:"\<Union>?ps = X"
    unfolding partitioning_of_equiv_def by auto
  from partitioning_of_equiv_non_overlapping[OF equiv] nonempty have "is_non_overlapping ?ps"
    unfolding is_non_overlapping_def by auto
  with Un have "?ps \<in> all_partitions X" unfolding all_partitions_def is_partition_of_def by auto
  from ps_to_rel assms[OF this] show "P rel" by auto
qed

definition var_rel_of_partitioning where
  "var_rel_of_partitioning ps = \<Union>{case sorted_list_of_set p of [] \<Rightarrow> {} | Cons x xs \<Rightarrow> {(y,x) |y. y \<in> set (Cons x xs)} |p. p \<in> ps}"

export_code var_rel_of_partitioning

definition var_tuples_of_partitioning where
  "var_tuples_of_partitioning ps = 
  concat (map (\<lambda>p. case sorted_list_of_set p of [] \<Rightarrow> [] | Cons x xs \<Rightarrow> map (\<lambda>y. (y, x)) (Cons x xs)) (remdups ps))"

export_code var_tuples_of_partitioning

definition "term_order_of_perm p = {(Var x, Var y) |x y. (x,y) \<in> order_set_of_perm p}"

definition "term_order_of_permx p = {(Var x, Var y) |x y. (x,y) \<in> order_set_of_permx p}"

locale moc_closure_ops = moc_ops check_ord least
  for check_ord :: "('a::showl, 'v::{showl, linorder, infinite}) term \<Rightarrow> ('a,'v) term \<Rightarrow> bool"
  and least :: "'a" +
  fixes xvar yvar :: "'v \<Rightarrow> 'v"
  and ext_check_ord :: "'v list \<Rightarrow> ('a, 'v) term \<Rightarrow> ('a, 'v) term \<Rightarrow> bool"
begin

definition "check_var_order_joinable E R s t vperm =
  (moc_ops.check_instance_joinable (ext_check_ord vperm) least E R s t)"

definition "var_subst_of_partitioning p \<equiv>
  (\<lambda>x. case map_of (var_tuples_of_partitioning p) x of Some y \<Rightarrow> y | _ \<Rightarrow> x)"

definition "subst_of_partitioning p \<equiv> (\<lambda>x. Var (var_subst_of_partitioning p x))"

definition check_var_orders_joinable
  where "check_var_orders_joinable E R s t =
 (let xs = remdups (vars_rule_impl (s,t)) in
  check_allm (\<lambda>ps.
    let \<sigma> = subst_of_partitioning ps in
    let (s', t') = (s \<cdot> \<sigma>, t \<cdot> \<sigma>) in
    let orders = perms (remdups (vars_rule_impl (s', t'))) in
    check_allm (check_var_order_joinable E R s' t') orders) (all_partitions_list xs))"
end

lemmas [code] =
  moc_closure_ops.var_subst_of_partitioning_def
  moc_closure_ops.subst_of_partitioning_def
  moc_closure_ops.check_var_order_joinable_def
  moc_closure_ops.check_var_orders_joinable_def

locale moc_closure_spec =
  moc_spec check_ord least F +
  moc_closure_ops check_ord least xvar yvar ext_check_ord +
  fgtotal_reduction_order_inf less UNIV
  for less :: "('a::showl, 'v::{showl, linorder, infinite}) term \<Rightarrow> ('a,'v) term \<Rightarrow> bool" (infix "\<succ>" 50)
  and check_ord :: "('a, 'v) term \<Rightarrow> ('a, 'v) term \<Rightarrow> bool"
  and least :: "'a"
  and F :: "('a \<times> nat) set"
  and xvar yvar :: "'v \<Rightarrow> 'v"
  and ext_check_ord :: "'v list \<Rightarrow> ('a, 'v) term \<Rightarrow> ('a, 'v) term \<Rightarrow> bool" +
  fixes \<C> :: "('a, 'v) term rel \<Rightarrow> ('a, 'v) term rel"
  assumes C_compatible:"\<C> {\<succ>} \<subseteq> {\<succ>}"
  and C_cond:"\<And>ord. (s, t) \<in> \<C> ord \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> \<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> ord}"
  and C_mono:"\<And>ord ord'. ord \<subseteq> ord' \<Longrightarrow> \<C> ord \<subseteq> \<C> ord'"
  and ext_check_ord:"\<And>s t p. ext_check_ord p s t \<longrightarrow> (s,t) \<in> \<C> (term_order_of_perm p)"
  and ext_least:"\<And>p. ((\<forall>t. (fground F t \<longrightarrow> t = Fun least [] \<or> t \<succ> Fun least [])) \<longrightarrow>
                  (\<forall>t. (fground F t \<longrightarrow> t = Fun least [] \<or> ext_check_ord p t (Fun least []))))"
  and ord_subset:"\<And>s t. check_ord s t \<Longrightarrow> s \<succ> t"
begin

abbreviation "mk_closure \<equiv> \<lambda>vord s t. (s,t) \<in> \<C> {(Var x, Var y) |x y. (x,y) \<in> vord}"

definition repr where "repr X \<rho> =
  (\<lambda>x. SOME y. (x,y) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>))"

lemma partitioning_of_equiv_subset: "equiv X \<rho> \<Longrightarrow> p \<in> partitioning_of_equiv X \<rho> \<Longrightarrow> p \<subseteq> X" 
  unfolding equiv_def partitioning_of_equiv_def refl_on_def by auto

lemma partitioning_of_equiv_rel: "equiv X \<rho> \<Longrightarrow> p \<in> partitioning_of_equiv X \<rho> \<Longrightarrow> x \<in> p \<Longrightarrow> y \<in> p \<Longrightarrow> (x,y) \<in> \<rho>" 
  unfolding equiv_def partitioning_of_equiv_def sym_def trans_def Image_def by blast

abbreviation "rule_repr rl \<equiv> repr (vars_rule rl)"

lemma partition_of_equiv_non_empty:"equiv X \<rho> \<Longrightarrow> q \<in> partitioning_of_equiv X \<rho> \<Longrightarrow> q \<noteq> {}"
  unfolding partitioning_of_equiv_def equiv_def refl_on_def by auto

lemma partition_of_equiv_non_Nil:
  assumes equiv:"equiv X \<rho>" and f:"finite X" and q:"q \<in> partitioning_of_equiv X \<rho>"
  shows "sorted_list_of_set q \<noteq> []"
  using partitioning_of_equiv_subset[OF equiv q, THEN finite_subset[OF _ f]] sorted_list_of_set_eq_Nil_iff[of q]
  partition_of_equiv_non_empty[OF equiv q] by auto

abbreviation ps where
  "ps \<equiv> (\<lambda>p ::'v set. case sorted_list_of_set p of [] \<Rightarrow> [] | x # xs \<Rightarrow> map (\<lambda>y. (y, x)) (x # xs))"

lemma part_inj:
  assumes ne:"\<And>p. p \<in> \<rho> \<Longrightarrow> p \<noteq> {}" and finp:"\<And>p. p \<in> \<rho> \<Longrightarrow> finite p"
  shows "inj_on (map fst \<circ> ps) \<rho>"
proof -
  let ?ps = "\<lambda>p::'v set. case sorted_list_of_set p of [] \<Rightarrow> [] | x # xs \<Rightarrow> map (\<lambda>y. (y, x)) (x # xs)"
  let ?l = "(map fst \<circ> ?ps) ` \<rho>"
  show "inj_on (map fst \<circ> ps) \<rho>"
  proof
    fix p q
    assume in_rho:"p \<in> \<rho>" "q \<in> \<rho>" and eq:"(map fst \<circ> ?ps) p = (map fst \<circ> ?ps) q"
    note sets = set_sorted_list_of_set[OF finp[OF in_rho(1)]] set_sorted_list_of_set[OF finp[OF in_rho(2)]]
    hence inj:"sorted_list_of_set p = sorted_list_of_set q \<Longrightarrow> p = q" by metis
    note eq = eq[unfolded comp_def]
    from ne[OF in_rho(1)] sets obtain p0 ps where
      sp:"sorted_list_of_set p = p0 # ps" by (cases "sorted_list_of_set p", auto)
    from ne[OF in_rho(2)] sets obtain q0 qs where
      sq:"sorted_list_of_set q = q0 # qs" by (cases "sorted_list_of_set q", auto)
    from eq inj show "p = q" unfolding sp sq list.case map_map comp_def fst_conv by auto
  qed
qed

lemma repr_rel:
  assumes fin:"finite (X :: 'v set)" and inX:"x \<in> X" and equiv:"equiv X \<rho>"
  shows "(x, repr X \<rho> x) \<in> \<rho> \<and> repr X \<rho> x \<in> X \<and> (\<forall>y. (x,y) \<in> \<rho> \<longrightarrow> repr X \<rho> x = repr X \<rho> y)"
proof -
  from assms obtain p where p:"p \<in> partitioning_of_equiv X \<rho>" "x \<in> p"
    unfolding partitioning_of_equiv_def equiv_def refl_on_def by auto
  from partitioning_of_equiv_subset[OF equiv p(1)] fin finite_subset have "finite p" by auto
  from partition_of_equiv_non_Nil[OF equiv fin p(1)] have ne:"sorted_list_of_set p \<noteq> []" by auto
  let ?ppairs = "\<lambda>p. (case sorted_list_of_set p of [] \<Rightarrow> {} | x # xs \<Rightarrow> {(y, x) |y. y \<in> set (x # xs)})"
  note set_sort = set_sorted_list_of_set[OF \<open>finite p\<close>]
  with p have "x \<in> set (sorted_list_of_set p)" by auto
  then obtain y ys where y:"(x, y) \<in> ?ppairs p" "sorted_list_of_set p = y # ys"
    using p ne by (cases "sorted_list_of_set p", auto)
  with p(2) ne set_sort have yp:"y \<in> p" by (cases "sorted_list_of_set p", auto)
  from y have ex:"(x, y) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>)"
    using p(1) unfolding var_rel_of_partitioning_def by auto
  note xy = partitioning_of_equiv_rel[OF equiv p yp]
  { fix x
    assume ex:"(x, y) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>)" and xp:"x \<in> p"
    define yy where "yy \<equiv> SOME y. (x, y) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>)"
    from someI_ex ex have "(x, yy) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>)"
      unfolding yy_def by metis
    from this[unfolded var_rel_of_partitioning_def] obtain q where
      q:"(x, yy) \<in> ?ppairs q" "q \<in> partitioning_of_equiv X \<rho>" by auto
    from partition_of_equiv_non_Nil[OF equiv fin q(2)] have ne:"sorted_list_of_set q \<noteq> []" by auto
    from partitioning_of_equiv_subset[OF equiv q(2)] fin finite_subset have fq:"finite q" by auto
    from set_sorted_list_of_set[OF fq] q ne have x_in_q:"x \<in> q" by (cases "sorted_list_of_set q", auto)
    from ne set_sorted_list_of_set[OF fq] q(1) obtain yys where yys:"sorted_list_of_set q = yy # yys"
      by (cases "sorted_list_of_set q", auto)
    from x_in_q xp partitioning_of_equiv_non_overlapping[OF equiv p(1) q(2)] have pq:"p = q" by auto
    from yys y(2) have "repr X \<rho> x = y" unfolding repr_def yy_def pq by auto
  } note repr_p = this
  with ex p have rxy:"repr X \<rho> x = y" by auto
  { fix z
    assume a:"(x,z) \<in> \<rho>"
    with assms have z:"z \<in> X" "(z,x) \<in> \<rho>"
      unfolding partitioning_of_equiv_def equiv_def refl_on_def sym_def by auto
    with a p have zp:"z \<in> p" unfolding partitioning_of_equiv_def
      using equiv equiv_class_eq_iff by fastforce
    with set_sort p have "z \<in> set (sorted_list_of_set p)" by auto
    hence zpp:"(z, y) \<in> ?ppairs p" using zp ne y by (cases "sorted_list_of_set p", auto)
    then have ex:"(z, y) \<in> var_rel_of_partitioning (partitioning_of_equiv X \<rho>)"
      using p(1) unfolding var_rel_of_partitioning_def by auto
    with repr_p zp have "repr X \<rho> z = y" by auto
  }
  with xy \<open>y \<in> p\<close> \<open>p \<subseteq> X\<close> show ?thesis unfolding rxy by blast
qed

lemma equiv_equiv_of_partitioning:
  assumes \<rho>:"\<rho> partitions X"
  shows "equiv X (equiv_of_partitioning \<rho>)"
proof -
  from assms have part:"\<Union>\<rho> = X" "is_non_overlapping \<rho>"
    unfolding is_partition_of_def by auto
  with \<rho> have refl:"refl_on X (equiv_of_partitioning \<rho>)"
    unfolding equiv_of_partitioning_def refl_on_def by auto
  from part \<rho> have sym:"sym (equiv_of_partitioning \<rho>)"
    unfolding equiv_of_partitioning_def sym_def by auto
  from part(1) have "\<forall>x y z. (\<exists>p\<in>\<rho>. x \<in> p \<and> y \<in> p) \<longrightarrow> (\<exists>p\<in>\<rho>. y \<in> p \<and> z \<in> p) \<longrightarrow> (\<exists>p\<in>\<rho>. x \<in> p \<and> z \<in> p)"
    unfolding trans_def mem_Collect_eq prod.inject using elem_in_uniq_set[OF _ \<rho>] by auto
  hence "trans (equiv_of_partitioning \<rho>)"
    unfolding equiv_of_partitioning_def trans_def mem_Collect_eq prod.inject by meson
  with refl sym show ?thesis unfolding equiv_def by auto
qed

abbreviation "instance_join ord R \<equiv> (ordstep ord R)\<^sup>* O rstep R O ((ordstep ord R)\<inverse>)\<^sup>*"

lemma partitioning_of_equiv_equiv_of_partitioning:
  assumes "\<rho> partitions X" and "X \<noteq> {}"
  shows "partitioning_of_equiv X (equiv_of_partitioning \<rho>) = \<rho>"
proof -
  note equiv = equiv_equiv_of_partitioning[OF assms(1), unfolded equiv_def]
  {fix p
    assume a:"p \<in> partitioning_of_equiv X (equiv_of_partitioning \<rho>)"
    then obtain x where x:"x \<in> X" "p = equiv_of_partitioning \<rho> `` {x}"
      unfolding partitioning_of_equiv_def by blast
    from x(2)[unfolded equiv_of_partitioning_def Image_def mem_Collect_eq]
    have p_set:"p = {y. (\<exists>p\<in>\<rho>. x \<in> p \<and> y \<in> p)}" by simp 
    with x have pX:"p \<subseteq> X"
      using a assms equiv_equiv_of_partitioning partitioning_of_equiv_subset by blast
    from pX p_set have "p \<in> \<rho>" using elem_in_uniq_set[OF _ assms(1), OF x(1)]
      by (smt mem_Collect_eq set_eq_subset subset_eq)
  } note lr = this
  { fix p
    assume a:"p \<in> \<rho>"
    with assms obtain x where x:"x \<in> p" unfolding is_partition_of_def is_non_overlapping_def by auto
    with a assms(1) have xX:"x \<in> X" unfolding is_partition_of_def by auto
    note ep = equiv_equiv_of_partitioning[OF assms(1)]
    have "p = {y. (\<exists>p\<in>\<rho>. x \<in> p \<and> y \<in> p)}" using elem_in_uniq_set[OF _ assms(1), OF xX] x a by blast
    hence "p = {b. (x, b) \<in> equiv_of_partitioning \<rho>}"
      unfolding equiv_of_partitioning_def mem_Collect_eq by auto
    with ep xX have "p \<in> partitioning_of_equiv X (equiv_of_partitioning \<rho>)"
      unfolding partitioning_of_equiv_def Image_singleton mem_Collect_eq by auto
  }
  with lr show ?thesis by auto
qed

lemma partition_finite:
  assumes "(set \<rho>) partitions X" and "finite X" and "p \<in> set \<rho>"
  shows "finite p"
proof -
  from assms(1)[unfolded is_partition_of_def is_non_overlapping_def] have UX:"\<Union>(set \<rho>) = X" by auto
  with assms finite_UnionD[of "set \<rho>"] show"finite p" by (metis Sup_insert Un_infinite insert_absorb)
qed

sublocale gtotal_reduction_order_inf_closure less UNIV \<C> repr
  by (unfold_locales, insert repr_rel C_cond C_mono C_compatible, auto)

lemma subst_of_partitioning:
  assumes x_in_X:"x \<in> (X :: 'v set)" and "(set \<rho>) partitions X"
  and fin:"finite X"
  shows "subst_of_partitioning \<rho> x = hat X (equiv_of_partitioning (set \<rho>)) x"
proof -
  note hat = hat_def[of X]
  from assms have neX:"X \<noteq> {}" by auto
  note uniq = elem_in_uniq_set[OF assms(1) assms(2)]
  then obtain p where p:"p \<in> set \<rho>" "x \<in> p" "\<And>q. q \<in> set \<rho> \<and> x \<in> q \<Longrightarrow> q = p" by auto
  note fin = partition_finite[OF assms(2) assms(3)]
  with assms(2) have ne:"\<And>p. p \<in> set \<rho> \<Longrightarrow> p \<noteq> {}" unfolding is_partition_of_def is_non_overlapping_def by auto
  with assms(2) have subset:"\<And>p. p \<in> set \<rho> \<Longrightarrow> p \<subseteq> X" unfolding is_partition_of_def is_non_overlapping_def by auto
  let ?l = "sorted_list_of_set p"
  from p(2) have "x \<in> set ?l" unfolding set_sorted_list_of_set[OF fin[OF p(1)]] by auto 
  then obtain y ys where y:"?l = y # ys" "x \<in> set (y # ys)" by (cases ?l, auto)
  define ps where "ps \<equiv> \<lambda>p::'v set. case sorted_list_of_set p of [] \<Rightarrow> [] | x # xs \<Rightarrow> map (\<lambda>y. (y, x)) (x # xs)"
  from y(2) have "(x,y) \<in> set (ps p)" unfolding y list.cases ps_def by auto
  with p(1) have in_set:"(x,y) \<in> set (concat (map ps (remdups \<rho>)))" unfolding set_concat set_map by auto
  have eq:"map fst (concat (map ps (remdups \<rho>))) = (concat (map (map fst \<circ> ps) (remdups \<rho>)))"
    unfolding map_concat map_map by auto
  let ?l = "map (map fst \<circ> ps) (remdups \<rho>)"
  from part_inj[OF ne fin] have d1:"distinct ?l" unfolding distinct_map ps_def by simp
    let ?S = "set (map (map fst \<circ> ps) (remdups \<rho>))"
    have "distinct (map fst (concat (map ps (remdups \<rho>))))"
      unfolding eq proof(rule distinct_concat, simp add:d1)
      fix ys
      assume a:"ys \<in> ?S"
      then obtain p where p:"p \<in> set \<rho>" "ys = (map fst \<circ> ps) p" by auto
      from ne[OF p(1)] set_sorted_list_of_set[OF fin[OF p(1)]] obtain p0 ps where
        sp:"sorted_list_of_set p = p0 # ps" by (cases "sorted_list_of_set p", auto)
      from p(2)[unfolded ps_def comp_def sp list.case map_map] have "ys = p0 # ps" by auto
      with sp linorder_class.distinct_sorted_list_of_set show "distinct ys" by metis
    next
      fix ys zs
      assume a:"ys \<in> ?S" "zs \<in> ?S" "ys \<noteq> zs"
      from a obtain p where p:"p \<in> set \<rho>" "ys = (map fst \<circ> ps) p" by auto
      from a obtain q where q:"q \<in> set \<rho>" "zs = (map fst \<circ> ps) q" by auto
      from ne[OF p(1)] set_sorted_list_of_set[OF fin[OF p(1)]] obtain p0 ps where
        sp:"sorted_list_of_set p = p0 # ps" by (cases "sorted_list_of_set p", auto)
      from ne[OF q(1)] set_sorted_list_of_set[OF fin[OF q(1)]] obtain q0 qs where
        sq:"sorted_list_of_set q = q0 # qs" by (cases "sorted_list_of_set q", auto)
      from p(2)[unfolded ps_def comp_def sp list.case map_map] have yp:"ys = p0 # ps" by auto
      from q(2)[unfolded ps_def comp_def sq list.case map_map] have zp:"zs = q0 # qs" by auto
      note sets = set_sorted_list_of_set[OF fin[OF p(1)]] set_sorted_list_of_set[OF fin[OF q(1)]]
      hence inj:"sorted_list_of_set p = sorted_list_of_set q \<Longrightarrow> p = q" by metis
      from Int_mono[OF subset[OF p(1)] subset[OF q(1)]] have "\<And>x. x \<in> p \<inter> q \<Longrightarrow> x \<in> X" by auto
      from elem_in_uniq_set[OF this assms(2)] p(1) q(1) a(3)
      show "set ys \<inter> set zs = {}" unfolding yp zp sq[symmetric] sp[symmetric] sets by auto
    qed
  from map_of_is_SomeI[OF this in_set] have 1:"var_subst_of_partitioning \<rho> x = y"
    unfolding var_subst_of_partitioning_def var_tuples_of_partitioning_def ps_def by auto
  let ?ps = "\<lambda>p. case sorted_list_of_set p of [] \<Rightarrow> {} | x # xs \<Rightarrow> {(y, x) |y. y \<in> set (x # xs)}"
  from y(2) have "(x, y) \<in> ?ps p" unfolding y list.cases by auto
  hence xy:"(x, y) \<in> \<Union>{?ps p |p. p \<in> set \<rho>}" using p(1) by auto
  { fix z
    assume "(x, z) \<in> \<Union>{?ps p |p. p \<in> set \<rho>}"
    then obtain q where q:"q \<in> set \<rho>" "(x, z) \<in> ?ps q" by auto
    then obtain zs where zs:"sorted_list_of_set q = z # zs" "x \<in> set (z # zs)"
      by (cases "sorted_list_of_set q", auto)
    from set_sorted_list_of_set[OF fin[OF q(1)], unfolded zs] zs(2) have "x \<in> q" by auto
    with p(3)[of q] q(1) zs(1) y(1) have "z = y" by simp
  }
  with xy have "\<exists>!y. (x, y) \<in> \<Union>{?ps p |p. p \<in> set \<rho>}" by auto
  from some1_equality[OF this xy] have 2:"repr X (equiv_of_partitioning (set \<rho>)) x = y"
    unfolding repr_def var_rel_of_partitioning_def partitioning_of_equiv_equiv_of_partitioning[OF assms(2) neX] by auto
  from 1 2 show ?thesis unfolding subst_of_partitioning_def hat by auto
qed

lemma dom_ran_subst_of_partitioning:
  assumes part:"(set \<rho>) partitions X" and fin:"finite X" and x:"y \<in> subst_domain (subst_of_partitioning \<rho>)"
  shows "y \<in> X \<and> subst_of_partitioning \<rho> y \<in> Var ` X"
proof -
  note a = x[unfolded mem_Collect_eq subst_of_partitioning_def subst_domain_def]
  from a have a:"var_subst_of_partitioning \<rho> y \<noteq> y" by auto
  note a = a[unfolded var_subst_of_partitioning_def]
  with not_Some_eq have m:"map_of (var_tuples_of_partitioning \<rho>) y \<noteq> None" by fastforce
  with a obtain z where zm:"map_of (var_tuples_of_partitioning \<rho>) y = Some z" "y \<noteq> z" by force
  with map_of_SomeD have z:"(y,z) \<in> set (var_tuples_of_partitioning \<rho>)" by fast
  let ?r = "\<lambda>p. case sorted_list_of_set p of [] \<Rightarrow> [] | x # xs \<Rightarrow> map (\<lambda>y. (y, x)) (x # xs)"
  from z[unfolded var_tuples_of_partitioning_def set_concat set_map] obtain p where
    p:"p \<in> set \<rho>" "(y,z) \<in> set (?r p)" unfolding set_remdups by fast
  hence "sorted_list_of_set p \<noteq> []" by (cases, auto)
  from this[unfolded neq_Nil_conv] p obtain ps where ps:"sorted_list_of_set p = z # ps" by (cases, force+)
  from p(2) have "y \<in> set (sorted_list_of_set p)" "z \<in> set (sorted_list_of_set p)" unfolding ps list.case by auto
  with partition_finite[OF part fin p(1), THEN set_sorted_list_of_set] have "y \<in> p" "z \<in> p" by auto
  with part[unfolded is_partition_of_def] p(1) have yX:"y \<in> X \<and> z \<in> X" by auto
  hence "subst_of_partitioning \<rho> y \<in> Var ` X"
    unfolding subst_of_partitioning_def var_subst_of_partitioning_def zm(1) by auto
  with yX show ?thesis by auto
qed

lemma range_subst_of_partitioning:
  assumes part:"(set \<rho>) partitions X" and fin:"finite X"
  shows "subst_range (subst_of_partitioning \<rho> :: ('a, 'v) subst) \<subseteq> Var ` X"
  using dom_ran_subst_of_partitioning[OF assms] subst_range.simps by auto

lemma instance_join_mono:
  assumes "ord \<subseteq> ord'" and "(s,t) \<in> instance_join ord R"
  shows "(s,t) \<in> instance_join ord' R"
proof -
  from ordstep_mono[OF subset_refl assms(1)] have "(ordstep ord R)\<inverse> \<subseteq> (ordstep ord' R)\<inverse>" by simp
  from rtrancl_mono[OF this] ordsteps_mono[OF subset_refl assms(1)] assms(2) show ?thesis by blast
qed

lemma least_less:"\<forall>t. (fground F t \<longrightarrow> t = Fun least [] \<or> t \<succ> Fun least [])"
  using least ord_subset by auto

lemma check_var_orders_joinable:
  assumes "isOK(check_var_orders_joinable E R s t)"
  shows "var_order_joinable (set (E @ R)) s t"
proof -                                                
  define X where "X \<equiv> vars_rule (s,t)"
  let ?X = "remdups (vars_rule_impl (s, t))"
  define ps where "ps \<equiv> all_partitions_list ?X"
  { fix p
    assume a:"p \<in> all_partitions (vars_rule (s,t))"
    note pequiv = all_partitions_paper_equiv_alg[OF distinct_remdups, of "vars_rule_impl (s, t)"]
    note pequiv = pequiv[unfolded set_remdups set_vars_rule_impl]
    from a have \<rho>_ps:"\<exists>\<rho>. \<rho> \<in> set ps \<and> set \<rho> = p" unfolding pequiv[symmetric] set_map ps_def by auto
    define \<rho> where "\<rho> \<equiv> (SOME \<rho>. \<rho> \<in> set ps \<and> set \<rho> = p)"
    with \<rho>_ps[unfolded some_eq_ex[symmetric]] have \<rho>: "\<rho> \<in> set ps" "set \<rho> = p" by auto
    let ?\<sigma> = "subst_of_partitioning \<rho>"
    from \<rho> all_partitions_paper_equiv_alg[OF distinct_remdups] have part:"(set \<rho>) partitions (set ?X)"
      unfolding all_partitions_def ps_def by fastforce
    from equiv_equiv_of_partitioning[OF part] have equiv:"equiv (set ?X) (equiv_of_partitioning (set \<rho>))"
      by auto
    have fin:"finite (vars_rule (s, t))" unfolding vars_rule_def using finite_vars_term by simp
    let ?rho = "equiv_of_partitioning p"
    let ?\<tau> = "hat (vars_rule (s,t)) ?rho"
    define X\<^sub>\<sigma> where "X\<^sub>\<sigma> = remdups (vars_rule_impl (s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>))"
    define X\<^sub>\<tau> where "X\<^sub>\<tau> = remdups (vars_rule_impl (s \<cdot> ?\<tau>, t \<cdot> ?\<tau>))"
    from distinct_remdups have distinct:"\<And>ps. distinct X\<^sub>\<sigma>" unfolding X\<^sub>\<sigma>_def by auto
    have finite:"\<And>ps. finite (set X\<^sub>\<sigma>)" unfolding X\<^sub>\<sigma>_def by auto
    from assms[unfolded check_var_orders_joinable_def Let_def] \<rho>[unfolded ps_def] have
      isOK:"\<forall>\<pi> \<in> set (perms X\<^sub>\<sigma>). isOK (check_var_order_joinable E R (s \<cdot> ?\<sigma>) (t \<cdot> ?\<sigma>) \<pi>)"
      unfolding X\<^sub>\<sigma>_def ps_def split isOK_update_error isOK_forallM by metis
    { fix \<pi>
      assume \<pi>:"\<pi> \<in> set (perms X\<^sub>\<tau>)"
      { fix x :: 'v
        assume memX:"x \<in> set ?X"
        from subst_of_partitioning[OF memX part] fin have "?\<sigma> x = ?\<tau> x"
          unfolding set_remdups set_vars_rule_impl \<rho> by simp
      } note vs = this
      from vs have s:"s \<cdot> ?\<sigma> = s \<cdot> ?\<tau>" using term_subst_eq_conv[of s] by auto
      from vs have t:"t \<cdot> ?\<sigma> = t \<cdot> ?\<tau>" using term_subst_eq_conv[of t] by auto
      from \<pi> have "\<pi> \<in> set (perms X\<^sub>\<sigma>)" unfolding X\<^sub>\<sigma>_def X\<^sub>\<tau>_def s t by simp
      with isOK have isOK:"isOK (check_var_order_joinable E R (s \<cdot> ?\<sigma>) (t \<cdot> ?\<sigma>) \<pi>)" by auto
      interpret moc:moc_spec "ext_check_ord \<pi>" least
        by (unfold_locales, insert least_less ext_least, fastforce)
      note ran = range_subst_of_partitioning[OF part, unfolded set_remdups set_vars_rule_impl, OF fin]
      note dom = dom_ran_subst_of_partitioning[OF part, unfolded set_remdups set_vars_rule_impl, OF fin]
      from ran have vs:"vars_rule (s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<subseteq> vars_rule (s,t)" unfolding vars_rule_def fst_conv snd_conv
        using vars_term_subst_pow[of _ 1 "subst_of_partitioning \<rho>"] by force
      
      note isOK = isOK[unfolded check_var_order_joinable_def]
      from ext_check_ord[of \<pi>] have ext:"moc.all_less \<subseteq> \<C> (term_order_of_perm \<pi>)" by auto
      from moc.check_instance_joinable[OF isOK]
      have "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> instance_join moc.all_less (set (E @ R))"
        using rstep_union[of "set E" "set R"] by auto
      note join = instance_join_mono[OF ext this] 
      with vs have "(s \<cdot> ?\<tau>, t \<cdot> ?\<tau>) \<in> instance_join (\<C> (term_order_of_perm \<pi>)) (set (E @ R))"
        "vars_rule (s \<cdot> ?\<tau>, t \<cdot> ?\<tau>) \<subseteq> vars_rule (s,t)" unfolding s t by auto
    }
  } note check = this[unfolded X_def[symmetric]]
  from X_def have X':"vars_term s \<union> vars_term t = X" unfolding vars_rule_def by auto

  show ?thesis unfolding var_order_joinable_def Let_def X' proof(rule, rule, rule, rule)
    fix \<rho> gt ::"'v  rel"
    assume equiv:"equiv X \<rho>" and equiv_total:"equiv_total X \<rho> gt"
    let ?\<sigma> = "\<lambda>p. hat X p"
    let ?X = "\<lambda>p. (vars_rule_impl (s \<cdot> ?\<sigma> p, t \<cdot> ?\<sigma> p))"
    let ?perms = "\<lambda>p. set (perms (remdups (?X p)))"
    let ?ord = "\<lambda>\<pi>. {(x, y). (x, y) \<in> \<C> (term_order_of_perm \<pi>)}"
    let ?P = "\<lambda>p. \<forall>\<pi> \<in> ?perms p.
      (s \<cdot> ?\<sigma> p, t \<cdot> ?\<sigma> p) \<in> instance_join {(x, y). (x, y) \<in> \<C> (term_order_of_perm \<pi>)} (set (E @ R)) \<and> vars_rule (s \<cdot> ?\<sigma> p, t \<cdot> ?\<sigma> p) \<subseteq> X"
    
    note x = all_partitions_all_equiv_rels[of _ ?P, OF _ equiv]
    have "\<forall>\<pi> \<in> ?perms \<rho>. (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<in> instance_join (?ord \<pi>) (set (E @ R)) \<and>
      vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<subseteq> X" using x check ext_check_ord 
      using x check X_def by auto
    hence *:"\<forall>\<pi> \<in> ?perms \<rho>. (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<in> instance_join (?ord \<pi>) (set (E @ R))"
      "vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<subseteq> X" by auto
    have "finite X" unfolding X_def vars_rule_def by auto
    note repr = repr[OF this equiv]
    { fix x ::"'v"
      assume a:"x \<in> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>)"
      with *(2) have inX:"x \<in> X" unfolding X_def by auto
      with a X_def have "\<exists>y \<in> X. x \<in> vars_term (?\<sigma> \<rho> y)" unfolding vars_rule_def fst_conv snd_conv
          vars_term_subst Un_iff hat_def using image_iff UN_E by auto
      then obtain y where yinX:"y \<in> X" "x = repr X \<rho> y" unfolding hat_def by auto
      with repr[OF yinX(1)] equiv[unfolded equiv_def sym_def] have "(x,y) \<in> \<rho>" by auto
      with repr yinX have "x = repr X \<rho> x" by auto
    } note x_is_repr_x = this
    { fix x y
      assume x:"x \<in> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>)" and y:"y \<in> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>)" and xy:"x \<noteq> y"
      with *(2) have inX:"x \<in> X" "y \<in> X" by auto
      from x_is_repr_x[OF x] x_is_repr_x[OF y] repr[OF inX(1), of y] xy have "(x,y) \<notin> \<rho>" by auto
    } note aux = this
    have total:"Relation.total_on (set (remdups (?X \<rho>))) gt"
      unfolding set_remdups set_vars_rule_impl Relation.total_on_def proof(rule, rule, rule)
      fix x y
      assume a:"x \<in> vars_rule (s \<cdot> hat X \<rho>, t \<cdot> hat X \<rho>)" "y \<in> vars_rule (s \<cdot> hat X \<rho>, t \<cdot> hat X \<rho>)" "x \<noteq> y"
      with aux *(2) have "(x,y) \<notin> \<rho>" "x \<in> X" "y \<in> X" unfolding set_vars_rule_impl by auto
      with equiv_total[unfolded equiv_total_def] a show "(x, y) \<in> gt \<or> (y, x) \<in> gt" by auto
    qed
    from equiv_total have wf:"wf (gt\<inverse>)" "trans gt" unfolding equiv_total_def by auto
    let ?cord = "\<lambda>\<pi>. {(x, y). mk_closure \<pi> x y}"
    let ?P = "\<lambda>\<pi>. (s \<cdot> hat X \<rho>, t \<cdot> hat X \<rho>) \<in> instance_join (?cord \<pi>) (set (E @ R))"
    from all_perms_all_total_wf_rels[OF distinct_remdups _ total wf, of ?P] *
    have *:"(s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<in> instance_join (?cord (gt \<restriction> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>))) (set (E @ R))"
      unfolding term_order_of_perm_def set_remdups set_vars_rule_impl by fast
    have subset:"(gt \<restriction> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>)) \<subseteq> gt" using restrict_def by fast
    have "?cord (gt \<restriction> vars_rule (s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>)) \<subseteq> ?cord gt" proof(rule, unfold mem_Collect_eq split)
      fix x y
      assume "mk_closure (gt \<restriction> vars_rule (s \<cdot> hat X \<rho>, t \<cdot> hat X \<rho>)) x y"
      with C_mono subset show "mk_closure gt x y"
        by (smt mem_Collect_eq subsetCE subsetI)
    qed
    from instance_join_mono[OF this] *
    have "(s \<cdot> ?\<sigma> \<rho>, t \<cdot> ?\<sigma> \<rho>) \<in> instance_join (?cord gt) (set (E @ R))" by auto
    thus "(s \<cdot> hat X \<rho>, t \<cdot> hat X \<rho>)
       \<in> (ordstep (\<C> {(Var x, Var y) |x y. (x, y) \<in> gt}) (set (E @ R)))\<^sup>* O
          (rstep (set (E @ R)))\<^sup>= O ((ordstep (\<C> {(Var x, Var y) |x y. (x, y) \<in> gt}) (set (E @ R)))\<inverse>)\<^sup>*" by simp
  qed
qed                                               
end

(* TODO move *)
fun choice_bot :: "('e +\<^sub>\<bottom> 'b) list \<Rightarrow> 'e list +\<^sub>\<bottom> 'b" ("choice\<^sub>\<bottom>")
where
  "choice\<^sub>\<bottom> [] = Strict_Sum.error []" |
  "choice\<^sub>\<bottom> (x # xs) = (try x catch (\<lambda>e. choice_bot xs <+? Cons e))"

(* TODO write in a way such that the specializations below are not necessary? *)
lemma choice_bot_mono [partial_function_mono]:
  assumes xs: "\<And>x. x \<in> set xs \<Longrightarrow> mono_sum_bot x"
  shows "mono_sum_bot (\<lambda>f. choice\<^sub>\<bottom> (map (\<lambda>x. x f) xs))"
  using assms
proof(induct xs)
  case (Cons x xs)
  hence mono_x:"mono_sum_bot x" and mono_xs:"\<And>x. x \<in> set xs \<Longrightarrow> mono_sum_bot x" by auto
  note ih = Cons(1)[OF mono_xs, simplified]
  note aux = catch_mono[OF ih sum_bot_const_mono]
  show ?case unfolding list.map choice_bot.simps by
    (rule catch_mono, rule mono_x, insert aux, auto)
qed (simp add: monotone_def)

lemma choice_bot_mono2 [partial_function_mono]:
  assumes x: "mono_sum_bot x" "mono_sum_bot y"
  shows "mono_sum_bot (\<lambda>f. choice\<^sub>\<bottom> [x f, y f])"
  using assms choice_bot_mono[of "[x,y]"] by auto

lemma choice_bot_mono6 [partial_function_mono]:
  assumes x: "mono_sum_bot x1" "mono_sum_bot x2"  "mono_sum_bot x3" "mono_sum_bot x4"  "mono_sum_bot x5" "mono_sum_bot x6"
  shows "mono_sum_bot (\<lambda>f. choice\<^sub>\<bottom> [x1 f, x2 f, x3 f, x4 f, x5 f, x6 f])"
  using assms choice_bot_mono[of "[x1, x2, x3, x4, x5, x6]"]
  by auto

fun forallM_bot :: "('b \<Rightarrow> 'e +\<^sub>\<bottom> unit) \<Rightarrow> 'b list \<Rightarrow> ('b * 'e) +\<^sub>\<bottom> unit" ("forallM\<^sub>\<bottom>")
where
  "forallM\<^sub>\<bottom> f [] = Strict_Sum.return ()" |
  "forallM\<^sub>\<bottom> f (x # xs) = f x <+? Pair x \<then> forallM_bot f xs"

fun existsM_bot :: "('b \<Rightarrow> 'e +\<^sub>\<bottom> unit) \<Rightarrow> 'b list \<Rightarrow> 'e list +\<^sub>\<bottom> unit" ("existsM\<^sub>\<bottom>")
where
  "existsM\<^sub>\<bottom> f [] =  Strict_Sum.error []" |
  "existsM\<^sub>\<bottom> f (x # xs) = (try f x catch (\<lambda>e. existsM_bot f xs <+? Cons e))"

lemma existsM_bot_mono[partial_function_mono]:
  assumes f: "\<And>x. mono_sum_bot (g x)"
  shows "mono_sum_bot (\<lambda>f. existsM\<^sub>\<bottom> (\<lambda>x. g x f) xs)"
proof(induct xs)
  case (Cons x xs)
  from f have "sum_bot.mono_body (\<lambda>f. f x)" by (simp add: fun_ord_def monotone_def)
  show ?case unfolding list.map existsM_bot.simps 
    by (rule catch_mono, rule f, rule catch_mono, auto simp:Cons sum_bot_const_mono)
qed (simp add: monotone_def)

lemma forallM_bot_mono[partial_function_mono]:
  assumes f: "\<And>x. mono_sum_bot (g x)"
  shows "mono_sum_bot (\<lambda>f. forallM\<^sub>\<bottom> (\<lambda>x. g x f) xs)"
proof(induct xs)
  case (Cons x xs)
  show ?case unfolding list.map forallM_bot.simps
    by (rule bind_mono, rule catch_mono, rule f, auto simp:sum_bot_const_mono Cons)
qed (simp add: monotone_def)

definition lift :: "'e check \<Rightarrow> ('e +\<^sub>\<bottom> unit)"
  where "lift c = (case c of return v \<Rightarrow> Strict_Sum.return v | error e \<Rightarrow> Strict_Sum.error e)"

abbreviation check_bot :: "bool \<Rightarrow> 'e \<Rightarrow> 'e +\<^sub>\<bottom> unit" ("check\<^sub>\<bottom>")
  where "check\<^sub>\<bottom> b e \<equiv> lift (check b e)"

lemmas [code] =
  choice_bot.simps
  existsM_bot.simps
  forallM_bot.simps
  lift_def


locale gcr_closure_ops = moc_closure_ops check_ord least xvar yvar ext_check_ord
  for check_ord :: "('a::showl, 'v::{showl, linorder, infinite}) term \<Rightarrow> ('a,'v) term \<Rightarrow> bool"
  and least :: "'a"
  and xvar yvar :: "'v \<Rightarrow> 'v"
  and ext_check_ord :: "'v list \<Rightarrow> ('a, 'v) term \<Rightarrow> ('a, 'v) term \<Rightarrow> bool"
begin

context
  fixes E R:: "('a, 'v) rules"
begin

abbreviation "mord_reducts \<equiv> mord_rewrite (E @ R)"

text \<open>Implement ground joinability check defined in order_closure.ground_join_rel.\<close>
partial_function (sum_bot)
  check_ground_join_rel_bot :: "('a, 'v) Term.term \<Rightarrow> ('a, 'v) Term.term \<Rightarrow> ((String.literal \<Rightarrow> String.literal) +\<^sub>\<bottom> unit)"
where [simp,code]:
  "check_ground_join_rel_bot s t = (
     case (s,t) of (Var x,_) \<Rightarrow>
       choice\<^sub>\<bottom> [ check\<^sub>\<bottom> (Var x = t) (showsl_lit (STR ''The terms are different.'')),
                    existsM\<^sub>\<bottom> (check_ground_join_rel_bot (Var x)) (mord_reducts t)
                      <+? (\<lambda>_. (showsl_lit (STR ''No right-rewrite is possible.'')))
                  ] <+? showsl_sep id showsl_nl
| (Fun f ss, Var x) \<Rightarrow>
     choice\<^sub>\<bottom> [ check\<^sub>\<bottom> (Var x = s) (showsl_lit (STR ''The terms are different.'')),
                  existsM\<^sub>\<bottom> (\<lambda>u. check_ground_join_rel_bot u (Var x)) (mord_reducts s)
                    <+? (\<lambda>_. showsl_lit (STR ''No left-rewrite is possible.''))
                ] <+? showsl_sep id showsl_nl
| (Fun f ss, Fun g ts) \<Rightarrow>
     choice\<^sub>\<bottom> [ check\<^sub>\<bottom> (Fun f ss = Fun g ts) (showsl_lit (STR ''terms differ'')),
                  lift (check_instance (E @ R) (Fun f ss) (Fun g ts)),
                  existsM\<^sub>\<bottom> (\<lambda>u. check_ground_join_rel_bot u (Fun g ts)) (mord_reducts (Fun f ss))
                    <+? (\<lambda>_. showsl (STR ''No left-rewrite is possible.'')),
                  existsM\<^sub>\<bottom> (check_ground_join_rel_bot (Fun f ss)) (mord_reducts (Fun g ts))
                    <+? (\<lambda>_. showsl (STR ''No right-rewrite is possible.'')),
                  if f = g \<and> length ss = length ts then
                    forallM\<^sub>\<bottom> (\<lambda>(si, ti). check_ground_join_rel_bot si ti) (zip ss ts)
                      <+? (\<lambda>_. showsl (STR ''Arguments are not ground-joinable.''))
                  else
                    Strict_Sum.error (showsl (STR ''The congruence rule does not apply.'')),
                 lift (check_var_orders_joinable E R (Fun f ss) (Fun g ts))
               ] <+? showsl_sep id showsl_nl)"

text \<open>Use above check function in standard check monad.\<close>
definition check_ground_join_rel where
"check_ground_join_rel s t \<equiv> (
   case check_ground_join_rel_bot s t of
     Strict_Sum.Left e \<Rightarrow>
       error (showsl_lit (STR ''The equation '') \<circ> showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t \<circ> showsl_lit (STR '' is not ground joinable\<newline>''))
   | Strict_Sum.Right v \<Rightarrow> return v
   | Bottom \<Rightarrow> error (showsl (STR ''Ground joinability could not be established.'')))"

definition "isOK_bot" ("isOK\<^sub>\<bottom>") where "isOK\<^sub>\<bottom> x \<equiv> (case x of Right v \<Rightarrow> True | _ \<Rightarrow> False)"
end
end

declare
  gcr_closure_ops.check_ground_join_rel_bot.simps[code]
  gcr_closure_ops.check_ground_join_rel_def[code]
  gcr_closure_ops.isOK_bot_def[code]

locale gtotal_moc_closure_spec = gcr_closure_ops check_ord least xvar yvar ext_check_ord +
  moc_closure_spec less check_ord least F xvar yvar ext_check_ord \<C>
  for less :: "('f, 'v) term \<Rightarrow> ('f::{showl}, 'v::{showl, linorder, infinite}) term \<Rightarrow> bool" (infix "\<succ>" 50) (* should read as gt *)
  and check_ord :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" 
  and least :: "'f"
  and F :: "('f \<times> nat) set"
  and xvar :: "'v \<Rightarrow> 'v"
  and yvar :: "'v \<Rightarrow> 'v"
  and ext_check_ord :: "'v list \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> bool"
  and \<C> :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel"
  and repr :: "'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> 'v" +
  assumes ren: "inj xvar" "inj yvar" "range xvar \<inter> range yvar = {}"
begin

sublocale ocomp:ordered_completion_inf by (insert ctxt subst trans SN_less, standard, auto)

context
  fixes E R:: "('f, 'v) rules"
begin

abbreviation "mord_rdcts \<equiv> mord_reducts E R"


text \<open>Some auxiliary results to prove termination of the function below.\<close>
abbreviation "enccomp_pair_rel \<equiv> {((s,t),(s',t')) | s t s' t'. ({#s',t'#}, {#s, t#}) \<in> ocomp.mulless}"

lemma wf_enccomp_pair_rel:"wf enccomp_pair_rel"
proof -
  { fix f
    assume a:"\<forall>i. (f i, f (Suc i)) \<in> enccomp_pair_rel\<inverse>"
    define g where "g i \<equiv> {# fst (f i), snd (f i)#}" for i
    { fix i
      obtain a b where id:"f i = (a,b)" by (cases "f i", auto)
      obtain a' b' where id':"f (Suc i) = (a',b')" by (cases "f (Suc i)", auto)
      from a[rule_format, of i] have "(g i, g(Suc i)) \<in> s_mul_ext {\<cdot>\<unrhd>} {\<cdot>\<succ>}"
        unfolding g_def id id' fst_conv snd_conv converse_iff mem_Collect_eq by auto
    }
    with ocomp.lessenc_op.SN have False by auto
  }
  hence "SN (enccomp_pair_rel\<inverse>)" by fast
  from SN_imp_wf[OF this] show ?thesis by simp
qed

lemma mord_reducts_lessenc:
  assumes "u \<in> set (mord_rdcts t)"
  shows "((s, u), (s, t)) \<in> enccomp_pair_rel \<and> ((u, s), (t, s)) \<in> enccomp_pair_rel" 
proof -
  let ?check_set = "{(s,t) | s t. check_ord s t}"
  from rewrite_mordstep_sound[OF assms] mordstep_ordstep have "(t, u) \<in> ordstep ?check_set (set (E @ R))" by force
  with ordstep_mono[of _ _ ?check_set less_set] ord_subset have "(t, u) \<in> ordstep less_set (set (E @ R))" by auto
  with ctxt_closed_less ordstep_imp_ord have "t \<succ> u" by auto
  hence "t \<cdot>\<succ> u" unfolding ocomp.lessencp_def by blast
  from ocomp.mset_two2[OF this, of s] ocomp.mset_two[OF this, of s] show ?thesis by simp
qed

lemma args_lessenc:
  assumes "(si, ti) \<in> set (zip ss ts)"
  shows "((si, ti), (Fun f ss, Fun g ts)) \<in> enccomp_pair_rel" 
proof -
  from assms have "Fun f ss \<rhd> si" by (meson set_zip_leftD supt.arg)
  hence si:"Fun f ss \<cdot>\<succ> si" unfolding ocomp.lessencp_def using encomp_subsumes_cases[of si "Fun f ss"] by auto
  from assms have "Fun g ts \<rhd> ti" by (meson set_zip_rightD supt.arg)
  hence "Fun g ts \<cdot>\<succ> ti" unfolding ocomp.lessencp_def using encomp_subsumes_cases[of ti "Fun g ts"] by auto
  from ocomp.mset_two[OF si, of ti] ocomp.mset_two2[OF this, of "Fun f ss"] 
  show ?thesis using ocomp.lessenc_op.trans_S[unfolded trans_def] by blast
qed

text \<open>Function equivalent to check_ground_join_rel, but in this context termination can be shown.
      It is only used as an auxiliary to simplify proofs, so error messages are minimal.\<close>
function (sequential) check_aux
where
  "check_aux (Var x) t =
     choice [ check ((Var x) = t) (showsl_lit (STR '''')),
              check_exm (\<lambda>u. check_aux (Var x) u) (mord_rdcts t) (\<lambda>_. showsl_lit (STR ''''))
            ] <+? showsl_sep id showsl_nl"
| "check_aux s (Var x) =
     choice [ check (Var x = s) (showsl (STR '''')) ,
              check_exm (\<lambda>u. check_aux u (Var x)) (mord_rdcts s) (\<lambda>_. showsl (STR ''''))
            ] <+? showsl_sep id showsl_nl"
| "check_aux (Fun f ss) (Fun g ts) =
     choice [ check (f = g \<and> ss = ts) (showsl_lit (STR '''')),
              check_instance (E @ R) (Fun f ss) (Fun g ts),
              check_exm (\<lambda>u. check_aux u (Fun g ts)) (mord_rdcts (Fun f ss)) (\<lambda>_. showsl (STR '''')),
              check_exm (\<lambda>u. check_aux (Fun f ss) u) (mord_rdcts (Fun g ts)) (\<lambda>_. showsl (STR '' '')),
              (if f = g \<and> length ss = length ts then
                 check_allm (\<lambda>(si, ti). check_aux si ti) (zip ss ts)
               else
                 error (showsl (STR ''''))),
              check_var_orders_joinable E R (Fun f ss) (Fun g ts)
            ] <+? showsl_sep id showsl_nl"
  by pat_completeness auto
termination apply (relation enccomp_pair_rel)
  apply (simp add:wf_enccomp_pair_rel)
  apply (rule conjunct1[OF mord_reducts_lessenc], simp)
  apply (rule conjunct2[OF mord_reducts_lessenc], simp)
  apply (rule conjunct2[OF mord_reducts_lessenc], simp)
  apply (rule conjunct1[OF mord_reducts_lessenc], simp)
  apply (rule args_lessenc, simp)
  done

lemma bind_bot_bind:
  assumes "isOK\<^sub>\<bottom>(xx) \<Longrightarrow> isOK(x)" "(\<exists>e :: 'c. isOK\<^sub>\<bottom>(yy e)) \<Longrightarrow> (\<forall>e :: 'c. isOK(y e))"
  and "isOK\<^sub>\<bottom>(xx \<bind> yy)"
shows "isOK(x \<bind> y)"
proof -
  from assms(3) obtain v where v:"xx = Right v" unfolding isOK_bot_def by (cases xx, auto)
  with assms(3) have ok:"isOK\<^sub>\<bottom>(yy v)" by (cases "yy v", auto)
  from v assms obtain v' where v':"x = Inr v'" unfolding isOK_bot_def by (cases xx, auto)
  from ok assms have "isOK(y v')" by auto
  with v' show ?thesis by auto
qed

lemma catch_bot_catch:
  assumes "isOK\<^sub>\<bottom>(xx) \<Longrightarrow> isOK(x)" "(\<exists>e :: 'c. isOK\<^sub>\<bottom>(yy e)) \<Longrightarrow> (\<forall>e :: 'c. isOK(y e))"
  and "isOK\<^sub>\<bottom>(try xx catch yy)"
shows "isOK(try x catch y)"
proof (cases xx)
  case Bottom
  with assms(3) show ?thesis unfolding isOK_bot_def by auto
next
  case (Right r)
  with assms(1) show ?thesis unfolding isOK_bot_def by auto
next
  case (Left e)
  with assms(3) have "isOK\<^sub>\<bottom>(yy e)" by (cases "yy e", insert catch_splits, auto)
  with assms(2) have e:"\<exists>e. isOK\<^sub>\<bottom>(yy e)" by auto
  show ?thesis proof (cases x)
    case (Inr _)
    thus ?thesis by auto
  next
    case (Inl e')
    with assms(2)[OF] e have "isOK(y e')" by simp
    thus ?thesis unfolding Inl using catch_splits by auto
  qed
qed

lemma ok_catch_left_bot[simp]:"isOK\<^sub>\<bottom>(try a catch (\<lambda>ea. sum_bot.Left (e ea))) = isOK\<^sub>\<bottom> a"
  using catch_splits
proof (cases a)
  case Bottom
  with catch_mono show ?thesis unfolding isOK_bot_def by auto
qed (auto simp:isOK_bot_def)

lemma ok_catch_error_bot[simp]:"isOK\<^sub>\<bottom>(try a catch (\<lambda>ea. Strict_Sum.error (e ea))) = isOK\<^sub>\<bottom> a"
  using ok_catch_left_bot error_def by auto

lemma choice_bot_choice:
  assumes "length (xs :: ('a + 'b) list) = length (xxs :: ('a +\<^sub>\<bottom> 'c) list)"
  and "\<forall>i < length xs. isOK\<^sub>\<bottom>(xxs ! i) \<longrightarrow> isOK(xs ! i)"
  and "isOK\<^sub>\<bottom>(choice\<^sub>\<bottom> xxs)"
  shows "isOK(choice xs)"
  using assms
proof(induct xs arbitrary: xxs)
  case Nil
  then have xxs:"xxs = Nil" by auto
  from Nil(3) show ?case unfolding xxs unfolding isOK_bot_def by auto
next
  case (Cons x xs)
  from Cons(2) obtain y ys where xxs:"xxs = y # ys" and len:"length xs = length ys" by (cases "xxs", auto)
  from Cons(3)[rule_format, of 0] have xy:"isOK\<^sub>\<bottom> y \<Longrightarrow> isOK x" unfolding xxs Cons by auto
  { fix i
    assume "i < length xs"
    hence "Suc i < Suc (length xs)" by auto
    from Cons(3)[rule_format, of "Suc i", unfolded xxs nth_Cons_Suc length_Cons, OF this]
    have "(isOK\<^sub>\<bottom>(ys ! i) \<longrightarrow> isOK(xs ! i))" by blast
  }
  hence "\<forall>i < length xs. isOK\<^sub>\<bottom>(ys ! i) \<longrightarrow> isOK(xs ! i)" by auto
  note ih = Cons(1)[OF len this]
  note ok = Cons(4)[unfolded xxs choice_bot.simps]
  note cbc = catch_bot_catch[of y x, OF xy, simplified, OF _ ok]
  show ?case unfolding Error_Monad.choice.simps by (rule cbc, simp add:ih)
qed

lemma existsM_bot_existsM:
  fixes aa :: "'b \<Rightarrow> 'e +\<^sub>\<bottom> unit" and a :: "'b \<Rightarrow> 'e + unit"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)"
  and "isOK\<^sub>\<bottom>(existsM\<^sub>\<bottom> aa xs)"
  shows "isOK(existsM a xs)"
  using assms
proof(induct xs)
  case Nil
  from Nil(2) show ?case unfolding isOK_bot_def by auto
next
  case (Cons x xs)
  from Cons(2) have xy:"isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)" unfolding Cons by auto
  from Cons(2) have "\<And>x. x \<in> set xs \<Longrightarrow> isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)" by auto
  note ih = Cons(1)[OF this]
  note ok = Cons(3)[unfolded existsM_bot.simps]
  note cbc = catch_bot_catch[of "aa x" "a x", OF xy, simplified, OF _ ok]
  show ?case unfolding existsM.simps by (rule cbc, insert ih, simp)
qed

lemma forallM_bot_forallM:
  fixes aa :: "'b \<Rightarrow> 'e +\<^sub>\<bottom> unit" and a :: "'b \<Rightarrow> 'e + unit"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)"
  and "isOK\<^sub>\<bottom>(forallM\<^sub>\<bottom> aa xs)"
  shows "isOK(forallM a xs)"
  using assms
proof(induct xs)
  case Nil
  from Nil(2) show ?case unfolding isOK_bot_def by auto
next
  case (Cons x xs)
  from Cons(2) have xy:"isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)" unfolding Cons by auto
  from Cons(2) have "\<And>x. x \<in> set xs \<Longrightarrow> isOK\<^sub>\<bottom>(aa x) \<Longrightarrow> isOK(a x)" by auto
  note ih = Cons(1)[OF this]
  note ok = Cons(3)[unfolded forallM_bot.simps]
  note bbb = bind_bot_bind[OF _ _ ok]
  show ?case unfolding forallM.simps by (rule bbb, simp add:xy, insert ih, simp)
qed

lemma check_aux:
  assumes "isOK\<^sub>\<bottom>(check_ground_join_rel_bot E R s t)"
  shows "isOK(check_aux s t)"
proof -
  have ok_catch_error:"\<And>chk e. isOK(try chk catch (\<lambda>x. Inl (e x))) = isOK(chk)" by simp
  have try_error:"\<And>e f. (try (Inl e) catch (\<lambda>e. f e)) = f e" using catch_splits by auto
  have try_error_bot:"\<And>e f. (try (Strict_Sum.error e) catch (\<lambda>e. f e)) = f e" using catch_splits by auto
  { fix k and y :: "'a +\<^sub>\<bottom> 'b" and ys :: "('a +\<^sub>\<bottom> 'b) list" and x :: "'a + 'b" and xs ::"('a + 'b) list"
    assume "isOK\<^sub>\<bottom> y \<longrightarrow> isOK x" and "\<forall>i < k. isOK\<^sub>\<bottom> (ys ! i) \<longrightarrow> isOK (xs ! i)"
    hence "\<forall>i < Suc k. isOK\<^sub>\<bottom> ((y # ys) ! i) \<longrightarrow> isOK ((x # xs) ! i)"
      using less_Suc_eq_0_disj by auto
  } note list_check = this
  note defs = check_ground_join_rel_bot.simps[of E R]
  let ?cgj = "check_ground_join_rel_bot E R"
  from assms show ?thesis proof(induct rule:check_aux.induct)
    case (1 x t)
    note defs = defs[of "Var x" t, unfolded split] check_aux.simps(1)[of x t]
    note ok = 1(2)[unfolded defs term.simps ok_catch_error_bot]
    note cbc = choice_bot_choice[OF _ _ ok]
    show ?case proof(cases "Var x = t")
      case True
      show ?thesis unfolding defs ok_catch_error choice.simps unfolding True check_def by auto
    next
      case False
      hence False:"(Var x = t) = False" by auto
      note ok = ok[unfolded check_def False if_False lift_def choice_bot.simps]
      hence ok:"isOK\<^sub>\<bottom>(existsM\<^sub>\<bottom> (?cgj (Var x)) (mord_rdcts t))" by auto
      show ?thesis unfolding defs ok_catch_error check_def
        unfolding Error_Monad.choice.simps False if_False catch_error ok_catch_error
        using existsM_bot_existsM[OF 1(1) ok, of "\<lambda>x. x"] by blast
    qed
next
  case (2 f ss x)
  note defs = defs[of "Fun f ss" "Var x", unfolded split] check_aux.simps(2)[of f ss x]
  note ok = 2(2)[unfolded defs term.simps ok_catch_error_bot]
  note cbc = choice_bot_choice[OF _ _ ok]
  have False:"(Var x = Fun f ss) = False" by auto
  note ok = ok[unfolded check_def False if_False lift_def choice_bot.simps ]
  hence ok:"isOK\<^sub>\<bottom>(existsM\<^sub>\<bottom> (\<lambda>u. ?cgj u (Var x)) (mord_rdcts (Fun f ss)))" by auto
  show ?case unfolding defs ok_catch_error check_def
    unfolding Error_Monad.choice.simps False if_False catch_error ok_catch_error
    using existsM_bot_existsM[OF 2(1) ok, of "\<lambda>x. x"] by blast
next
  case (3 f ss g ts)
  note defs = defs[of "Fun f ss" "Fun g ts", unfolded split] check_aux.simps(3)[of f ss g ts]
  note ok = 3(4)[unfolded defs term.simps ok_catch_error_bot]
  (* show cases separately *)
  let ?inst = "check_instance (E @ R) (Fun f ss) (Fun g ts)"
  { assume "isOK\<^sub>\<bottom> (lift ?inst)"
    hence "isOK ?inst" unfolding isOK_def isOK_bot_def lift_def by (cases "?inst", auto)
  } note inst = this
  { assume ok:"isOK\<^sub>\<bottom> (existsM\<^sub>\<bottom> (\<lambda>u. ?cgj u (Fun g ts)) (mord_rdcts (Fun f ss)))"
    note exM = existsM_bot_existsM[OF 3(1) ok, of "\<lambda>x. x"]
    hence "isOK (existsM (\<lambda>u. check_aux u (Fun g ts)) (mord_rdcts (Fun f ss)))" by blast
  } note rewrite_left = this
  { assume ok:"isOK\<^sub>\<bottom> (existsM\<^sub>\<bottom> (?cgj (Fun f ss)) (mord_rdcts (Fun g ts)))"
    note exM = existsM_bot_existsM[OF 3(2) ok, of "\<lambda>x. x"]
    hence "isOK (existsM (check_aux (Fun f ss)) (mord_rdcts (Fun g ts)))" by blast
  } note rewrite_right = this
  { fix b a aa e e'
    assume "b \<and> isOK\<^sub>\<bottom>(aa) \<Longrightarrow> isOK(a)"
    hence "isOK\<^sub>\<bottom>(if b then aa else Strict_Sum.error e') \<longrightarrow> isOK (if b then a else Inl e)"
      unfolding isOK_bot_def by (cases b, auto)
  } note if_ok = this
  { assume eq:"(f = g \<and> length ss = length ts) \<and>
      isOK\<^sub>\<bottom> (forallM\<^sub>\<bottom> (\<lambda>(x, y). check_ground_join_rel_bot E R x y) (zip ss ts))"
    note ok = conjunct2[OF eq]
    note all = forallM_bot_forallM[OF _ ok]
    have "isOK (forallM (\<lambda>(x, y). check_aux x y) (zip ss ts))"
      by (rule all, insert 3(3)[OF conjunct1[OF eq]], fast)
  } note cong = this
  let ?vo = "check_var_orders_joinable E R (Fun f ss) (Fun g ts)"
  { assume "isOK\<^sub>\<bottom> (lift ?vo)"
    hence "isOK ?vo" unfolding isOK_def isOK_bot_def lift_def by (cases "?vo", auto)
  } note vo = this
  note cbc = choice_bot_choice[OF _ _ ok]
  show ?case unfolding defs ok_catch_error
    apply (rule cbc, unfold length_Cons length_nth_simps, simp)
    apply (rule list_check)
    apply (simp add:isOK_bot_def lift_def check_def)
    apply (rule list_check)
    apply (rule impI, rule inst, simp)
    apply (rule list_check)
    apply (unfold ok_catch_error_bot ok_catch_error, rule impI, rule rewrite_left, simp)
    apply (rule list_check)
    apply (unfold ok_catch_error_bot ok_catch_error, rule impI, rule rewrite_right, simp)
    apply (rule list_check)
    apply (rule if_ok, unfold ok_catch_error_bot ok_catch_error, rule cong, fast)
    apply (rule list_check)
    apply (rule impI, rule vo, simp)
    apply auto
    done
  qed
qed

lemma check_aux_sound:
  assumes "isOK(check_aux s t)"
  shows "(s,t) \<in> ground_join_rel (set (E @ R))"
  using assms
proof -
  let ?ok = "\<lambda>s t. isOK (check_aux s t)"
  let ?ER = "set (E @ R)"
  let ?rel = "\<lambda> s t. (s,t) \<in> ground_join_rel ?ER"
  let ?reducts = "\<lambda>t. set (mord_rdcts t)"
  let ?ordstep' = "\<lambda>s t. (s,t) \<in> ordstep {(s,t) | s t. check_ord s t} ?ER"
  let ?ordstep = "\<lambda>s t. (s,t) \<in> ordstep less_set ?ER"
  note defs = check_aux.simps
  have oo[simp]: "\<And>x xa. ((x, xa) \<in> ordstep less_set (set (E @ R)) = (ordstepp (\<lambda>x xa. (x, xa) \<in> less_set) (\<lambda>x xa. (x, xa) \<in> set (E @ R)) x xa))"
    using ordstepp_ordstep_eq[of less_set "set (E @ R)"] by auto
  note ordstep_mono = ordstep_mono[of _ _ "{(s,t) | s t. check_ord s t}" less_set]
  with ord_subset have ordstep_mono:"ordstep {(s, t) | s t. check_ord s t} ?ER \<subseteq> ordstep {\<succ>} ?ER" by blast
  {fix s t
    assume "t \<in> ?reducts s"
    from rewrite_mordstep_sound[OF this] have "?ordstep s t" using 
  mordstep_ordstep[of least all_less ?ER] ordstep_mono by auto
  } note reduct_ordstep = this
  from assms show ?thesis proof(induct rule:check_aux.induct)
    fix x t
    assume ih:"\<And>u. (u \<in> ?reducts t \<Longrightarrow> ?ok (Var x) u \<Longrightarrow> ?rel (Var x) u)" and ok:"?ok (Var x) t"
    from ok[unfolded defs(1)[of x t]] consider "\<exists> u \<in> ?reducts t. ?ok (Var x) u" | "Var x = t"
      unfolding isOK_update_error isOK_choice isOK_check isOK_existsM by argo
    thus "?rel (Var x) t" proof(cases)
      case 1
      then obtain u where u:"u \<in> ?reducts t" "?ok (Var x) u" by blast
      from reduct_ordstep[OF u(1)]  ih[OF u, THEN ground_join_rel.rewrite_right, of t] 
        show ?thesis unfolding oo by auto
    qed (auto simp: ground_join_rel.refl)
  next
    case (2 f ss x)
    from 2(2)[unfolded defs(2)] have "\<exists>u \<in> ?reducts (Fun f ss). ?ok u (Var x)"
      unfolding isOK_update_error isOK_choice isOK_check isOK_existsM by fast
    then obtain u where u:"u \<in> ?reducts (Fun f ss)" "?ok u (Var x)" by blast
    from reduct_ordstep[OF u(1)] 2(1)[OF u, THEN ground_join_rel.rewrite_left] show ?case
      unfolding oo by auto
  next
    case (3 f ss g ts)
    let ?s = "Fun f ss" and ?t = "Fun g ts"
    from 3(4)[unfolded defs] have alts:"Fun f ss = Fun g ts \<or> isOK (check_instance (E @ R) ?s ?t) \<or>
    (\<exists>u \<in> ?reducts ?s. ?ok u ?t) \<or> (\<exists>u \<in> ?reducts ?t. ?ok ?s u) \<or>
    (f = g \<and> length ss = length ts \<and> (\<forall>p \<in> set (zip ss ts). case p of (si, ti) \<Rightarrow> ?ok si ti)) \<or>
    isOK(check_var_orders_joinable E R ?s ?t)"
      unfolding isOK_update_error isOK_choice isOK_check isOK_existsM isOK_forallM isOK_if_error by fastforce
    { assume "Fun f ss = Fun g ts"
      hence ?case using ground_join_rel.refl by auto
    } note refl = this
    { assume "isOK (check_instance (E @ R) ?s ?t)"
      with ground_join_rel.step[of _ _ "set (E @ R)" ?s \<box> _ ?t] have ?case unfolding check_instance by auto
      (*FIXME admit steps with contexts*)
    } note step = this
    { assume "\<exists>u \<in> ?reducts ?s. ?ok u ?t"
      then obtain u where u:"u \<in> ?reducts ?s" "?ok u ?t" by blast
      from reduct_ordstep[OF u(1)]  3(1)[OF u, THEN ground_join_rel.rewrite_left] have ?case
        unfolding oo by auto
    } note rewritel = this
    { assume "\<exists>u \<in> ?reducts ?t. ?ok ?s u"
      then obtain u where u:"u \<in> ?reducts ?t" "?ok ?s u" by blast
      from reduct_ordstep[OF u(1)] 3(2)[OF u, THEN ground_join_rel.rewrite_right] have ?case
        unfolding oo by auto
    } note rewriter = this
    { assume fg:"f = g" and len: "length ss = length ts" and "\<forall>p \<in> set (zip ss ts). case p of (si, ti) \<Rightarrow> ?ok si ti"
      with 3(3) have "\<And>p. p \<in> set (zip ss ts) \<Longrightarrow> p \<in> ground_join_rel (set (E @ R))" by fast
      hence "\<forall>i<length ss. (ss ! i, ts ! i) \<in> ground_join_rel (set (E @ R))"
        unfolding set_zip len by auto
      with ground_join_rel.congg[of ?s f ss ?t ts, OF _ _ len] have ?case unfolding fg by auto
    } note cong = this
    { assume "isOK(check_var_orders_joinable E R ?s ?t)"
      from check_var_orders_joinable[OF] this ground_join_rel.var_order have ?case by simp
    }
    with alts refl rewritel rewriter step cong show ?case by fast
  qed
qed

lemma check_ground_join_rel:
  assumes "isOK(check_ground_join_rel E R s t)"
  shows "(s,t) \<in> ground_join_rel (set (E @ R))"
  using assms check_aux[THEN check_aux_sound, of s t]
  unfolding check_ground_join_rel_def isOK_bot_def isOK_def
  by (cases "check_ground_join_rel_bot E R s t", auto)
end

lemma check_ground_joinable:
  assumes ok:"isOK(check_ground_join_rel E R s t)"
    and ER_gt_sym:"\<And>s t. (s, t) \<in> (set (E @ R)) \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> (set ((E @ R)))"
  shows "ground_joinable less_set (set (E @ R)) s t"
  using check_ground_join_rel[OF ok] ground_join_rel_fground_joinable[OF C_compatible _ ER_gt_sym]
  by auto
end

context gcr_closure_ops
begin
text \<open>Check ground joinability of one extended overlap.\<close>
definition "check_ooverlap_gj E R \<rho>\<^sub>1 \<rho>\<^sub>2 p =
  (case mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) of
    None \<Rightarrow> succeed
  | Some (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow>
    let s = replace_at (fst \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (snd \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1) in
    let t = snd \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2 in
    check_ground_join_rel E R s t)"


text \<open>Check all extended critical pairs.\<close>
definition check_ECPs_gj :: " ('a, 'v) rules \<Rightarrow> ('a, 'v) rules \<Rightarrow> showsl check"
  where
  "check_ECPs_gj E R =
    (let E' = sym_list E; S = List.union R E' in
    check_allm
      (\<lambda>\<rho>\<^sub>2. let l\<^sub>2 = fst \<rho>\<^sub>2 in check_allm (\<lambda>\<rho>\<^sub>1. check_allm (\<lambda>p. check_ooverlap_gj E' R \<rho>\<^sub>1 \<rho>\<^sub>2 p) (fun_poss_list l\<^sub>2)) S)
      S)  <+? (\<lambda>str. showsl_lit (STR ''Not all extended CPs are ground joinable.'') \<circ> str)"
end

lemmas [code] =
  gcr_closure_ops.check_ooverlap_gj_def gcr_closure_ops.check_ECPs_gj_def


context gtotal_moc_closure_spec
begin
(* FIXME refactor, share parts with check_ECPs_ooverlap*)
lemma check_ECPs_ooverlap_gj:
  assumes "isOK (check_ECPs_gj E R)"
    and "ooverlap {\<succ>} (set (Rules E R)) r r' p \<mu> s t"
    and R: "set R \<subseteq> {\<succ>}"
  shows "ground_joinable less_set (set (Rules E R)) s t"
proof -
  let ?R = "set (Rules E R)"
  from assms(2) obtain \<pi>\<^sub>1 and \<pi>\<^sub>2 where rules': "\<pi>\<^sub>1 \<bullet> r \<in> ?R" "\<pi>\<^sub>2 \<bullet> r' \<in> ?R"
    and disj: "vars_rule r \<inter> vars_rule r' = {}"
    and p': "p \<in> fun_poss (fst r')"
    and mgu': "mgu (fst r) (fst r' |_ p) = Some \<mu>"
    and "\<not> (snd r \<cdot> \<mu> \<succ> fst r \<cdot> \<mu>)" "\<not> (snd r' \<cdot> \<mu> \<succ> fst r' \<cdot> \<mu>)"
    and t: "t = snd r' \<cdot> \<mu>"
    and s: "s = replace_at (fst r' \<cdot> \<mu>) p (snd r \<cdot> \<mu>)"
    unfolding ooverlap_def by fast
  define \<rho>\<^sub>1 and \<rho>\<^sub>2 where "\<rho>\<^sub>1 = \<pi>\<^sub>1 \<bullet> r" and "\<rho>\<^sub>2 = \<pi>\<^sub>2 \<bullet> r'"
  have p: "p \<in> fun_poss (fst \<rho>\<^sub>2)"
    and "\<rho>\<^sub>1 \<in> ?R" and "\<rho>\<^sub>2 \<in> ?R"
    using p' and rules' by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def rule_pt.fst_eqvt [symmetric])
  with assms have *: "isOK (check_ooverlap_gj (sym_list E) R \<rho>\<^sub>1 \<rho>\<^sub>2 p)" by (auto simp: check_ECPs_gj_def)
      
  have "(fst r' |_ p) \<cdot> \<mu> = fst r \<cdot> \<mu>" using mgu' [THEN mgu_sound] by (auto simp: is_imgu_def)
  then have "(fst r' |_ p) \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2) \<circ> Rep_perm \<pi>\<^sub>2) =
    fst r \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1) \<circ> Rep_perm \<pi>\<^sub>1)"
    by (simp add: o_assoc [symmetric] Rep_perm_add [symmetric] Rep_perm_0)
  then have "fst \<rho>\<^sub>2 |_ p \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2)) = fst \<rho>\<^sub>1 \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1))"
    using p [THEN fun_poss_imp_poss]
    by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def permute_term_subst_apply_term [symmetric] eqvt)
  from mgu_var_disjoint_generic_complete [OF ren this[symmetric]] obtain \<mu>\<^sub>1 \<mu>\<^sub>2 \<delta>
    where mgu: "mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    and **: "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>1) = \<mu>\<^sub>1 \<circ>\<^sub>s \<delta>" "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>2) = \<mu>\<^sub>2 \<circ>\<^sub>s \<delta>" by blast

  have "vars_term (fst r) \<subseteq> vars_rule r" and "vars_term (fst r' |_ p) \<subseteq> vars_rule r'"
    using p' [THEN fun_poss_imp_poss, THEN vars_term_subt_at] by (auto simp: vars_defs)
  from mgu_imp_mgu_var_disjoint [OF mgu' ren disj this finite_vars_rule finite_vars_rule, of \<pi>\<^sub>1 \<pi>\<^sub>2]
  obtain \<mu>' and \<pi>
    where left: "\<forall>x\<in>vars_rule r. \<mu> x = (sop \<pi>\<^sub>1 \<circ>\<^sub>s (\<mu>' \<circ> xvar) \<circ>\<^sub>s sop (- \<pi>)) x" (is "\<forall>x\<in>_. \<mu> x = ?\<pi>\<^sub>1 x")
      and right: "\<forall>x\<in>vars_rule r'. \<mu> x = (sop \<pi>\<^sub>2 \<circ>\<^sub>s (\<mu>' \<circ> yvar) \<circ>\<^sub>s sop (- \<pi>)) x" (is "\<forall>x\<in>_. \<mu> x = ?\<pi>\<^sub>2 x")
      and "mgu (\<pi>\<^sub>1 \<bullet> (fst r) \<cdot> (Var \<circ> xvar)) (\<pi>\<^sub>2 \<bullet> (fst r' |_ p) \<cdot> (Var \<circ> yvar)) = Some \<mu>'"
    by blast
  then have "mgu_var_disjoint_generic xvar yvar (fst \<rho>\<^sub>1) (fst \<rho>\<^sub>2 |_ p) = Some (\<mu>' \<circ> xvar, \<mu>' \<circ> yvar)"
    and \<mu>\<^sub>1: "\<mu>\<^sub>1 = \<mu>' \<circ> xvar" and \<mu>\<^sub>2: "\<mu>\<^sub>2 = \<mu>' \<circ> yvar"
    using p' [THEN fun_poss_imp_poss] and mgu
    unfolding \<rho>\<^sub>1_def \<rho>\<^sub>2_def mgu_var_disjoint_generic_def 
    by (auto simp: map_vars_term_eq mgu_var_disjoint_generic_def \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt)

  let ?t = "snd \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2"
  let ?t' = "snd r' \<cdot> \<mu>"
  let ?s = "replace_at (fst \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2) p (snd \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1)"
  let ?s' = "replace_at (fst r' \<cdot> \<mu>) p (snd r \<cdot> \<mu>)"
 
  have "fst r' \<cdot> \<mu> = fst r' \<cdot> ?\<pi>\<^sub>2" and snd_r: "snd r' \<cdot> \<mu> = snd r' \<cdot> ?\<pi>\<^sub>2"
    using right unfolding term_subst_eq_conv by (auto simp: vars_defs)
  then have 1: "fst \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 = \<pi> \<bullet> (fst r' \<cdot> \<mu>)"
    and t': "?t' = -\<pi> \<bullet> ?t" by (auto simp: \<mu>\<^sub>2 \<rho>\<^sub>2_def eqvt)
  
  have "snd r \<cdot> \<mu> = snd r \<cdot> ?\<pi>\<^sub>1"
    using left unfolding term_subst_eq_conv by (auto simp: vars_defs)
  then have 2: "snd \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 = \<pi> \<bullet> (snd r \<cdot> \<mu>)" by (auto simp: \<mu>\<^sub>1 \<rho>\<^sub>1_def eqvt)
  then have s': "?s' = -\<pi> \<bullet> ?s"
    using p' [THEN fun_poss_imp_poss]
    unfolding 1 by (auto simp: eqvt)
  from snd_r have 2: "snd \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 = \<pi> \<bullet> (snd r' \<cdot> \<mu>)" by (auto simp: \<mu>\<^sub>2 \<rho>\<^sub>2_def eqvt)

  have *:"isOK (check_ground_join_rel (sym_list E) R ?s ?t)"
    using * unfolding check_ooverlap_gj_def mgu by auto
  { fix s t assume "(s, t) \<in> set (sym_list E @ R)"
    with R have "s \<succ> t \<or> (t, s) \<in> set (sym_list E @ R)" by auto
  }
  
  from check_ground_joinable[OF * this, simplified] show ?thesis
    unfolding s t s' term_pt.permute_flip [OF 2] 
    by (simp add: ocomp.ground_joinable_permute_litsim sup_commute)
qed

lemma check_ECPs_gj:
  assumes R: "set R \<subseteq> {\<succ>}" and ok: "isOK (check_ECPs_gj E R)"
  shows "GCR (ordstep {\<succ>} (set (Rules E R)))"
proof -
  have [simp]:"\<And>R. FGROUND UNIV R = GROUND R" unfolding GROUND_def FGROUND_def fground_def by auto
  have "\<And>s t. (s, t) \<in> set (Rules E R) \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> set (Rules E R)" using R by auto
  thus ?thesis using check_ECPs_ooverlap_gj[OF ok _ R] ground_joinable_ooverlaps_implies_GCR
     by force
qed
end

(* TODO move KBO stuff *)

text \<open>Closure of ground-total reduction order with respect to a given signature.\<close>
record ('f, 'v) redord_closure =
  ext_less :: "'v list \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  valid :: "showsl check"

hide_const (open) valid ext_less

definition create_KBO_redord_closure :: "(('f :: {showl,compare_order} \<times> nat) \<times> nat \<times> nat \<times> nat list option) list \<times> nat \<Rightarrow>
  ('f \<times> nat) list \<Rightarrow>  ('f, string) redord_closure"
where "create_KBO_redord_closure pr fs = (let
  (ch,p,w,w0,lcs,scf) = prec_weight_repr_to_prec_weight pr;
  ro = create_KBO_redord pr fs :: ('f, string) redord
  in
  \<lparr> redord_closure.ext_less = (\<lambda>vp s t. fst (kbo.kbo_closure w w0 scf (\<lambda>f. f \<in> set lcs) (\<lambda>f g. fst (p f g)) (\<lambda>f g. snd (p f g)) (term_order_of_permx vp) s t)),
    redord_closure.valid = redord.valid ro
  \<rparr>)"

(* end KBO stuff *)

definition check_FGCR_gj ::
  "('f::{compare_order, showl}, string) redord \<Rightarrow> ('f, string) redord_closure \<Rightarrow> ('f \<times> nat) list \<Rightarrow>
   ('f, string) rules \<Rightarrow> ('f, string) rules \<Rightarrow> showsl check"
  where "check_FGCR_gj ro rc F E R = do {
  redord.valid ro;
  redord_closure.valid rc;
  check_subseteq (funas_trs_list (List.union E R)) F
    <+? (\<lambda>f. showsl_lit (STR ''the function symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' does not occur in the TRS\<newline>''));
  gcr_closure_ops.check_ECPs_gj (redord.less ro) (redord.min_const ro) x_var y_var (redord_closure.ext_less rc) E R
}"

declare create_KBO_redord_closure_def check_FGCR_gj_def[code]
 
lemma check_FGCR_gj:
  fixes F :: "('f::{showl,compare_order} \<times> nat) list" and r
  defines "ro \<equiv> create_KBO_redord r F"
  assumes "isOK (check_FGCR_gj ro (create_KBO_redord_closure r F) F E R)"
    and R: "set R \<subseteq> {(s, t). redord.less ro s t}"
  shows "CR (FGROUND (set F) (ordstep {(s, t). redord.less ro s t} (set (Rules E R))))"
proof -
  let ?F = "set F"
  let ?R = "set (Rules E R)"
  let ?roc = "create_KBO_redord_closure r F"

  define less where "less = redord.less ro"
  define ext_less where "ext_less = redord_closure.ext_less ?roc"
  define c where "c = redord.min_const ro"
  define check_ECPs where "check_ECPs = gcr_closure_ops.check_ECPs_gj less c x_var y_var ext_less"

  from assms have valid: "isOK (redord.valid ro)"
    and validc: "isOK (redord_closure.valid ?roc)"
    and ecps: "isOK (check_ECPs E R)"
    and F: "funas_trs ?R \<subseteq> ?F"
    unfolding check_FGCR_gj_def less_def ext_less_def c_def check_ECPs_def
    by (auto simp: check_FGCR_gj_def)

  obtain prw w0 where prw_w0:"r = (prw, w0)" by fastforce
  let ?prw = "prec_weight_repr_to_prec_weight r"
  obtain ch pr w w0' lcs scf where id: "?prw = (ch,pr,w,w0',lcs,scf)" by (cases ?prw, force)
  with prw_w0 have w0[simp]:"w0' = w0" unfolding prec_weight_repr_to_prec_weight_def
    prec_weight_repr_to_prec_weight_funs_def prw_w0 Let_def by fast

  let ?least = "\<lambda>c. c \<in> (set lcs)"
  let ?prs = "\<lambda> f g. fst (pr f g)"
  let ?prw = "\<lambda> f g. snd (pr f g)"
  from valid[unfolded id create_KBO_redord_def ro_def, simplified] have ch_ok:"isOK(ch)" unfolding id by auto

  from KBO_redord.valid [OF valid [unfolded ro_def]] have c:"(c,0) \<in> ?F" and
    ro:"reduction_order less" and
    min_less:"(\<forall>s t. fground ?F s \<and> fground ?F t \<longrightarrow> s = t \<or> less s t \<or> less t s)"
    unfolding c_def less_def by (auto simp: ro_def)
  have aux:"\<And>ro. fgtotal_reduction_order ro UNIV = gtotal_reduction_order ro"
    using gtotal_reduction_order_def by blast
  from ground_total_extension[OF valid [unfolded ro_def] id] obtain prec\<^sub>S prec\<^sub>W less' where
    lessx:"less' = (\<lambda>s t. fst (kbo.kbo w w0 scf ?least prec\<^sub>S prec\<^sub>W s t))" and
    rox:"gtotal_reduction_order less'" and
    less_extend:"\<forall>s t. redord.less ro s t \<longrightarrow> less' s t" and
    minx:"\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun c [])" and
    kbox:"admissible_kbo w w0 prec\<^sub>S prec\<^sub>W ?least scf" and
    prec_ext:"(\<forall>f g. (?prs f g \<longrightarrow> prec\<^sub>S f g) \<and> (?prw f g \<longrightarrow> prec\<^sub>W f g))"
    unfolding c_def w0 aux ro_def by auto

  interpret kbo:admissible_kbo w w0 ?prs ?prw ?least scf
    using prec_weight_repr_to_prec_weight[of r pr w w0' lcs scf, unfolded id] ch_ok
    unfolding isOK_def prw_w0 by (cases ch, auto)
  let ?\<C> = "kbo.kbo_closure"
  have "ext_less = (\<lambda>p s t. fst (?\<C> (term_order_of_permx p) s t))"
    unfolding ext_less_def create_KBO_redord_closure_def
    unfolding id Let_def split w0 term_order_of_perm_def order_set_of_permx by simp
  hence ext_less_eq:"ext_less = (\<lambda>p s t. fst (?\<C> (term_order_of_perm p) s t))"
    unfolding term_order_of_permx_def term_order_of_perm_def order_set_of_permx by simp

  have less_eq:"less = kbo.S" unfolding less_def create_KBO_redord_def ro_def unfolding id Let_def split w0 by simp
  interpret rox: gtotal_reduction_order less' by fact
  interpret kbox: admissible_kbo w w0 prec\<^sub>S prec\<^sub>W ?least scf by fact
  have R: "set R \<subseteq> rox.less_set" using R and less_extend by (auto simp: less_def)

  interpret kboc0:kbo_closure w w0 scf ?least ?prs ?prw ..
  interpret kboc:kbo_closure w w0 scf ?least prec\<^sub>S prec\<^sub>W ..
  interpret two_closures:two_kbo_closures w w0 scf ?least ?prs ?prw ?least prec\<^sub>S prec\<^sub>W ..
  let ?\<C>x = kbox.kbo_closure
  have cext:"\<And>\<O> s t. (fst (?\<C> \<O> s t) \<longrightarrow> fst (?\<C>x \<O> s t)) \<and> (snd (?\<C> \<O> s t) \<longrightarrow> snd (?\<C>x \<O> s t))"
    using two_closures.kbo_closure_prec_mono prec_ext by blast

  (* establish closure conditions *)
  define \<C> :: "('f, string) term rel \<Rightarrow>('f, string) term rel"
    where "\<C> \<equiv> (\<lambda>\<O>. {(s,t) | s t. fst (?\<C>x \<O> s t)})"
  have subst: "\<forall>ord s t \<sigma>. (s, t) \<in> \<C> ord \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> \<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u, v) \<in> ord}"
    using conjunct1[OF kboc.kbo_closure_subst] unfolding \<C>_def by blast
  have mono: "\<forall>ord ord'. ord \<subseteq> ord' \<longrightarrow> \<C> ord \<subseteq> \<C> ord'" using kboc.kbo_closure_mono unfolding \<C>_def by blast
  have "\<forall>s t p. ext_less p s t \<longrightarrow> ((s, t) \<in> \<C> (term_order_of_permx p))"
    unfolding ext_less_def
    unfolding create_KBO_redord_closure_def id split Let_def w0 \<C>_def
    using cext by fastforce
  hence compat: "\<forall>s t p. ext_less p s t \<longrightarrow> ((s, t) \<in> \<C> (term_order_of_perm p))"
    unfolding term_order_of_permx_def term_order_of_perm_def order_set_of_permx by simp
  from kboc.kbo_closure_compatible lessx have compat2:"\<C> rox.less_set \<subseteq> rox.less_set" unfolding \<C>_def by fast

  { fix t :: "('f, string) term"
    assume "fground ?F t" and neq: "t \<noteq> Fun c []"
    with c have fg:"fground ?F t \<and> fground ?F (Fun c [])" unfolding fground_def by auto
    with neq minx[rule_format, of t] have less':"less' t (Fun c [])" unfolding lessx fground_def by auto
    { assume "less (Fun c []) t"
      from less_extend[rule_format, OF this[unfolded less_def]] less'[THEN rox.trans] have "less' t t" by auto
      with SN_imp_acyclic[OF rox.SN_less] have False unfolding acyclic_def lessx by auto
    }
    with neq min_less[rule_format, OF fg] have "less t (Fun c [])" by auto
  }
  hence c_less:"\<forall>t. fground (set F) t \<longrightarrow> t = Fun c [] \<or> less t (Fun c [])" by auto

  { fix p :: "string list"
    { fix t :: "('f, string) term"
      assume "fground ?F t" and "t \<noteq> (Fun c [])"
      with c_less have "less t (Fun c [])" unfolding less_def by auto
      with kbo.kbo_kbo_closure[of t "Fun c []"] have "ext_less p t (Fun c [])" unfolding ext_less_eq less_eq by blast
    }
  } note min_const = this
  have least_compat: "\<And>p. (\<forall>t. (fground ?F t \<longrightarrow> t = Fun c [] \<or> less' t (Fun c []))) \<longrightarrow>
                        (\<forall>t. fground ?F t \<longrightarrow> t = Fun c [] \<or> ext_less p t (Fun c []))" using min_const by auto
  have mono:"\<And>ord ord' a b. ord \<subseteq> ord' \<Longrightarrow> \<C> ord \<subseteq> \<C> ord'" using mono by auto

  (* have conditions of main CR checks *)
  interpret oc: oc_spec less' "\<lambda>s t. check (less' s t) (showsl_lit (STR ''''))" by (unfold_locales) simp
  interpret gcr: gtotal_moc_closure_spec less' less c "set F" x_var y_var ext_less \<C> 
    apply (unfold_locales)
    apply (rule c_less)
    apply (rule compat2)
    apply (simp add:subst)
    apply (rule mono, simp)
    apply (simp add: compat)
    apply(rule least_compat, auto)
    apply(insert less_extend less_def, auto)
    done

  have "isOK (check_ECPs E R)" using ecps by (auto simp: check_ECPs_def)
  then have gcr:"GCR (ordstep rox.less_set ?R)" using gcr.check_ECPs_gj [OF R, of E]
    unfolding check_ECPs_def by simp
  note cr = rox.GCR_imp_CR_FGROUND[of less ?F c, OF _ ro min_less minx c F gcr]
  thus ?thesis unfolding less_def using less_extend less_def by auto
qed

definition check_FGCR_run_with_closure ::
    "('f::{showl,compare_order}, string) redord \<Rightarrow> _ \<Rightarrow> ('f \<times> nat) list \<Rightarrow> _"
  where
    [code]: "check_FGCR_run_with_closure ro rc F E\<^sub>0 R\<^sub>0 E R steps = do {
      let check_ord = (\<lambda>s t.
        check (redord.less ro s t) (showsl_lit (STR ''Term pair cannot be oriented.'')));
      oc_ops.check_oriented check_ord R\<^sub>0;
      oc_ops.check_oc check_ord (E\<^sub>0, R\<^sub>0) (E, R) steps
        <+? (\<lambda>s. showsl_lit (STR ''The oKB run could not be reconstructed.\<newline>\<newline>'') \<circ> s);
      check_FGCR_gj ro rc F E R
        <+? (\<lambda>s. showsl_lit (STR ''Ground confluence could not be verified.\<newline>\<newline>'') \<circ> s)
    }"

lemma check_FGCR_run_with_closure:
  fixes F :: "('f::{showl,compare_order} \<times> nat) list"
    and E :: "(('f, string) term \<times> ('f, string) term) list"
    and r
  defines "ro \<equiv> create_KBO_redord r F"
  assumes "isOK (check_FGCR_run_with_closure ro (create_KBO_redord_closure r F) F E\<^sub>0 R\<^sub>0 E R steps)"
  shows "CR (FGROUND (set F) (ordstep {(s, t). redord.less ro s t} (set (Rules E R)))) \<and>
    set R \<subseteq> {(s, t). redord.less (create_KBO_redord r F) s t} \<and>
    equivalent (set E\<^sub>0 \<union> set R\<^sub>0) (set E \<union> set R)"
proof -
  let ?F = "set F"
  let ?ER = "set (Rules E R)"
  let ?rc = "create_KBO_redord_closure r F"
  define less and c where"less = redord.less ro" and "c = redord.min_const ro"
  define ext_less where "ext_less = redord_closure.ext_less ?rc"
  let ?check_ECPs = "gcr_closure_ops.check_ECPs_gj less c x_var y_var ext_less"
  note ok = assms[unfolded check_FGCR_run_with_closure_def]

  from ok have FGCR:"isOK(check_FGCR_gj ro ?rc F E R)" by auto
  from FGCR have valid: "isOK (redord.valid ro)"
    and validc: "isOK (redord_closure.valid ?rc)"
    and ecps: "isOK (?check_ECPs E R)"
    and F: "funas_trs ?ER \<subseteq> ?F"
    using FGCR unfolding check_FGCR_gj_def less_def ext_less_def c_def by auto

  from KBO_redord.valid [OF valid [unfolded ro_def]] obtain less'
    where ro: "reduction_order less"
      and c: "(c, 0) \<in> ?F"
      and fground: "\<forall>s t. fground ?F s \<and> fground ?F t \<longrightarrow> s = t \<or> less s t \<or> less t s"
      and ro': "gtotal_reduction_order less'"
      and subset: "\<forall>s t. less s t \<longrightarrow> less' s t"
      and min: "\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun c [])"
    by (auto simp: less_def c_def ro_def)

  interpret ro: reduction_order less by fact
  interpret ro': gtotal_reduction_order less' by fact

  define check_ord where "check_ord = (\<lambda>s t. check (less s t) (showsl_lit (STR ''Term pair cannot be oriented.'')))"
  have check_ord: "\<And>s t. isOK (check_ord s t) \<longleftrightarrow> less s t" unfolding check_ord_def by auto
  define check_ord' where "check_ord' = (\<lambda>s t. check (less' s t) (showsl_lit (STR ''Term pair cannot be oriented.'')))"
  have check_ord': "\<And>s t. isOK (check_ord' s t) \<longleftrightarrow> less' s t" unfolding check_ord'_def by auto

  interpret oc: oc_spec less check_ord by (insert check_ord, unfold_locales) simp
  interpret oc': oc_spec less' check_ord' by (insert check_ord', unfold_locales) simp

  from ok have oc_ok: "isOK (oc.check_oc (E\<^sub>0, R\<^sub>0) (E, R) steps)" and
    oriented_ok: "isOK (oc.check_oriented R\<^sub>0)"
    unfolding check_ord_def less_def c_def by force+

  note run = oc.check_oc[OF this]
  let ?variant_trs = "\<lambda> R R'. \<forall>r\<in>set R :: (_,_) trs. \<exists>p. p \<bullet> r \<in> set R'"
  from run obtain E\<^sub>\<pi> R\<^sub>\<pi> where run\<^sub>\<pi>:"oc.oKB'\<^sup>*\<^sup>* (set E\<^sub>0, set R\<^sub>0) (set E\<^sub>\<pi>, set R\<^sub>\<pi>)" and
    vs:"set R\<^sub>\<pi> \<doteq> set R" "set E\<^sub>\<pi> \<doteq> set E" by auto
  note litsim = Litsim_Trs.subsumable_trs.litsim_def[unfolded Litsim_Trs.subsumeseq_trs_def]
  note oriented = oc.check_oriented[OF oriented_ok]
  with run\<^sub>\<pi>[THEN oc.oKB'_rtrancl_less] vs(1) have R_less:"set R \<subseteq> ro.less_set"
    using oc.less_set_permute litsim by (meson oc.R_less_litsim_R_less subsumable_trs.litsim_sym)
  note cr =  check_FGCR_gj[OF FGCR [unfolded ro_def]]

  from vs have "set E\<^sub>\<pi> \<union> set R\<^sub>\<pi> \<doteq> set E \<union> set R" using litsim by (simp add: litsim_union)
  note rstep_eq = litsim_rstep_eq[OF this]
  note equiv = oc.oKB_steps_conversion_permuted [OF run\<^sub>\<pi>]
  with cr R_less show ?thesis unfolding equivalent_def less_def rstep_eq by (simp add: ro_def)
qed

subsection \<open>Checking Ordered Completion Proofs\<close>

datatype ('f, 'v) ordered_completion_proof = OKB "('f, 'v) oc_irule list"

primrec check_ordered_completion_proof ::
  "showsl \<Rightarrow> ('f::{compare_order,showl}, string) equation list \<Rightarrow>
    ('f, string) equation list \<Rightarrow> ('f, string) rules \<Rightarrow>
    'f reduction_order_input \<Rightarrow> ('f, string) ordered_completion_proof \<Rightarrow>
    showsl check"
  where
    "check_ordered_completion_proof i E\<^sub>0 E R ro (OKB steps) = debug i (STR ''OKB'') (do {
      (case ro of
        KBO_Input precw \<Rightarrow>
          let F = precw_w0_sig precw in
          check_FGCR_run (create_KBO_redord precw F) F E\<^sub>0 [] E R steps
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in ground completeness proof \<newline>'') \<circ> s)
      |  _ \<Rightarrow> error (showsl_lit (STR ''unsupported reduction order '')))
    })"

lemma check_ordered_completion_proof_sound:
  assumes "isOK (check_ordered_completion_proof i E\<^sub>0 E R ro p)"
  shows "ordered_completed_rewrite_system (set E\<^sub>0) (set E) (set R) ro"
proof -
  obtain steps where "p = OKB steps" by (cases p, auto)
  note assms = assms [unfolded check_ordered_completion_proof_def this Let_def]
  then obtain precw_w0 where ro: "ro = KBO_Input precw_w0" by (cases ro, auto)
  let ?F = "precw_w0_sig precw_w0"
  let ?ro = "create_KBO_redord precw_w0 ?F :: ('a, string) redord"
  obtain precw w0 where pw0: "precw_w0 = (precw, w0)" by (cases precw_w0, auto)
  let ?pwfuns = "prec_weight_repr_to_prec_weight_funs precw_w0"
  let ?pw = "prec_weight_repr_to_prec_weight precw_w0"
  note assms = assms [unfolded ro]
  then have run_ok: "isOK (check_FGCR_run ?ro ?F E\<^sub>0 [] E R steps)" by auto
  then have FGCR: "isOK (check_FGCR ?ro ?F E R)" by (auto simp: check_FGCR_run_def)
  then have valid: "isOK (redord.valid ?ro)" by (auto simp: check_FGCR_def)
  then obtain p w lcs scf where pwfuns: "?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  obtain ok scf' where pw: "?pw = (ok, p, w, w0, lcs, scf_repr_to_scf scf)"
    unfolding prec_weight_repr_to_prec_weight_def Let_def pwfuns unfolding pw0 split by (cases ?pw, simp)
  note remember = KBO_redord.valid
  let ?scf = "scf_repr_to_scf scf"
  let ?less = "\<lambda>s t. fst (kbo.kbo w w0 ?scf (\<lambda>f. f \<in> set lcs) (\<lambda>f g. fst (p f g)) (\<lambda>f g. snd (p f g)) s t)"
  have less: "redord.less (create_KBO_redord precw_w0 ?F) = ?less"
    unfolding pw create_KBO_redord_def Let_def split by force
  then have o: "ordstep {(x, y). redord.less (create_KBO_redord precw_w0 ?F) x y} (set (Rules E R)) =
    ordstep {(x, y). ?less x y} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
    unfolding less Rules_def set_union set_sym_list Un_commute [of "set R"] by blast
  from check_FGCR_run [OF run_ok] show ?thesis unfolding ordered_completed_rewrite_system_def ro o
    using pwfuns pw unfolding pw0 precw_w0_sig_def by simp
qed

primrec check_ordered_completion_proof_ext ::
  "showsl \<Rightarrow> ('f::{compare_order,showl}, string) equation list \<Rightarrow>
    ('f, string) equation list \<Rightarrow> ('f, string) rules \<Rightarrow>
    'f reduction_order_input \<Rightarrow> ('f, string) ordered_completion_proof \<Rightarrow>
    showsl check"
  where
    "check_ordered_completion_proof_ext i E\<^sub>0 E R ro (OKB steps) = debug i (STR ''OKB'') (do {
      (case ro of
        KBO_Input precw \<Rightarrow>
          let F = map fst (fst precw) in
          check_FGCR_run_with_closure (create_KBO_redord precw F) (create_KBO_redord_closure precw F) F E\<^sub>0 [] E R steps
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in ground completeness proof with closure\<newline>'') \<circ> s)
      |  _ \<Rightarrow> error (showsl_lit (STR ''unsupported reduction order\<newline>'')))
    })"

lemma check_ordered_completion_proof_ext_sound:
  assumes "isOK (check_ordered_completion_proof_ext i E\<^sub>0 E R ro p)"
  shows "ordered_completed_rewrite_system (set E\<^sub>0) (set E) (set R) ro"
proof -
  let ?F = "funas_trs_list E\<^sub>0"
  obtain steps where "p = OKB steps" by (cases p, auto)
  note assms = assms [unfolded check_ordered_completion_proof_def this Let_def]
  then obtain precw_w0 where ro: "ro = KBO_Input precw_w0" by (cases ro, auto)
  obtain precw w0 where pw0: "precw_w0 = (precw, w0)" by (cases precw_w0, auto)
  let ?F = "map fst (fst precw_w0)"
  let ?pwfuns = "prec_weight_repr_to_prec_weight_funs precw_w0"
  let ?pw = "prec_weight_repr_to_prec_weight precw_w0"
  let ?ro = "create_KBO_redord precw_w0 ?F :: ('a, string) redord"
  let ?rc = "create_KBO_redord_closure precw_w0 ?F"
  note assms = assms [unfolded ro]
  then have run_ok: "isOK (check_FGCR_run_with_closure ?ro ?rc ?F E\<^sub>0 [] E R steps)" by auto
  then have FGCR: "isOK (check_FGCR_gj ?ro ?rc ?F E R)" by (auto simp: check_FGCR_run_with_closure_def)
  then have valid: "isOK (redord.valid ?ro)" and
    validc: "isOK (redord_closure.valid ?rc)" by (auto simp: check_FGCR_gj_def)
  then obtain p w lcs scf where pwfuns: "?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  obtain ok scf' where pw: "?pw = (ok, p, w, w0, lcs, scf_repr_to_scf scf)"
    unfolding prec_weight_repr_to_prec_weight_def Let_def pwfuns unfolding pw0 split by (cases ?pw, simp)
  note remember = KBO_redord.valid
  let ?scf = "scf_repr_to_scf scf"
  let ?less = "\<lambda>s t. fst (kbo.kbo w w0 ?scf (\<lambda>f. f \<in> set lcs) (\<lambda>f g. fst (p f g)) (\<lambda>f g. snd (p f g)) s t)"
  have less: "redord.less (create_KBO_redord precw_w0 ?F) = ?less"
    unfolding pw create_KBO_redord_def Let_def split by force
  then have o: "ordstep {(x, y). redord.less (create_KBO_redord precw_w0 ?F) x y} (set (Rules E R)) =
    ordstep {(x, y). ?less x y} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
    unfolding less Rules_def set_union set_sym_list Un_commute [of "set R"] by blast
  from check_FGCR_run_with_closure [OF run_ok] show ?thesis unfolding ordered_completed_rewrite_system_def
    unfolding ro o reduction_order_input.splits 
    using Un_commute[of "set R"]
    apply (simp, unfold pwfuns less precw_w0_sig_def)
    apply (insert Un_commute[of "set R"], auto)
    done
qed


lemma equational_disproof_by_ground_completeness:
  fixes gt and E and R
  assumes "(fground F s \<and> fground F t \<and> funas_trs (set E\<^sub>0) \<subseteq> F) \<and> reduction_order gt"
         (is "?sig \<and> ?ro")
  defines "gt_ordstep \<equiv> ordstep {(s,t). gt s t} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
  assumes "CR (FGROUND F gt_ordstep) \<and>
         (FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>* \<and>
         (\<exists>s' t'. (s, s') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> (t, t') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> s' \<noteq> t')"
         (is "?CR \<and> ?FGROUND_subset \<and> ?NFs")
  shows "(s, t) \<notin> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from assms obtain s' t' where
    fground: "fground F s" "fground F t" and sig_E0:"funas_trs (set E\<^sub>0) \<subseteq> F" and
    rord:"reduction_order gt" and
    CR:"CR (FGROUND F gt_ordstep)" and
    conv_eq:"(FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" and
    s':"(s, s') \<in> (FGROUND F gt_ordstep)\<^sup>!" and t':"(t, t') \<in> (FGROUND F gt_ordstep)\<^sup>!" and neq:"s' \<noteq> t'"
    by blast

  from rtrancl_FGROUND_fground[OF _ fground(1)] s' have fgs:"fground F s'"
    unfolding normalizability_def by blast
  from rtrancl_FGROUND_fground[OF _ fground(2)] t' have fgt:"fground F t'"
    unfolding normalizability_def by blast

  { assume "(s,t) \<in> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
    from fgterm_conv_FGROUND_conv[OF sig_E0 fground this]
    conv_eq have conv:"(s, t) \<in> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    note sn = reduction_order.SN_FGROUND_ordstep[OF rord, of F "(set E)\<^sup>\<leftrightarrow> \<union> set R"]
    have "semi_complete (FGROUND F gt_ordstep)"
      using SN_imp_WN[OF sn] CR unfolding semi_complete_on_def gt_ordstep_def by blast
    note conv = conv[unfolded semi_complete_imp_conversionIff_same_NF[OF this]]
    from this[rule_format, of s' t'] s' t' Un_commute[of "set R"] have "s' = t'" unfolding set_Rules by auto
    with neq have False ..
  }
  thus ?thesis .. 
qed

definition check_equational_disproof_oc ::
  "showsl \<Rightarrow>('f :: {compare_order,showl}, string) equation \<Rightarrow>
    ('f :: {compare_order,showl}, string) equation list \<Rightarrow> ('f, string) equation list \<Rightarrow>
    ('f, string) rules \<Rightarrow> 'f reduction_order_input \<Rightarrow> ('f, string) ordered_completion_proof \<Rightarrow>
    showsl check"
  where
    [code]: "check_equational_disproof_oc i eq E\<^sub>0 E R ro p =
      (case ro of KBO_Input precw \<Rightarrow> do {
        check_ordered_completion_proof_ext i E\<^sub>0 E R ro p;
        let ro = create_KBO_redord precw (precw_w0_sig precw);
        let (s, t) = eq;
        check_ground_term s <+? (\<lambda>m. showsl s \<circ> showsl_lit (STR '' is not a ground term\<newline>''));
        check_ground_term t <+? (\<lambda>m. showsl t \<circ> showsl_lit (STR '' is not a ground term\<newline>''));
        check_subseteq (funas_rule_list (s, t)) (precw_w0_sig precw)
          <+? (\<lambda>m. showsl_lit (STR '' goal is not over expected signature\<newline>''));
        check_subseteq (funas_trs_list (E\<^sub>0 @ E @ R)) (precw_w0_sig precw)
          <+? (\<lambda>m. showsl_lit (STR '' system is not over expected signature\<newline>''));
        let nf = moc_ops.compute_mordstep_NF (redord.less ro) (redord.min_const ro) (Rules E R); 
        (case (nf s, nf t) of
          (Some s', Some t') \<Rightarrow> (
            if s' \<noteq> t' then Inr ()
            else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' have same normal form '') \<circ> showsl s'))
        | _ \<Rightarrow> error (showsl_lit (STR ''error when computing normal forms of '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t)
      )}
      | _ \<Rightarrow> error (showsl_lit (STR ''unsupported reduction order'')))"

lemma check_equational_disproof_for_infeasibility:
  assumes ok: "isOK (check_equational_disproof_oc i (s, t) E\<^sub>0 E R (KBO_Input precw_w0) ocp)"
  defines "F \<equiv> set (precw_w0_sig precw_w0) :: ('f :: {compare_order,showl} \<times> nat) set"
      and "gt \<equiv> redord.less (create_KBO_redord precw_w0 (precw_w0_sig precw_w0) :: ('f, string) redord)"
  defines "gt_ordstep \<equiv> ordstep {(s,t). gt s t} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
  shows "(fground F s \<and> fground F t \<and> funas_trs (set E\<^sub>0) \<subseteq> F) \<and>
         reduction_order gt \<and>
         CR (FGROUND F gt_ordstep) \<and>
         (FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>* \<and>
         (\<exists>s' t'. (s, s') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> (t, t') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> s' \<noteq> t')"
         (is "?sig \<and> ?ro \<and> ?CR \<and> ?FGROUND_subset \<and> ?NFs")
proof -
  let ?pwfuns = "prec_weight_repr_to_prec_weight_funs precw_w0"
  let ?F = "precw_w0_sig precw_w0"
  define ro where "ro \<equiv> create_KBO_redord precw_w0 ?F :: ('f, string) redord"
  define rc where "rc \<equiv> create_KBO_redord_closure precw_w0 ?F"
  note ok = ok[unfolded check_equational_disproof_oc_def Let_def, simplified] 
  from ok have ocp_ok:"isOK(check_ordered_completion_proof_ext i E\<^sub>0 E R (KBO_Input precw_w0) ocp)" and
    sig_st: "ground s" "ground t" "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" and
    sig_E\<^sub>0:"funas_trs (set E\<^sub>0) \<subseteq> F" and sig_ER:"funas_trs (set E \<union> set R) \<subseteq> F"
    unfolding F_def funas_rule_def by auto
  hence fg:"fground F s" "fground F t" unfolding fground_def by auto
  obtain steps where ocp:"ocp = OKB steps" by (cases ocp, auto)
  obtain precw w0 where pw0: "precw_w0 = (precw, w0)" by (cases precw_w0, auto)
  define c where "c \<equiv> redord.min_const ro"
  let ?gt_set = "{(s,t). gt s t}"

  obtain p w lcs scf where pwfuns:"?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  let ?pw = "prec_weight_repr_to_prec_weight precw_w0"
  from ocp_ok have ok':"isOK (check_FGCR_run_with_closure ro rc ?F E\<^sub>0 [] E R steps)" 
    unfolding check_ordered_completion_proof_ext_def ro_def rc_def ocp precw_w0_sig_def by simp
  from ok' have valid: "isOK (redord.valid ro)"
    unfolding check_ordered_completion_proof_ext_def ro_def rc_def
    unfolding check_FGCR_run_with_closure_def check_FGCR_gj_def F_def[symmetric] by simp
  then obtain p w lcs scf where pwfuns: "?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  obtain ch where pw: "?pw = (ch, p, w, w0, lcs, scf_repr_to_scf scf)"
    unfolding prec_weight_repr_to_prec_weight_def Let_def pwfuns unfolding pw0 split by (cases ?pw, simp)
  from valid[unfolded ro_def create_KBO_redord_def] have ch_ok:"isOK(ch)" unfolding pw by auto
  let ?scf = "scf_repr_to_scf scf"
  let ?gt = "\<lambda>s t :: ('f, string) term. fst (kbo.kbo w w0 ?scf (\<lambda>f. f \<in> set lcs) (\<lambda>f g. fst (p f g)) (\<lambda>f g. snd (p f g)) s t)"
  have gt: "gt = ?gt" unfolding pw create_KBO_redord_def Let_def gt_def using pwfuns by auto
  from check_FGCR_run_with_closure[OF ok'[unfolded ro_def rc_def]] have R_less:"set R \<subseteq> ?gt_set"
    unfolding gt_def by auto

  note OCR = check_ordered_completion_proof_ext_sound[OF ocp_ok]
  from this[unfolded ordered_completed_rewrite_system_def, simplified, unfolded pwfuns, simplified] have
    equiv:"equivalent (set E\<^sub>0) (set E \<union> set R)" and
    CR:"CR (FGROUND F gt_ordstep)" unfolding F_def gt_ordstep_def gt unfolding equivalent_def by auto

  interpret kbo:admissible_kbo w w0 "\<lambda>f g. fst (p f g)" "\<lambda>f g. snd (p f g)" "\<lambda>c. c \<in> (set lcs)" ?scf
    using prec_weight_repr_to_prec_weight[of precw_w0 p w w0 lcs] ch_ok
    unfolding isOK_def pw by (cases ch, auto)

  from KBO_redord.valid [OF valid[unfolded ro_def]] gt
  obtain gt' :: "('f, string) term  \<Rightarrow> ('f, string) term \<Rightarrow> bool" where
    least_F:"(c,0) \<in> F" and
    rord:"reduction_order gt" and
    ftotal:"\<forall>s t. fground F s \<and> fground F t \<longrightarrow> s = t \<or> gt s t \<or> gt t s" and
    gtotal_ro:"gtotal_reduction_order gt'" and
    ext:"\<forall>s t. gt s t \<longrightarrow> gt' s t" and
    min':"\<forall>t. ground t \<longrightarrow> gt'\<^sup>=\<^sup>= t (Fun c [])"
    unfolding gt_def c_def[symmetric] F_def[symmetric] ro_def[symmetric] rc_def[symmetric] by auto
  from gtotal_reduction_order.axioms gtotal_ro have rordx:"reduction_order gt'"
    using fgtotal_reduction_order.axioms by auto
  from valid have c:"c \<in> set lcs" unfolding c_def create_KBO_redord_def pw Let_def ro_def by fastforce
  from ftotal[rule_format, of "Fun c []"] kbo.not_S_least[OF c] least_F have
    "\<forall>t:: ('f, string) term. (fground F t \<longrightarrow> t = Fun c [] \<or> ?gt t (Fun c []))"
    unfolding fground_def gt by (simp, blast)
  then interpret moc:moc_spec ?gt c F unfolding c_def by (unfold_locales, simp)

  have FG:?FGROUND_subset proof
    fix u v :: "('f, string) term"
    assume *:"(u, v) \<in> (FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>*" 
    have FG_sym:"\<And>R. (FGROUND F R)\<^sup>\<leftrightarrow> = FGROUND F (R\<^sup>\<leftrightarrow>)" unfolding FGROUND_def by auto
    show "(u, v) \<in> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" proof(cases "u = v", simp)
      case False
      with * have fgu:"fground F u" unfolding FG_sym conversion_def unfolding FGROUND_def
        by (metis IntE converse_rtranclE mem_Collect_eq mem_Sigma_iff)
      from rtrancl_FGROUND_fground[of u v, OF *[unfolded conversion_def FG_sym]] fgu
      have fg:"fground F u" "fground F v" and conv:"(u, v) \<in> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding conversion_def by auto
      from conv[unfolded equiv[unfolded equivalent_def]] have conv: "(u,v) \<in> (rstep (set E \<union> set R))\<^sup>\<leftrightarrow>\<^sup>*" by simp
      from fgterm_conv_FGROUND_conv[OF sig_ER fg conv] have conv:"(u, v) \<in> (FGROUND F (rstep (set E \<union> set R)))\<^sup>\<leftrightarrow>\<^sup>*" by auto
      from reduction_order.FGROUND_conversion_ordsteps[OF rord ftotal[rule_format] R_less, of F] conv
      show "(u, v) \<in> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" unfolding gt_ordstep_def by auto
    qed
  qed

  have NFs:?NFs proof -
    let ?mordstep_nf = "moc_ops.compute_mordstep_NF gt c (Rules E R)"
    note ok = ok[folded ro_def rc_def c_def]
    from ok c_def obtain s' where s': "?mordstep_nf s = Some s'"
      by (cases "?mordstep_nf s", simp add:gt_def ro_def, blast)
    with ok c_def obtain t' where t': "?mordstep_nf t = Some t'"
      by (cases "?mordstep_nf t", simp add:gt_def ro_def, blast)
    from conjunct2[OF ok, unfolded ro_def gt_def[symmetric] s' t'] have neq: "s' \<noteq> t'" by auto
    from s' t' have s'':"moc.compute_mordstep_NF (Rules E R) s = Some s'" and
      t'':"moc.compute_mordstep_NF (Rules E R) t = Some t'" using moc.moc_spec_axioms
      unfolding gt by auto
    have sig_Rules:"funas_trs(set (Rules E R)) \<subseteq> F" using sig_ER by auto
    have "moc.all_less \<subseteq> {(s,t). gt' s t}" using ext gt by auto

    note NF_complete = moc.compute_mordstep_NF_complete[OF _ this, folded gt, OF _ rord rordx]
    note NF_complete = NF_complete[unfolded gt, OF _ ftotal[unfolded gt] min'[unfolded gt] least_F sig_Rules]
    { fix w w' :: "('f,string) term"
      assume fg:"fground F w" and seq:"moc.compute_mordstep_NF (Rules E R) w = Some w'"
      from sig_ER have sig':"funas_trs (set (Rules E R)) \<subseteq> F" by auto
      note mordsteps_FGROUND = mordsteps_FGROUND[OF least_F this]
      note * = rtrancl_mono[OF FGROUND_mono[OF mordstep_ordstep], of F c moc.all_less]
      from moc.compute_mordstep_NF_sound'[OF seq] mordsteps_FGROUND[OF fg] *
      have uu':"(w, w') \<in> (FGROUND F gt_ordstep)\<^sup>*"
        unfolding gt_ordstep_def gt set_Rules using Un_commute[of "set R"] by auto
      with rtrancl_FGROUND_fground[OF _fg] have fg':"fground F w'" by blast
      with NF_complete[OF seq fg'] have nf:"w' \<in> NF (GROUND gt_ordstep)" unfolding gt_ordstep_def
        unfolding gt using Un_commute[of "set R"] by simp
      from FGROUND_GROUND have "\<And>R. FGROUND F R \<subseteq> GROUND R" by auto
      from NF_anti_mono[OF this] nf uu' fg' have "(w, w') \<in> (FGROUND F gt_ordstep)\<^sup>!" "fground F w'"
        unfolding normalizability_def by auto
    } note nfs = this[OF fg(1) s''] this[OF fg(2) t'']
    show ?NFs by (rule exI[of _ s'], rule exI[of _ t'], insert nfs neq, auto)
  qed
  from sig_E\<^sub>0 sig_st CR rord FG NFs show ?thesis unfolding fground_def by auto
qed

lemma check_equational_disproof:
  assumes ok:"isOK (check_equational_disproof_oc i eq E\<^sub>0 E R ro ocp)"
  shows "eq \<notin> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  note ok = ok[unfolded check_equational_disproof_oc_def] 
  from ok obtain s t where eq:"eq = (s,t)" by (cases eq, auto)
  from ok obtain precw_w0 where ro:"ro = KBO_Input precw_w0" by (cases ro, auto)

  let ?F = "set (precw_w0_sig precw_w0)"
  let ?less = "redord.less (create_KBO_redord precw_w0 (precw_w0_sig precw_w0)) :: ('a, string) term \<Rightarrow> _ \<Rightarrow> bool"
  let ?ordstep = "ordstep {(s, t). ?less s t} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
  note check = check_equational_disproof_for_infeasibility[OF assms[unfolded eq ro]]
  then obtain s' t' where
    fground: "fground ?F s" "fground ?F t" and sig_E0:"funas_trs (set E\<^sub>0) \<subseteq> ?F" and
    rord:"reduction_order ?less" and
    CR:"CR (FGROUND ?F ?ordstep)" and
    conv_eq:"(FGROUND ?F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND ?F ?ordstep)\<^sup>\<leftrightarrow>\<^sup>*" and
    s':"(s, s') \<in> (FGROUND ?F ?ordstep)\<^sup>!" and t':"(t, t') \<in> (FGROUND ?F ?ordstep)\<^sup>!" and neq:"s' \<noteq> t'"
    by blast

  with eq equational_disproof_by_ground_completeness show ?thesis by blast
qed

subsection \<open>Checking equational disproof via ground-complete system.
Note that equivalence of the ground-complete system to the original system is not neccesary
for disproof, and thus only subsumption is checked.\<close>

definition
  ground_complete_rewrite_system :: "('f::{compare_order,showl}, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow> 'f reduction_order_input \<Rightarrow> bool"
where
  "ground_complete_rewrite_system E R F ord \<equiv>
   case ord of KBO_Input precw \<Rightarrow>
     let less = redord.less (create_KBO_redord precw F) in
     CR (FGROUND (set F) (ordstep {(s, t). less s t} (R \<union> E\<^sup>\<leftrightarrow>)))"

definition check_ground_completeness ::
  "showsl \<Rightarrow> ('f::{compare_order,showl}, string) equation list \<Rightarrow> ('f, string) rules  \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow> 'f reduction_order_input \<Rightarrow> showsl check"
  where
    "check_ground_completeness i E R F ro = debug i (STR ''check ground completeness'') (do {
      (case ro of
        KBO_Input precw \<Rightarrow> (let kbo = (create_KBO_redord precw F) in do {
          check (list_all (\<lambda> (s, t). redord.less kbo s t) R) (showsl_lit (STR ''found unorientable rule in R''));
          check_FGCR_gj kbo (create_KBO_redord_closure precw F) F E R 
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in ground confluence proof \<newline>'') \<circ> s)
        })
      |  _ \<Rightarrow> error (showsl_lit (STR ''unsupported reduction order '')))
    })"

lemma check_ordered_compelteness:
  assumes "isOK (check_ground_completeness i E R F ro)"
  shows "ground_complete_rewrite_system (set E) (set R) F ro"
proof -
  obtain precw where
    "ro = KBO_Input precw" and
    R: "(list_all (\<lambda> (s, t). redord.less (create_KBO_redord precw F) s t) R)" and
    GCR: "isOK (check_FGCR_gj (create_KBO_redord precw F) (create_KBO_redord_closure precw F) F E R )"
    using assms[unfolded check_ground_completeness_def, simplified] by (auto split: reduction_order_input.splits)
  note [simp] = this(1)
  let ?less = "redord.less (create_KBO_redord precw F)"
  have  R: "set R \<subseteq> {(s, t). ?less s t}"
    using R unfolding subset_iff list_all_iff by fast
  then have "CR (FGROUND (set F) (ordstep {(s, t). ?less s t} (set (Rules E R))))"
    using check_FGCR_gj GCR by meson
  then show ?thesis unfolding ground_complete_rewrite_system_def by (auto simp: Let_def)
qed

thm gtotal_moc_closure_spec.check_ground_joinable (* TODO: nice to have a wrapper of this lemma? (locale part is annoying) *)

definition check_equational_disproof_by_ground_complete_system ::
  "showsl \<Rightarrow>('f :: {compare_order,showl}, string) equation \<Rightarrow>
    ('f :: {compare_order,showl}, string) equation list \<Rightarrow> ('f, string) equation list \<Rightarrow>
    ('f, string) rules \<Rightarrow> 'f reduction_order_input \<Rightarrow> showsl check"
  where
    [code]: "check_equational_disproof_by_ground_complete_system i eq E\<^sub>0 E R ro =
      (case ro of KBO_Input precw \<Rightarrow> do {
        let F = precw_w0_sig precw;
        let kbo = create_KBO_redord precw F;
        let kbo_ext = redord_closure.ext_less (create_KBO_redord_closure precw F);
        let (s, t) = eq;
        check_ground_term s <+? (\<lambda>m. showsl s \<circ> showsl_lit (STR '' is not a ground term\<newline>''));
        check_ground_term t <+? (\<lambda>m. showsl t \<circ> showsl_lit (STR '' is not a ground term\<newline>''));
        check_subseteq (funas_rule_list (s, t)) F
          <+? (\<lambda>m. showsl_lit (STR '' goal is not over expected signature\<newline>''));
        check_subseteq (funas_trs_list (E\<^sub>0 @ E @ R)) F
          <+? (\<lambda>m. showsl_lit (STR '' system is not over expected signature\<newline>''));
        check_ground_completeness i E R F ro;
        \<comment> \<open>check E_0 is subsumed by E and R by ground joinability (TODO: alternatively demands equational proofs cf. check_subsumption)\<close>
        \<comment> \<open>NOTE: could be improved by ground joinability checking (maybe inverse of E shoud be added?)\<close>
        \<comment> \<open>let gj_check =
            (\<lambda> (s, t). gcr_closure_ops.check_ground_join_rel (redord.less kbo) (redord.min_const kbo) kbo_ext E R s t);\<close>
        check_allm (\<lambda> (s, t). moc_ops.check_instance_joinable (redord.less kbo) (redord.min_const kbo) E R s t) E\<^sub>0
          <+? (\<lambda>m. showsl_lit (STR '' E_0 is not subsumed by E and R\<newline>''));
        let nf = moc_ops.compute_mordstep_NF (redord.less kbo) (redord.min_const kbo) (Rules E R); 
        (case (nf s, nf t) of
          (Some s', Some t') \<Rightarrow> (              
            if s' \<noteq> t' then Inr ()
            else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' have same normal form '') \<circ> showsl s'))
        | _ \<Rightarrow> error (showsl_lit (STR ''error when computing normal forms of '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t)
      )}
      | _ \<Rightarrow> error (showsl_lit (STR ''unsupported reduction order'')))"

(* an adapted version of check_equational_disproof_for_infeasibility *)
lemma check_equational_disproof_by_ground_complete_system':
  assumes ok: "isOK (check_equational_disproof_by_ground_complete_system i (s,t) E\<^sub>0 E R (KBO_Input precw_w0))"
  defines "F \<equiv> set (precw_w0_sig precw_w0) :: ('f :: {compare_order,showl} \<times> nat) set"
      and "gt \<equiv> redord.less (create_KBO_redord precw_w0 (precw_w0_sig precw_w0) :: ('f, string) redord)"
  defines "gt_ordstep \<equiv> ordstep {(s,t). gt s t} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
  shows "(fground F s \<and> fground F t \<and> funas_trs (set E\<^sub>0) \<subseteq> F) \<and>
         reduction_order gt \<and>
         CR (FGROUND F gt_ordstep) \<and>
         (FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>* \<and>
         (\<exists>s' t'. (s, s') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> (t, t') \<in> (FGROUND F gt_ordstep)\<^sup>! \<and> s' \<noteq> t')"
         (is "?sig \<and> ?ro \<and> ?CR \<and> ?FGROUND_subset \<and> ?NFs")
proof -
  let ?pwfuns = "prec_weight_repr_to_prec_weight_funs precw_w0"
  let ?F = "precw_w0_sig precw_w0"
  define ro where "ro \<equiv> create_KBO_redord precw_w0 ?F :: ('f, string) redord"
  define rc where "rc \<equiv> create_KBO_redord_closure precw_w0 ?F"
  let ?join_check =
    "(\<lambda> (s, t). moc_ops.check_instance_joinable (redord.less ro) (redord.min_const ro) E R s t)"
  note ok = ok[unfolded check_equational_disproof_by_ground_complete_system_def Let_def, simplified] 
  from ok have
    ground_complete_ok:
      "isOK(check_ground_completeness i E R (precw_w0_sig precw_w0) (KBO_Input precw_w0))"  and 
    sig_st: "ground s" "ground t" "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" and
    sig_E\<^sub>0:"funas_trs (set E\<^sub>0) \<subseteq> F" and sig_ER:"funas_trs (set E \<union> set R) \<subseteq> F" and
    E\<^sub>0_subsumption_ok: "isOK (check_allm ?join_check E\<^sub>0)"
    unfolding F_def funas_rule_def ro_def rc_def by auto
  hence fg:"fground F s" "fground F t" unfolding fground_def by auto
  obtain precw w0 where pw0: "precw_w0 = (precw, w0)" by (cases precw_w0, auto)
  define c where "c \<equiv> redord.min_const ro"
  let ?gt_set = "{(s,t). gt s t}"
  let ?ext_less = "redord_closure.ext_less rc"

  obtain p w lcs scf where pwfuns:"?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  let ?pw = "prec_weight_repr_to_prec_weight precw_w0"
  from ground_complete_ok
  have valid: "isOK (redord.valid ro)"
    unfolding check_ground_completeness_def ro_def
    unfolding check_FGCR_gj_def F_def[symmetric] by simp
  then obtain p w lcs scf where pwfuns: "?pwfuns = (p, w, w0, lcs, scf)"
    unfolding pw0 prec_weight_repr_to_prec_weight_funs_def Let_def split by (cases ?pwfuns, simp)
  obtain ch where pw: "?pw = (ch, p, w, w0, lcs, scf_repr_to_scf scf)"
    unfolding prec_weight_repr_to_prec_weight_def Let_def pwfuns unfolding pw0 split by (cases ?pw, simp)
  from valid[unfolded ro_def create_KBO_redord_def] have ch_ok:"isOK(ch)" unfolding pw by auto
  let ?scf = "scf_repr_to_scf scf"
  let ?gt = "\<lambda>s t :: ('f, string) term. fst (kbo.kbo w w0 ?scf (\<lambda>f. f \<in> set lcs) (\<lambda>f g. fst (p f g)) (\<lambda>f g. snd (p f g)) s t)"
  have gt: "gt = ?gt" unfolding pw create_KBO_redord_def Let_def gt_def using pwfuns by auto
  from ground_complete_ok have R_less:"set R \<subseteq> ?gt_set"
    unfolding check_ground_completeness_def subset_iff gt_def list_all_iff by auto 

  from check_ordered_compelteness[OF ground_complete_ok, unfolded ground_complete_rewrite_system_def]
  have  CR:"CR (FGROUND F gt_ordstep)" unfolding gt_ordstep_def gt_def
    by (simp add: F_def sup_commute)

  interpret kbo:admissible_kbo w w0 "\<lambda>f g. fst (p f g)" "\<lambda>f g. snd (p f g)" "\<lambda>c. c \<in> (set lcs)" ?scf
    using prec_weight_repr_to_prec_weight[of precw_w0 p w w0 lcs] ch_ok
    unfolding isOK_def pw by (cases ch, auto)

  from KBO_redord.valid [OF valid[unfolded ro_def]] gt
  obtain gt' :: "('f, string) term  \<Rightarrow> ('f, string) term \<Rightarrow> bool" where
    least_F:"(c,0) \<in> F" and
    rord:"reduction_order gt" and
    ftotal:"\<forall>s t. fground F s \<and> fground F t \<longrightarrow> s = t \<or> gt s t \<or> gt t s" and
    gtotal_ro:"gtotal_reduction_order gt'" and
    ext:"\<forall>s t. gt s t \<longrightarrow> gt' s t" and
    min':"\<forall>t. ground t \<longrightarrow> gt'\<^sup>=\<^sup>= t (Fun c [])"
    unfolding gt_def c_def[symmetric] F_def[symmetric] ro_def[symmetric] rc_def[symmetric] by auto
  from gtotal_reduction_order.axioms gtotal_ro have rordx:"reduction_order gt'"
    using fgtotal_reduction_order.axioms by auto
  from valid have c:"c \<in> set lcs" unfolding c_def create_KBO_redord_def pw Let_def ro_def by fastforce
  from ftotal[rule_format, of "Fun c []"] kbo.not_S_least[OF c] least_F have
    "\<forall>t:: ('f, string) term. (fground F t \<longrightarrow> t = Fun c [] \<or> ?gt t (Fun c []))"
    unfolding fground_def gt by (simp, blast)
  then interpret moc:moc_spec ?gt c F unfolding c_def by (unfold_locales, simp)

  interpret moc_ro: moc_spec "redord.less ro" "redord.min_const ro"
    apply (unfold_locales) unfolding ro_def
    using c_def gt gt_def moc.least ro_def by auto
  from E\<^sub>0_subsumption_ok moc_ro.check_instance_joinable'[of E R]
  have "(s, t) \<in> set E\<^sub>0 \<Longrightarrow> (s, t) \<in> (rstep (set (E @ R)))\<^sup>\<leftrightarrow>\<^sup>*" for s t
    by (smt (verit, best) isOK_check_allm old.prod.case)
  then have
     "set E\<^sub>0 \<subseteq> (rstep (set E \<union> set R))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then have
    subst: "(rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (set E \<union> set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis (no_types, lifting) UnCI rstep_simulate_conv sup.absorb_iff1 conversion_conversion_idemp conversion_mono)

  have FG:?FGROUND_subset proof
    fix u v :: "('f, string) term"
    assume *:"(u, v) \<in> (FGROUND F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>*" 
    have FG_sym:"\<And>R. (FGROUND F R)\<^sup>\<leftrightarrow> = FGROUND F (R\<^sup>\<leftrightarrow>)" unfolding FGROUND_def by auto
    show "(u, v) \<in> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" proof(cases "u = v", simp)
      case False
      with * have fgu:"fground F u" unfolding FG_sym conversion_def unfolding FGROUND_def
        by (metis IntE converse_rtranclE mem_Collect_eq mem_Sigma_iff)
      from rtrancl_FGROUND_fground[of u v, OF *[unfolded conversion_def FG_sym]] fgu
      have fg:"fground F u" "fground F v" and conv:"(u, v) \<in> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding conversion_def by auto
      from conv[unfolded ] subst fg have conv: "(u,v) \<in> (rstep (set E \<union> set R))\<^sup>\<leftrightarrow>\<^sup>*" unfolding FGROUND_def by blast
      from fgterm_conv_FGROUND_conv[OF sig_ER fg conv] have conv:"(u, v) \<in> (FGROUND F (rstep (set E \<union> set R)))\<^sup>\<leftrightarrow>\<^sup>*" by auto
      from reduction_order.FGROUND_conversion_ordsteps[OF rord ftotal[rule_format] R_less, of F] conv
      show "(u, v) \<in> (FGROUND F gt_ordstep)\<^sup>\<leftrightarrow>\<^sup>*" unfolding gt_ordstep_def by auto
    qed
  qed

  have NFs:?NFs proof -
    let ?mordstep_nf = "moc_ops.compute_mordstep_NF gt c (Rules E R)"
    note ok = ok[folded ro_def rc_def c_def]
    from ok c_def obtain s' where s': "?mordstep_nf s = Some s'"
      by (cases "?mordstep_nf s", simp add:gt_def ro_def, blast)
    with ok c_def obtain t' where t': "?mordstep_nf t = Some t'"
      by (cases "?mordstep_nf t", simp add:gt_def ro_def, blast)
    from conjunct2[OF ok, unfolded ro_def gt_def[symmetric] s' t'] have neq: "s' \<noteq> t'" by auto
    from s' t' have s'':"moc.compute_mordstep_NF (Rules E R) s = Some s'" and
      t'':"moc.compute_mordstep_NF (Rules E R) t = Some t'" using moc.moc_spec_axioms
      unfolding gt by auto
    have sig_Rules:"funas_trs(set (Rules E R)) \<subseteq> F" using sig_ER by auto
    have "moc.all_less \<subseteq> {(s,t). gt' s t}" using ext gt by auto

    note NF_complete = moc.compute_mordstep_NF_complete[OF _ this, folded gt, OF _ rord rordx]
    note NF_complete = NF_complete[unfolded gt, OF _ ftotal[unfolded gt] min'[unfolded gt] least_F sig_Rules]
    { fix w w' :: "('f,string) term"
      assume fg:"fground F w" and seq:"moc.compute_mordstep_NF (Rules E R) w = Some w'"
      from sig_ER have sig':"funas_trs (set (Rules E R)) \<subseteq> F" by auto
      note mordsteps_FGROUND = mordsteps_FGROUND[OF least_F this]
      note * = rtrancl_mono[OF FGROUND_mono[OF mordstep_ordstep], of F c moc.all_less]
      from moc.compute_mordstep_NF_sound'[OF seq] mordsteps_FGROUND[OF fg] *
      have uu':"(w, w') \<in> (FGROUND F gt_ordstep)\<^sup>*"
        unfolding gt_ordstep_def gt set_Rules using Un_commute[of "set R"] by auto
      with rtrancl_FGROUND_fground[OF _fg] have fg':"fground F w'" by blast
      with NF_complete[OF seq fg'] have nf:"w' \<in> NF (GROUND gt_ordstep)" unfolding gt_ordstep_def
        unfolding gt using Un_commute[of "set R"] by simp
      from FGROUND_GROUND have "\<And>R. FGROUND F R \<subseteq> GROUND R" by auto
      from NF_anti_mono[OF this] nf uu' fg' have "(w, w') \<in> (FGROUND F gt_ordstep)\<^sup>!" "fground F w'"
        unfolding normalizability_def by auto
    } note nfs = this[OF fg(1) s''] this[OF fg(2) t'']
    show ?NFs by (rule exI[of _ s'], rule exI[of _ t'], insert nfs neq, auto)
  qed

  from sig_E\<^sub>0 sig_st CR rord FG NFs show ?thesis unfolding fground_def by auto
qed

lemma check_equational_disproof_by_ground_complete_system:
  assumes ok: "isOK (check_equational_disproof_by_ground_complete_system i eq E\<^sub>0 E R ro)"
  shows "eq \<notin> (rstep (set E\<^sub>0))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  note ok = ok[unfolded check_equational_disproof_by_ground_complete_system_def] 
  from ok obtain s t where eq:"eq = (s,t)" by (cases eq, auto)
  from ok obtain precw_w0 where ro:"ro = KBO_Input precw_w0" by (cases ro, auto)

  let ?F = "set (precw_w0_sig precw_w0)"
  let ?less = "redord.less (create_KBO_redord precw_w0 (precw_w0_sig precw_w0)) :: ('a, string) term \<Rightarrow> _ \<Rightarrow> bool"
  let ?ordstep = "ordstep {(s, t). ?less s t} ((set E)\<^sup>\<leftrightarrow> \<union> set R)"
  note check = check_equational_disproof_by_ground_complete_system'[OF assms[unfolded eq ro]]
  from check ok obtain s' t' where
    fground: "fground ?F s" "fground ?F t" and sig_E0:"funas_trs (set E\<^sub>0) \<subseteq> ?F" and
    rord:"reduction_order ?less" and
    CR:"CR (FGROUND ?F ?ordstep)" and
    conv_eq:"(FGROUND ?F (rstep (set E\<^sub>0)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND ?F ?ordstep)\<^sup>\<leftrightarrow>\<^sup>*" and
    s':"(s, s') \<in> (FGROUND ?F ?ordstep)\<^sup>!" and t':"(t, t') \<in> (FGROUND ?F ?ordstep)\<^sup>!" and neq:"s' \<noteq> t'"
    by auto
  with equational_disproof_by_ground_completeness eq show ?thesis by blast
qed

end
