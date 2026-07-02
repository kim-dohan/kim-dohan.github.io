(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_NJ_Unif_Impl
imports 
  Usable_Rules_NJ_Unif
  TRS.Tcap_Impl
  Show.Shows_Literal
begin

definition check_contains where "check_contains U V = 
      check_allm (\<lambda> lr. check (lr \<in> rstep U) (showsl (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl (STR '' is not contained''))) V"

lemma contains_code[code]: "contains U V = (\<forall> lr \<in> V. lr \<in> rstep U)" 
  unfolding contains_def by auto

lemma check_contains[simp]: "isOK(check_contains U V) = contains U (set V)" 
  unfolding contains_code check_contains_def by auto

definition check_contains_U0 where
  "check_contains_U0 R U s \<equiv>  
    check_allm (\<lambda> fts. case fts of 
       Var _ \<Rightarrow> succeed
     | Fun f ts \<Rightarrow> let tcapb = tcap_below U f ts
         in check_allm (\<lambda> lr. 
            case gc_matcher tcapb (fst lr) of
              None \<Rightarrow> succeed
            | Some \<sigma> \<Rightarrow> let irule = (fst lr \<cdot> \<sigma>, snd lr \<cdot> \<sigma>)
                in check (irule \<in> rstep U) (
                showsl (STR ''When considering the subterm '') \<circ> showsl fts  
                \<circ> showsl (STR ''\<newline>and the rule '') \<circ> showsl_rule lr  
                \<circ> showsl (STR ''\<newline>the capped subterm is '') \<circ> showsl tcapb 
                \<circ> showsl (STR ''\<newline>leading to the mgu with the lhs: '') \<circ> showsl_list (map (\<lambda> x. (x, \<sigma> x)) (vars_term_list (fst lr)))
                \<circ> showsl (STR ''\<newline>The instantiated rule '') \<circ> showsl_rule irule
                \<circ> showsl (STR ''\<newline>cannot be simulated by the given set of usable rules'')
                )) R) (supteq_list s)"

lemma check_contains_U0[simp]: "isOK(check_contains_U0 R U s) = contains U (U0 (set R) U s)" (is "?l = ?r")
proof -
  note cd = contains_def
  note ccd = check_contains_U0_def
  note simps = isOK_check_allm isOK_check
  let ?p = "\<lambda> f ts. (\<forall>lr\<in> set R. case gc_matcher (tcap_below U f ts) (fst lr) of None \<Rightarrow> True | Some \<sigma> \<Rightarrow> (fst lr \<cdot> \<sigma>, snd lr \<cdot> \<sigma>) \<in> rstep U)"
  {
    assume "\<not> ?l"
    from this[unfolded ccd Let_def, simplified, unfolded simps]
    obtain f ts where s: "s \<unrhd> Fun f ts" and not: "\<not> ?p f ts"
      by (force split: term.splits option.splits)
    from not obtain l r \<sigma> where lr: "(l,r) \<in> set R" and mgu: "gc_matcher (tcap_below U f ts) l = Some \<sigma>" and
      not: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<notin> rstep U" by (auto split: option.splits)
    from match_non_var[OF lr s mgu] not have "\<not> ?r" unfolding cd by auto
  }
  moreover
  {
    assume ?l
    have ?r unfolding cd
    proof
      fix ls rs
      assume "(ls,rs) \<in> U0 (set R) U s"
      then show "(ls,rs) \<in> rstep U"
      proof (cases)
        case (match_non_var l r f ts \<sigma>)
        from match_non_var(4) \<open>?l\<close>[unfolded ccd Let_def, simplified, unfolded simps]
          have "?p f ts" by (auto split: option.splits term.splits)
        with match_non_var show ?thesis by auto
      qed
    qed
  }
  ultimately show ?thesis by auto
qed 

definition check_usable_instantiation where 
  "check_usable_instantiation R U s \<equiv> do {
     let UU = set U;
     check_contains_U0 R UU s
       <+? (\<lambda> s. showsl (STR ''U <= U0(R,s) required\<newline>'') \<circ> s);
     check_allm (\<lambda> r. check_contains_U0 R UU r 
       <+? (\<lambda> s. showsl (STR ''U <= U0(R,r) for rhs r = '') \<circ> showsl r \<circ> showsl (STR '' required\<newline>'') \<circ> s))
       (map snd U)
  }"

lemma check_usable_instantiation[simp]: 
  "isOK(check_usable_instantiation R U s) = usable_instantiation (set R) (set U) s"
  unfolding check_usable_instantiation_def usable_instantiation_def Let_def
  by simp

definition check_usable_rules_unif where "
  check_usable_rules_unif R U s \<equiv> do {
    check (ground s \<or> (\<forall> l \<in> set (map fst R). is_Fun l)) (showsl (STR ''since '') \<circ> showsl s 
      \<circ> showsl (STR '' is not ground, left-hand sides of R must not be variables''));
    check_varcond_subset U;
    check_usable_instantiation R U s <+? (\<lambda> s. showsl (STR ''closure properties of usable rules not satisfied\<newline>'') \<circ> s)
  } <+? (\<lambda> e. showsl (STR ''problem in checking validity of usable rules U =\<newline>'') \<circ> showsl_trs U \<circ> 
     showsl (STR ''\<newline>for term '') \<circ> showsl s \<circ>
     showsl (STR ''\<newline>wrt TRS R =\<newline>'') \<circ> showsl_trs R \<circ> showsl_nl \<circ> e)"

lemma check_usable_rules_unif_left: assumes ok: "isOK(check_usable_rules_unif Rs U s)"
  and nj: "\<not> (\<exists> u. (s,u) \<in> (rstep (set U))^* \<and> (t,u) \<in> (rstep Rt)^*)"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep Rt)^*)" (is "\<not> ?join")
proof
  assume ?join
  then obtain u where su: "(s,u) \<in> (rstep (set Rs))^*" and tu: "(t,u) \<in> (rstep Rt)^*" by auto
  have "(s,u) \<in> (rstep (set U))^*"
    by (rule usable_instantiation_rsteps_main[OF _ _ su, of "set U", THEN conjunct1],
    insert ok[unfolded check_usable_rules_unif_def], auto simp: no_lhs_var_def)
  with tu nj show False by auto
qed

lemma check_usable_rules_unif_right: assumes ok: "isOK(check_usable_rules_unif Rt U t)"
  and nj: "\<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep (set U))^*)"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
  using check_usable_rules_unif_left[OF ok, of s Rs] nj by blast

end
