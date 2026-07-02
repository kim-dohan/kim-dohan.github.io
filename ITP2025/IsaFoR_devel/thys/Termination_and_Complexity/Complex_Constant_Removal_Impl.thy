(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Complex_Constant_Removal_Impl
imports
  Complex_Constant_Removal
  Framework.QDP_Framework_Impl
  CR.Critical_Pairs_Impl
begin

definition extract_fresh_var :: "(('f,'v)rule \<times> ('f,'v)rule)list \<Rightarrow> 'v result" where
  "extract_fresh_var sts \<equiv> case (case sts of [] \<Rightarrow> None 
    | (_,(s,_)) # _ \<Rightarrow> (case s of Var _ \<Rightarrow> None
      | Fun _ ss \<Rightarrow> if ss = [] then None else (case (last ss) of
         Var x \<Rightarrow> Some x | _ \<Rightarrow> None))) of
   None \<Rightarrow> error (showsl_lit (STR ''could not extract fresh variable (as last argument from some lhs of new pairs)''))
  | Some x \<Rightarrow> return x"

definition extract_ren :: "(('f,'v)rule \<times> ('f,'v)rule)list \<Rightarrow> 
  ('f \<times> nat \<Rightarrow> 'f) result" where
  "extract_ren ps_ps' \<equiv> do {
     check (\<forall> st_st' \<in> set ps_ps'. (\<lambda> ((s,t),(s',t')). is_Fun s \<and> is_Fun t \<and> is_Fun s' \<and> is_Fun t') st_st')
       (showsl_lit (STR ''all lhss and rhss of pairs must be non-variables''));
     let rt = (\<lambda> t. the (root t));
     let pair = (\<lambda> s s'. (rt s, fst (rt s')));
     let pairs = (\<lambda> (st,st'). [pair (fst st) (fst st'), pair (snd st) (snd st')]);
     let ren' = map_of (remdups (concat (map pairs ps_ps')));
     let ren = (\<lambda> fn. case ren' fn of None \<Rightarrow> fst fn | Some f \<Rightarrow> f);
     return ren
   }"

definition check_drop :: "'v \<Rightarrow> ('f :: showl,'v :: showl)term \<Rightarrow> ('f \<times> nat \<Rightarrow> 'f) \<Rightarrow> ('f,'v)rule \<times> ('f,'v)rule \<Rightarrow> showsl check" where
  "check_drop x c ren st_st' \<equiv> case st_st' of ((s,t),(s',t')) \<Rightarrow> case s of Fun f ss \<Rightarrow> case t of Fun g ts \<Rightarrow> do {
     check (s' = Fun (ren (f,length ss)) (ss @ [Var x])) 
       (showsl_lit (STR ''could not relate '') \<circ> showsl s \<circ> showsl_lit (STR '' with '') \<circ> showsl s');
     let ts'' = args t';
     let ts' = take (length ts'' - 1) ts'';
     check (t' = Fun (ren (g,length ts)) (ts' @ [Var x]) \<and> ts = map (\<lambda>t. t \<cdot> subst x c) ts') 
       (showsl_lit (STR ''could not relate '') \<circ> showsl t \<circ> showsl_lit (STR '' with '') \<circ> showsl t')
  }"

lemma check_drop: assumes "isOK (check_drop x c ren ((Fun f ss, Fun g ts), (s', t')))"
  shows "\<exists>ts'. s' = Fun (ren (f, length ss)) (ss @ [Var x]) \<and> t' = Fun (ren (g, length ts)) (ts' @ [Var x]) \<and> 
    ts = map (\<lambda>t. t \<cdot> subst x c) ts'"
  using assms unfolding check_drop_def by (auto simp: Let_def)

datatype ('f,'v)complex_constant_removal_prf = Complex_Constant_Removal_Proof 
  "('f,'v)term" (* the constant *)
  "(('f,'v)rule \<times> ('f,'v)rule) list" (* a list of mappings: old pair -> new pair *)

context
  fixes rename :: "'v :: {infinite,showl} renaming2" 
begin

primrec
  complex_constant_removal_proc ::
    "('dpp, 'f :: {compare_order,showl}, 'v) dpp_ops
  \<Rightarrow> ('f,'v)complex_constant_removal_prf 
  \<Rightarrow> 'dpp \<Rightarrow> 'dpp result"
where
  "complex_constant_removal_proc I (Complex_Constant_Removal_Proof c ps) dpp =
    do {
      let p = dpp_ops.P I dpp;
      let pw = dpp_ops.Pw I dpp;
      let r = dpp_ops.Rw I dpp;
      let q = dpp_ops.Q I dpp;
      let pairs = dpp_ops.pairs I dpp;
      x \<leftarrow> extract_fresh_var ps;
      ren \<leftarrow> extract_ren ps;
      let is_def = dpp_spec.is_defined I dpp;
      let rQs = remdups (map root q);
      check_allm (\<lambda>(s, t). do { \<comment> \<open>require that pairs have standard structure\<close>
        check_no_var s;
        check_no_var t;        
        check_no_defined_root is_def t;
        check (x \<notin> set (vars_rule_list (s,t))) (showsl x \<circ> showsl_lit (STR '' is not fresh for pair '') \<circ> showsl_rule (s,t));
        let f = the (root s);
        let f' = (ren f, Suc (snd f));
        check (Some f' \<notin> set rQs) (showsl_lit (STR ''renaming delivers defined symbol of Q''));
        check (\<not> is_def f') (showsl_lit (STR ''renaming delivers defined symbol of R'')) 
      }) pairs;
      let pps = filter (\<lambda> st_st'. fst st_st' \<in> set p) ps;
      let pwps = filter (\<lambda> st_st'. fst st_st' \<in> set pw) ps;
      check_allm (\<lambda> st. check (st \<in> set (map fst pps)) (showsl_lit (STR ''could not find entry for pair '') \<circ> showsl_rule st)) p;
      check_allm (\<lambda> st. check (st \<in> set (map fst pwps)) (showsl_lit (STR ''could not find entry for pair '') \<circ> showsl_rule st)) pw;
      check (ground c) (showsl_lit (STR ''the term '') \<circ> showsl c \<circ> showsl_lit (STR '' is not ground''));
      check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost required''));
      check (dpp_ops.R I dpp = []) (showsl_lit (STR ''strict rules not allowed''));
      check (dpp_ops.rules_no_left_var I dpp) (showsl_lit (STR ''rules may not have variables as lhss''));
      (if is_NF_trs r c then succeed else check_critical_pairs_innermost rename r 
         <+? (\<lambda> s. showsl_lit (STR ''could not ensure confluence\<newline>'') \<circ> s));
      check_allm (\<lambda> st_st'. check_drop x c ren st_st' <+? (\<lambda> s. showsl_lit (STR ''problem in finding correspondence between rule '') 
          \<circ> showsl_rule (fst st_st') \<circ> showsl_lit (STR '' and rule '') \<circ> showsl_rule (snd st_st') \<circ> showsl_nl \<circ> s)) ps;
      return (dpp_ops.mk I (dpp_ops.nfs I dpp) (dpp_ops.minimal I dpp) (map snd pps) (map snd pwps) q [] r)
    } <+? (\<lambda> s. showsl_lit (STR ''problem in complex constant removal proc:\<newline>'') \<circ> s)" 

lemma complex_constant_removal_proc: assumes "dpp_spec I"
  shows "dpp_spec.sound_proc_impl I (complex_constant_removal_proc I prf)"
proof -
  interpret dpp_spec I by fact
  note Let_def[simp]
  show ?thesis
  proof
    fix d d'
    assume res: "complex_constant_removal_proc I prf d = return d'" and fin: "finite_dpp (dpp d')"
    obtain c ps where "prf = Complex_Constant_Removal_Proof c ps" by (cases "prf", auto)
    note res = res[unfolded this, simplified]
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?Q = "set (Q d)"
    let ?R = "set (Rw d)"    
    from res obtain x where x: "extract_fresh_var ps = return x"
      by (cases "extract_fresh_var ps", auto)
    note res = res[unfolded x, simplified]
    from res obtain ren where ren: "extract_ren ps = return ren"
      by (cases "extract_ren ps", auto)
    note res = res[unfolded ren, simplified]
    from res have [simp]: "R d = []" by auto
    note res = res[unfolded this, simplified]
    from res have d: "dpp d = (?nfs,?m,?P,?Pw,?Q,{},?R)" unfolding dpp_sound by auto
    let ?pss = "{ st_st'. st_st' \<in> set ps \<and> fst st_st' \<in> ?P}"
    let ?psw = "{ st_st'. st_st' \<in> set ps \<and> fst st_st' \<in> ?Pw}"
    from res have "d' = mk ?nfs ?m (map snd [st_st'\<leftarrow>ps . fst st_st' \<in> set (P d)]) 
      (map snd [st_st'\<leftarrow>ps . fst st_st' \<in> set (Pw d)]) (Q d) [] (Rw d)" by simp
    then have d': "dpp d' = (?nfs,?m,snd ` ?pss, snd ` ?psw, ?Q, {}, ?R)" by simp
    from res have c: "ground c" by auto
    from res have inn: "NF_terms ?Q \<subseteq> NF_trs ?R" by auto
    from res have is_FunR: "\<And> l r. (l,r) \<in> ?R \<Longrightarrow> is_Fun l" by auto
    then have is_FunR': "\<forall>(l,r) \<in> ?R. is_Fun l" by auto
    from res have "c \<in> NF_trs ?R \<or> isOK(check_critical_pairs_innermost rename (Rw d))" by auto
    with check_critical_pairs_innermost[OF _ inn is_FunR, of rename _ ?nfs]
    have CR: "c \<in> NF_trs ?R \<or> CR (qrstep ?nfs ?Q ?R)" by force
    from res have drop: "\<And> st_st'. st_st' \<in> set ps \<Longrightarrow> isOK(check_drop x c ren st_st')" by auto
    define rel where "rel = (\<lambda> P P'. \<forall> st \<in> P. \<exists> st' \<in> P'. (st,st') \<in> set ps)"
    show "finite_dpp (dpp d)" unfolding d
    proof (rule complex_constant_removal[OF fin[unfolded d'] CR inn c _ _ _ _ _ is_FunR'])
      fix s t
      assume st: "(s,t) \<in> ?P \<union> ?Pw"
      show "x \<notin> vars_rule (s,t)" using st res by auto
      show "is_Fun s \<and> is_Fun t \<and>  \<not> defined ?R (the (root t))" using st res by auto
    next
      fix f ss t
      assume mem: "(Fun f ss, t) \<in> ?P \<union> ?Pw"
      let ?s = "Fun f ss"
      from mem res[THEN conjunct1] have ndef: "Some (ren (the (root ?s)), Suc (snd (the (root ?s)))) \<notin> root ` ?Q \<and>
        \<not> defined ?R (ren (the (root ?s)), Suc (snd (the (root ?s))))" by blast
      show "Some (ren (f, length ss), Suc (length ss)) \<notin> root ` ?Q" using ndef by simp
      show "\<not> defined ?R (ren (f, length ss), Suc (length ss))" using ndef by simp
    next
      from res have "(\<forall>x\<in> ?P. x \<in> fst ` {x \<in> set ps. fst x \<in> ?P})" by auto
      then show "rel ?P (snd ` ?pss)" unfolding rel_def by force
      from res have "(\<forall>x\<in> ?Pw. x \<in> fst ` {x \<in> set ps. fst x \<in> ?Pw})" by auto
      then show "rel ?Pw (snd ` ?psw)" unfolding rel_def by force
    next
      fix P P' f ss g ts
      assume rel: "rel P P'" and mem: "(Fun f ss, Fun g ts) \<in> P"
      from rel[unfolded rel_def, rule_format, OF mem] obtain st' where
        st': "st' \<in> P'" and mem: "((Fun f ss, Fun g ts), st') \<in> set ps" ..
      obtain s' t' where id: "st' = (s',t')" by force
      note st' = st'[unfolded id]
      from drop[OF mem[unfolded id]] have cdrop: "isOK (check_drop x c ren ((Fun f ss, Fun g ts), s', t'))" .
      from check_drop[OF cdrop] st'
      show "\<exists>ts'. (Fun (ren (f, length ss)) (ss @ [Var x]), Fun (ren (g, length ts)) (ts' @ [Var x])) \<in> P' 
        \<and> ts = map (\<lambda>t. t \<cdot> subst x c) ts'" by auto
    qed
  qed
qed

end
end
