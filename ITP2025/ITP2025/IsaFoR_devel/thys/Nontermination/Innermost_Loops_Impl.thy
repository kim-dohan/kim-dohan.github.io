(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Loops_Impl
  imports
    Innermost_Loops
    TRS.Q_Restricted_Rewriting_Impl
    "Transitive-Closure.Transitive_Closure_List_Impl"
    Auxx.Inductive_Set_Impl
begin

context fixed_subst_incr
begin
lemma ident_solve'_code: "ident_solve' cps st = (let cp = conflicts st in
    if (\<exists> (u,v,n) \<in> set cp. is_Fun u) then None
    else if (\<exists>(u,v,n) \<in> set cp. (u,v) \<in> (\<lambda> (u,v,m). (u,v)) ` cps) then None
    else do {
      is \<leftarrow> mapM (\<lambda>(u, v, m). ident_solve' (insert (u, v, m) cps) (u \<cdot> \<mu>, v, Suc m)) (conflicts st);
      Some (max_list (map Suc is))
    })" 
  unfolding ident_solve'.simps[of cps st] Let_def
  by (rule if_cong, force, force, rule if_cong, force, force, force)
end

declare fixed_subst.conflicts.simps[code]
declare fixed_subst_incr.ident_solve'_code[code]
declare fixed_subst_incr.ident_solve_def[code]

definition ident_decision :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)ident_prob \<Rightarrow> bool" where
  "ident_decision \<sigma> ip \<equiv> fixed_subst_incr.ident_solve \<sigma> ip \<noteq> None"

lemma ident_decision[simp]: "ident_decision \<mu> ip = (\<exists> i. fixed_subst.ident_solution (si_subst \<mu>) ip i)"
proof -
  interpret fixed_subst_incr \<mu> .
  show ?thesis unfolding ident_decision_def using ident_solve[of ip] by auto
qed

definition gmatch_decision :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)gmatch_prob \<Rightarrow> bool" where
  "gmatch_decision \<sigma> mp \<equiv> do {
    (smp,i) \<leftarrow> fixed_subst_incr.simplify_mp \<sigma> mp [];
    guard (Ball (set (ident_prob_of_smp smp)) (ident_decision \<sigma>))
  } \<noteq> None"

lemma gmatch_decision[simp]: "gmatch_decision \<mu> mp = (\<exists> sol. fixed_subst.gmatch_solution (si_subst \<mu>) mp sol)" (is "?l = ?r")
proof -
  interpret fixed_subst_incr \<mu> .
  note simp = gmatch_decision_def[of \<mu> mp]
  show ?thesis
  proof (cases "simplify_mp mp []")
    case None
    with simplify_mp_complete[of mp] show ?thesis unfolding simp by auto
  next
    case (Some sol)
    then obtain smp i where sol: "sol = (smp, i)" by force
    note Some = Some[unfolded sol]
    note simp = simp[unfolded Some]
    note simp_sound = simplify_mp_sound[OF Some]
    from simplify_mp_solved_form[OF Some] have solved: "gmatch_solved_form smp"
      unfolding gmatch_solved_form_def by auto
    let ?ips = "ident_prob_of_smp smp"
    show ?thesis
    proof (cases "Ball (set ?ips) (ident_decision \<mu>)")
      case True
      with simp have l: "?l = True" by simp
      {
        fix ip
        assume "ip \<in> set ?ips"
        with True have "ident_decision \<mu> ip" by auto
        then have "\<exists> i. ident_solution ip i" by simp
      }
      then have "\<forall> ip. \<exists> i. ip \<in> set ?ips \<longrightarrow> ident_solution ip i" by auto
      from choice[OF this] obtain "is" where sol: "\<And> ip. ip \<in> set ?ips \<Longrightarrow> ident_solution ip (is ip)" by blast
      define i where "i = max_list (map is ?ips)"
      have "\<exists>\<sigma>. gmatch_solution smp (i, \<sigma>)"
        by (rule ident_prob_of_smp_sound[OF solved], rule exI, rule conjI[OF _ sol], unfold i_def, rule max_list, auto)
      then obtain \<sigma> where "gmatch_solution smp (i, \<sigma>)" ..
      from simp_sound[OF this] l show ?thesis by auto
    next
      case False
      with simp have l: "?l = False" by simp
      from False obtain ip where ip: "ip \<in> set ?ips" and False: "\<not> ident_decision \<mu> ip" by auto
      {
        fix n \<sigma>
        assume "gmatch_solution mp (n,\<sigma>)"
        from simplify_mp_complete[OF this] Some obtain k where "gmatch_solution smp (k, \<sigma>)" by auto
        from ident_prob_of_smp_complete[OF this, of "fst ip" "snd ip"] ip False
        have False by auto
      }
      with l show ?thesis by auto
    qed
  qed
qed

definition match_decision :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)match_prob \<Rightarrow> bool" where
  "match_decision \<mu> mp \<equiv> gmatch_decision \<mu> [mp]"

lemma match_decision[simp]: "match_decision \<mu> mp = (\<exists> sol. fixed_subst.match_solution (si_subst \<mu>) mp sol)"
proof -
  interpret fixed_subst_incr \<mu> .
  show ?thesis unfolding match_decision_def gmatch_decision 
    using gmatch_solution_def by auto
qed

lemma v_incr_the_set: "v_incr \<mu> = {x. \<exists> y. is_Fun (\<mu> y) \<and> generic_inductive_set.the_set 
  {x. \<mu> x \<noteq> Var x}
  (=)
  (\<lambda> x. {y. \<mu> y = Var x \<and> x \<noteq> y}) y x}
  " (is "?l = {x. \<exists> y. _ \<and> generic_inductive_set.the_set ?R ?P ?Q y x}")
proof -
  interpret generic_inductive_set ?R ?P ?Q .
  {
    fix x
    assume "x \<in> {x. \<exists> y. is_Fun (\<mu> y) \<and> the_set y x}"
    then obtain y where y: "is_Fun (\<mu> y)" and "the_set y x" by auto
    from is_Fun[of \<mu>, OF y] have "y \<in> v_incr \<mu>" .
    with \<open>the_set y x\<close>
    have "x \<in> ?l"
    proof (induct rule: the_set_induct)
      case (rec x y z u)
      then have "\<mu> z = Var y" and "y \<in> v_incr \<mu>" by auto
      from rec(5)[OF later[OF this]]
      show ?case .
    qed simp
  }
  moreover
  {
    fix x
    assume "x \<in> ?l"
    then have "\<exists> y. is_Fun (\<mu> y) \<and> the_set y x"
    proof (induct rule: v_incr.induct)
      case (is_Fun x)
      then show ?case
        by (intro exI[of _ x] conjI non_rec, auto)
    next
      case (later z x)
      from later(3) obtain y where y: "is_Fun (\<mu> y)" and set: "the_set y x" by blast
      show ?case
      proof (cases "x = z")
        case True
        with later(3) show ?thesis by blast
      next
        case False
        show ?thesis
          by (intro exI[of _ y] conjI[OF y]
            rec_rec[OF set _ non_rec[OF _ refl]], insert False later(1), auto)
      qed
    qed
  }
  ultimately show ?thesis by blast
qed      
  

context fixed_subst
begin

lemma W_via_rtrancl: 
  "W t = {(x, y). x \<noteq> y \<and> y \<in> vars_term (\<mu> x)}^* `` vars_term t"
proof -
  obtain V where V: "V = vars_term t" by auto
  let ?M = "\<lambda> i V. \<Union>(vars_term ` (\<mu> ^^ i) ` V)"
  let ?R = "{(x,y) | x y. y \<in> vars_term (\<mu> x)}"
  have "?R^* `` V = (\<Union>n. (?R ^^ n) `` V)"
    unfolding rtrancl_is_UN_relpow by auto
  also have "... = (\<Union> n. ?M n V)"
  proof -
    {
      fix n 
      have "?M n V = (?R ^^ n) `` V"
      proof (induct n)
        case 0
        show ?case by auto
      next
        case (Suc n)
        have "(?R ^^ Suc n) `` V = (?R ^^ n O ?R) `` V" by auto
        also have "... = ?R `` ((?R ^^ n) `` V)" by auto
        also have "... = ?R `` ?M n V" unfolding Suc ..
        also have "... = ?M (Suc n) V" 
        proof -
          have "?M (Suc n) V = vars_term (t \<cdot> \<mu> ^^ Suc n)" 
            unfolding V vars_term_subst ..
          also have "... = vars_term (t \<cdot> \<mu> ^^ n \<cdot> \<mu>)" 
            unfolding subst_power_Suc by auto
          also have "... = ?R `` ?M n V" 
            unfolding V vars_term_subst by auto
          finally show ?thesis by simp
        qed
        finally show ?case by simp
      qed
    } note main = this
    show ?thesis unfolding main ..
  qed
  also have "... = W t" unfolding vars_iteration_def vars_term_subst V by auto
  finally have main: "W t = ?R^* `` V" by simp
  show ?thesis unfolding main rtrancl_r_diff_Id[of ?R, symmetric] unfolding V[symmetric] 
    by (rule arg_cong[where f = "\<lambda> x. x^* `` V"], auto)
qed
end

definition "v_incr_impl mu \<equiv>
    inductive_set_impl (map fst mu) (=) (\<lambda> x. [ y . (y,t) <- mu, t = Var x]) [ y . (y,t) <- mu, is_Fun t]"

lemma v_incr_impl: "set (v_incr_impl (mk_subst_domain \<mu>)) = v_incr (mk_subst Var \<mu>)"
  unfolding v_incr_the_set v_incr_impl_def 
  by (rule inductive_set_impl_pred, (force simp: mk_subst_domain subst_domain_def split: if_splits)+)

definition W_impl :: "('f, 'v) substL \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v list" where
  "W_impl d \<equiv>
    let 
      filt = filter (\<lambda>(x,y). x \<noteq> y);
      xvs = concat (map (\<lambda> (x,t). (map (\<lambda> y. (x,y)) (vars_term_list t))) d);
      rel = filt xvs;
      rtran = rtrancl_list_impl rel
    in (\<lambda>t. rtran (vars_term_list t))"

lemma W_impl: "set (W_impl (mk_subst_domain \<mu>) t) = vars_iteration (mk_subst Var \<mu>) t" 
proof -  
  interpret fixed_subst "mk_subst Var \<mu>" .
  let ?I = "set [(x,y)\<leftarrow>concat (map (\<lambda>(x, t). map (Pair x) (vars_term_list t))
        (mk_subst_domain \<mu>)) . x \<noteq> y]"
  let ?S = " {(x, y) |x y. x \<noteq> y \<and> y \<in> vars_term (mk_subst Var \<mu> x)}"
  have id: "?I = ?S" 
  proof -
    have "?I \<subseteq> ?S" unfolding set_concat set_map set_filter mk_subst_domain
      by auto
    moreover {
      fix xy
      assume S: "xy \<in> ?S"
      obtain x y where xy: "xy = (x,y)" by (cases xy, auto)
      with S have neq: "x \<noteq> y" and y: "y \<in> vars_term (mk_subst Var \<mu> x)" by auto
      then have "mk_subst Var \<mu> x \<noteq> Var x" by (cases "mk_subst Var \<mu> x", auto)
      then have x: "x \<in> subst_domain (mk_subst Var \<mu>)" unfolding subst_domain_def by auto
      have "(x,y) \<in> ?I"
        unfolding set_filter set_concat set_map split mk_subst_domain
        by (rule, rule, rule, rule, rule, rule refl, rule x, simp_all add: y neq)
      then have "xy \<in> ?I" unfolding xy .
    }
    ultimately show "?I = ?S" by blast
  qed
  show ?thesis
    unfolding W_via_rtrancl
    unfolding W_impl_def Let_def
    unfolding rtrancl_list_impl
    unfolding id 
  by auto
qed


lift_definition subst_incr :: "('f,'v)substL \<Rightarrow> ('f,'v)subst_incr" 
  is "\<lambda> \<sigma>. let dom = mk_subst_domain \<sigma> in (mk_subst Var \<sigma>, set (v_incr_impl dom), W_impl dom)" 
  unfolding Let_def v_incr_impl 
  using finite_mk_subst W_impl by force

lemma si_subst_subst_incr: "si_subst (subst_incr \<sigma>) = mk_subst Var \<sigma>"
  by (transfer, simp add: Let_def)

fun match_prob_of_rp_impl :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)redex_prob \<Rightarrow> ('f,'v)match_prob list" where
  "match_prob_of_rp_impl \<mu> (t, Var x) = [(t, Var x)]"
| "match_prob_of_rp_impl \<mu> (t, l) = (
    let
      sterms = remdups (t # map (si_subst \<mu>) (si_W \<mu> t));
      uterms = concat (map (filter is_Fun \<circ> supteq_list) sterms)
    in map (\<lambda>u. (u, l)) (remdups uterms))"

lemma (in fixed_subst_incr) match_prob_of_rp_impl:
  "set (match_prob_of_rp_impl \<mu>_incr (t,l)) =
    match_prob_of_rp (t,l)"
proof (cases l)
  case (Var x)
  show ?thesis unfolding match_prob_of_rp_def Var by simp
next
  case (Fun f ls)
  show ?thesis unfolding Fun match_prob_of_rp_def match_prob_of_rp_impl.simps
    unfolding Let_def split term.simps unfolding si_W[symmetric]
    by auto 
qed

definition redex_decision where
  "redex_decision \<mu> rp \<equiv>
      (\<exists> mp \<in> set (match_prob_of_rp_impl \<mu> rp). match_decision \<mu> mp)"

lemma redex_decision: "redex_decision \<mu> rp = (\<exists> sol. fixed_subst.redex_solution (si_subst \<mu>) rp sol)" (is "?l = ?r")
proof -
  interpret fixed_subst_incr \<mu> .
  let ?\<mu> = "si_subst \<mu>"
  obtain t l where rp: "rp = (t,l)" by force
  show ?thesis
  proof
    assume ?r
    then obtain i \<sigma> C where "redex_solution (t,l) (i,\<sigma>,C)" unfolding rp by auto
    from match_prob_of_rp_complete[OF this]
    obtain \<tau> u j
      where mem: "(u,l) \<in> match_prob_of_rp (t,l)"
      and sol: "match_solution (u,l) (j,\<tau>)" by auto
    show ?l unfolding rp redex_decision_def Let_def 
      set_map match_prob_of_rp_impl
      using match_decision[of \<mu> "(u,l)"] sol mem by auto
  next
    assume ?l
    from this[unfolded rp redex_decision_def Let_def set_map match_prob_of_rp_impl]
    obtain m p where mp: "(m,p) \<in> match_prob_of_rp (t,l)"
      and sol: "match_decision \<mu> (m,p)" by auto
    from sol[unfolded match_decision] match_prob_of_rp_sound[OF _ mp] show ?r unfolding rp by force
  qed
qed


definition redex_rps_decision :: "('f, 'v) substL \<Rightarrow> ('f, 'v) redex_prob list \<Rightarrow> ('f, 'v) redex_prob check" where
  "redex_rps_decision \<mu> \<equiv> 
    let
      \<mu>' = subst_incr \<mu>;
      main = redex_decision \<mu>'
    in check_allm (\<lambda>tl. check (\<not> main tl) tl)"

lemma redex_rps_decision:
  "isOK (redex_rps_decision \<mu> rps) = (\<not>(\<exists>t l i C \<sigma>. (t, l) \<in> set rps \<and> t \<cdot> ((mk_subst Var \<mu>) ^^ i) = C\<langle>l \<cdot> \<sigma>\<rangle>))"
  (is "?l = ?r")
proof -
  interpret fixed_subst_incr "subst_incr \<mu>" .
  show ?thesis unfolding redex_rps_decision_def Let_def 
    unfolding redex_decision si_subst_subst_incr[symmetric]
    using redex_solution_def by force
qed

definition check_NF_iteration :: "('f, 'v) substL \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) redex_prob check" where
  "check_NF_iteration \<mu> \<equiv> let dec = redex_rps_decision \<mu> in (\<lambda>Q t. dec (map (Pair t) Q))"

lemma check_NF_iteration:
  "isOK (check_NF_iteration \<mu> Q t) = (\<forall>i. t \<cdot> mk_subst Var \<mu> ^^ i \<in> NF_terms (set Q))"
  (is "?l = ?r") 
proof -
  have id: "?r = (\<not>(\<exists>q \<sigma> C i. q \<in> set Q \<and> t \<cdot> mk_subst Var \<mu> ^^ i = C\<langle>q \<cdot> \<sigma>\<rangle>))" 
    unfolding NF_ctxt_subst by auto
  show ?thesis unfolding id check_NF_iteration_def redex_rps_decision Let_def by force
qed

definition check_qrstep_subst :: "(('f:: showl, 'v:: showl) term \<Rightarrow> ('f,'v)redex_prob check) \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) rules \<Rightarrow>
     pos \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
     showsl check"
where "check_qrstep_subst cni nfs \<equiv> let main = check_prop_rstep nfs (\<lambda> t. cni t <+? (\<lambda> _. showsl t \<circ> showsl_lit (STR '' mu ^^ i is not in Q-normal form for all i''))) in
   (\<lambda> R p r s t. do { 
      check (is_Fun (fst r)) (showsl_lit (STR ''loop check requires lhss to be non-variable''));
      main R p r s t
   })"

lemma check_qrstep_subst_pos:
  assumes cni: "cni = check_NF_iteration \<mu> Q"
  and ok: "isOK (check_qrstep_subst cni nfs R p r s t)"
  shows "\<exists> \<sigma> r'. (s \<cdot> mk_subst Var \<mu> ^^ i, t \<cdot> mk_subst Var \<mu> ^^ i) \<in> qrstep_r_p_s nfs (set Q) (set R) r' p \<sigma> \<and> r =\<^sub>v r'"
proof -
  from ok[unfolded check_qrstep_subst_def Let_def]
  have nvar: "is_Fun (fst r)" by auto
  from check_prop_rstep_sound[OF ok[unfolded check_qrstep_subst_def Let_def cni, simplified, THEN conjunct2], unfolded isOK_update_error check_NF_iteration]
  obtain \<sigma> r' where step: "(s,t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. \<forall> i. t \<cdot> mk_subst Var \<mu> ^^ i \<in> NF_terms (set Q)) (set R) r' p \<sigma>" 
    and r': "(fst r, snd r) =\<^sub>v (fst r', snd r')" by auto
  from eq_rule_mod_varsE[OF r'] nvar have nvar: "is_Fun (fst r')" by (cases "fst r", auto)
  from step show ?thesis unfolding prop_rstep_qrstep_subst[OF nvar] using r'[simplified] by blast
qed


lemma check_qrstep_subst:
  assumes cni: "cni = check_NF_iteration \<mu> Q"
    and ok: "isOK (check_qrstep_subst cni nfs R p r s t)"
  shows "(s \<cdot> mk_subst Var \<mu> ^^ i, t \<cdot> mk_subst Var \<mu> ^^ i) \<in> qrstep nfs (set Q) (set R)"
  using check_qrstep_subst_pos[OF cni ok] 
  unfolding qrstep_qrstep_r_p_s_conv by blast

definition check_rqrstep_subst :: "(('f:: showl, 'v:: showl) term \<Rightarrow> ('f,'v)redex_prob check) \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) rules \<Rightarrow>
     ('f, 'v) rule \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
     showsl check"
where "check_rqrstep_subst cni nfs \<equiv> \<lambda> R. check_qrstep_subst cni nfs R []"

lemma check_rqrstep_subst:
  assumes cni: "cni = check_NF_iteration \<mu> Q"
    and ok: "isOK(check_rqrstep_subst cni nfs R r s t)"
  shows "(s \<cdot> mk_subst Var \<mu> ^^ i, t \<cdot> mk_subst Var \<mu> ^^ i) \<in> rqrstep nfs (set Q) (set R)"
  using check_qrstep_subst_pos[OF cni ok[unfolded check_rqrstep_subst_def], of i] 
  unfolding qrstep_r_p_s_def rqrstep_def Let_def by auto

fun
  check_qsteps_subst ::
    "(('f:: showl, 'v:: showl) term \<Rightarrow> ('f,'v)redex_prob check) \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
     ('f, 'v) prseq \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_qsteps_subst cni nfs P R [] s u = check (s = u) (
    showsl_lit (STR ''the last term of the rewrite sequence\<newline>'') \<circ> showsl s \<circ> 
    showsl_lit (STR ''\<newline>does not correspond to the goal term\<newline>'') \<circ> showsl u \<circ> showsl_nl)"
| "check_qsteps_subst cni nfs P R ((_, r, True, t) # prts) s u = do {
    check_rqrstep_subst cni nfs P r s t;
    check_qsteps_subst cni nfs P R prts t u
  }"
| "check_qsteps_subst cni nfs P R ((p, r, False, t) # prts) s u = do {
    check_qrstep_subst cni nfs R p r s t;
    check_qsteps_subst cni nfs P R prts t u
  }"

lemma check_qsteps_subst_sound:
  assumes cni: "cni = check_NF_iteration \<mu> Q"
    and ok: "isOK (check_qsteps_subst cni nfs P R rseq s t)"
  shows "(s \<cdot> mk_subst Var \<mu> ^^ i, t \<cdot> mk_subst Var \<mu> ^^ i) \<in> (rqrstep nfs (set Q) (set P) \<union> qrstep nfs (set Q) (set R))^^(length rseq)"
proof -
  obtain PR where PR: "PR = rqrstep nfs (set Q) (set P) \<union> qrstep nfs (set Q) (set R)" by auto
  from ok show ?thesis unfolding PR[symmetric] 
  proof (induct rseq arbitrary: s)
    case Nil then show ?case by simp
  next
    case (Cons prt rseq)
    obtain p r or u where prt: "prt = (p, r, or, u)" by (cases prt, blast)
    let ?\<sigma> = "mk_subst Var \<mu> ^^ i"
    note Cons = Cons[unfolded prt]
    from Cons(2) have ok: "isOK(check_qsteps_subst cni nfs P R rseq u t)" by (cases or, auto)
    have IH: "(u \<cdot> ?\<sigma> , t \<cdot> ?\<sigma>) \<in> PR ^^ (length rseq)" 
      by (rule Cons(1)[OF ok])
    have "(s \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> PR"
    proof (cases or)
      case True
      with Cons[unfolded prt]
      have "isOK (check_rqrstep_subst cni nfs P r s u)" by simp
      from check_rqrstep_subst[OF cni this]
        have "(s \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> rqrstep nfs (set Q) (set P)" .
      then show ?thesis unfolding PR ..
    next
      case False
      with Cons[unfolded prt]
      have "isOK (check_qrstep_subst cni nfs R p r s u)" by simp
      from check_qrstep_subst[OF cni this]
        have "(s \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> qrstep nfs (set Q) (set R)" .
      then show ?thesis unfolding PR ..
    qed
    with IH show ?case unfolding prt o_def using relpow_Suc_I2[of "s \<cdot> ?\<sigma>" "u \<cdot> ?\<sigma>" PR] by simp
  qed
qed

definition
  check_qrsteps_subst ::
    "(('f:: showl, 'v:: showl) term \<Rightarrow> ('f,'v)redex_prob check) \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) rules \<Rightarrow>
     ('f, 'v) rseq \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_qrsteps_subst cni nfs R prts s u \<equiv>
    check_qsteps_subst cni nfs [] R (map (\<lambda>(p, r, t). (p, r, False, t)) prts) s u"

lemma check_qrsteps_subst_sound:
  assumes cni: "cni = check_NF_iteration \<mu> Q"
    and ok: "isOK (check_qrsteps_subst cni nfs R rseq s t)"
  shows "(s \<cdot> mk_subst Var \<mu> ^^ i, t \<cdot> mk_subst Var \<mu> ^^ i) \<in> (qrstep nfs (set Q) (set R))^^(length rseq)"
proof -
  have empty: "rqrstep nfs (set Q) {} \<union> qrstep nfs (set Q) (set R) = qrstep nfs (set Q) (set R)"
    unfolding rqrstep_def qrstep_r_p_s_def by auto
  from check_qsteps_subst_sound[OF assms[unfolded check_qrsteps_subst_def]]
    show ?thesis by (auto simp: Let_def empty)
qed

end
