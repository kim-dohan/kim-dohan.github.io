(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Loops
imports
  First_Order_Rewriting.Trs
  First_Order_Rewriting.Term_Impl
  First_Order_Terms.Option_Monad
  "HOL-Library.Monad_Syntax"
begin


section \<open>decision procedures for innermost loops\<close>
type_synonym ('f, 'v) redex_prob = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) match_prob = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) gmatch_prob = "('f, 'v) match_prob list"
type_synonym ('f, 'v) ident_prob = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) nident_prob = "('f, 'v) term \<times> ('f, 'v) term \<times> nat"
type_synonym ('f, 'v) match_solution = "nat \<times> ('f, 'v) subst"
type_synonym ('f, 'v) redex_solution = "nat \<times> ('f, 'v) subst \<times> ('f, 'v) ctxt"

text \<open>The set of variables for which at some point a non-variable term will be substituted
when iteratively applying @{term "\<mu>"}.\<close>
inductive_set v_incr :: "('f,'v)subst \<Rightarrow> 'v set" for \<mu> where 
  is_Fun: "is_Fun (\<mu> x) \<Longrightarrow> x \<in> v_incr \<mu>"
| later: "\<mu> x = Var y \<Longrightarrow> y \<in> v_incr \<mu> \<Longrightarrow> x \<in> v_incr \<mu>"

lemma v_incr_is_Fun[elim]: "x \<in> v_incr \<mu> \<Longrightarrow> \<exists> i. is_Fun (Var x \<cdot> \<mu> ^^ i)"
proof (induct rule: v_incr.induct)
  case is_Fun
  then show ?case by (intro exI[of _ 1], auto)
next
  case (later x y)
  from later(3) obtain i where "is_Fun (Var y \<cdot> \<mu> ^^ i)" by auto
  with later(1) show ?case by (intro exI[of _ "Suc i"], auto simp: subst_compose)
qed

lemma is_Fun_v_incr[intro,elim]: "is_Fun (Var x \<cdot> \<mu> ^^ i) \<Longrightarrow> x \<in> v_incr \<mu>"
proof (induct i arbitrary: x)
  case (Suc i)
  show ?case
  proof (cases "\<mu> x")
    case (Fun f ls)
    show ?thesis by (rule v_incr.is_Fun, simp add: Fun)
  next
    case (Var y)
    from v_incr.later[OF Var Suc(1)] Suc(2) Var show ?thesis by (auto simp: subst_compose)
  qed
qed simp
  
lemma v_incr_def': "v_incr \<mu> = {x. \<exists> i. is_Fun (Var x \<cdot> \<mu> ^^ i)}"
  using v_incr_is_Fun[of _ \<mu>] is_Fun_v_incr[of _ _ \<mu>] by blast

definition v_incr_measure :: "('f,'v)subst \<Rightarrow> ('f,'v)term \<Rightarrow> nat" where
  "v_incr_measure \<mu> t \<equiv> case t of Fun _ _ \<Rightarrow> 0 | Var x \<Rightarrow> (if x \<in> v_incr \<mu> then (LEAST i. is_Fun (Var x \<cdot> \<mu> ^^ i)) else 0)"

lemma v_incr_measure_Fun[simp]: "v_incr_measure \<mu> (Fun f ts) = 0"
  unfolding v_incr_measure_def by simp

lemma v_incr_measure_non_incr[simp]: "x \<notin> v_incr \<mu> \<Longrightarrow> v_incr_measure \<mu> (Var x) = 0"
  unfolding v_incr_measure_def by simp

lemma v_incr_measure_less: fixes \<mu> :: "('f,'v)subst"
  assumes x: "x \<in> v_incr \<mu>" 
  shows "v_incr_measure \<mu> (\<mu> x) < v_incr_measure \<mu> (Var x)"
proof -
  define L where "L = (\<lambda> x. LEAST i. is_Fun (Var x \<cdot> \<mu> ^^ i))"
  from LeastI_ex[OF v_incr_is_Fun[OF x]] have f: "is_Fun (Var x \<cdot> \<mu> ^^ (L x))" unfolding L_def .
  then obtain n where Lx: "L x = Suc n" by (cases "L x", auto)
  then have l: "v_incr_measure \<mu> (Var x) = Suc n" unfolding v_incr_measure_def L_def using x by simp
  show ?thesis
  proof (cases "\<mu> x")
    case Fun
    then show ?thesis unfolding l by simp
  next
    case (Var y)
    with x have y: "y \<in> v_incr \<mu>" by (cases, auto)
    from f[unfolded Lx] Var have f: "is_Fun (Var y \<cdot> \<mu> ^^ n)" by (simp add: subst_compose)
    have "L y \<le> n" unfolding L_def by (rule Least_le, rule f)
    with y show ?thesis unfolding l by (simp add: Var v_incr_measure_def L_def)
  qed
qed

lemma v_incr_measure_lesseq[simp]: "v_incr_measure \<mu> (t \<cdot> \<mu>) \<le> v_incr_measure \<mu> t"
proof (cases t)
  case (Var x) note x = this
  show ?thesis
  proof (cases "x \<in> v_incr \<mu>")
    case True 
    from v_incr_measure_less[OF this] show ?thesis unfolding Var by simp
  next
    case False
    show ?thesis
    proof (cases "\<mu> x")
      case (Var y)
      from False have "y \<notin> v_incr \<mu>" using later[of \<mu>, OF Var] by blast
      then show ?thesis using x Var by auto
    qed (auto simp: x)
  qed
qed simp

text \<open>The set of all variables that ever occur in a term of the form @{term "t \<cdot> \<mu> ^^ i"},
for arbitrary @{term i}.\<close>
definition vars_iteration :: "('f,'v)subst \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v set" where
  "vars_iteration \<mu> t \<equiv> \<Union> {vars_term (t \<cdot> \<mu> ^^ i) | i::nat. True}"

definition gmatch_solved_form :: "('f, 'v) gmatch_prob \<Rightarrow> bool" where
  "gmatch_solved_form gmp \<equiv> \<forall>tl\<in>set gmp. is_Var (snd tl)"

locale fixed_subst = 
  fixes \<mu> :: "('f, 'v) subst"
begin

abbreviation W where "W \<equiv> vars_iteration \<mu>"

definition redex_solution :: "('f, 'v) redex_prob \<Rightarrow> ('f, 'v) redex_solution \<Rightarrow> bool" where
  "redex_solution rp sol \<equiv> case (rp, sol) of ((t, l), (i, \<sigma>, C)) \<Rightarrow> t \<cdot> (\<mu> ^^ i) = C\<langle>l \<cdot> \<sigma>\<rangle>"

definition match_solution :: "('f, 'v) match_prob \<Rightarrow> ('f, 'v) match_solution \<Rightarrow> bool" where
  "match_solution mp sol \<equiv> case (mp, sol) of ((t, l), (i, \<sigma>)) \<Rightarrow> t \<cdot> (\<mu> ^^ i) = l \<cdot> \<sigma>"

definition gmatch_solution :: "('f, 'v) gmatch_prob \<Rightarrow> ('f, 'v) match_solution \<Rightarrow> bool" where
  "gmatch_solution gmp sol \<equiv> \<forall>tl\<in>set gmp. match_solution tl sol"

definition ident_solution :: "('f, 'v) ident_prob \<Rightarrow> nat \<Rightarrow> bool" where
  "ident_solution ip n \<equiv> case ip of (s, t) \<Rightarrow> s \<cdot> (\<mu> ^^ n) = t \<cdot> (\<mu> ^^ n)"

definition match_prob_of_rp :: "('f, 'v) redex_prob \<Rightarrow> ('f, 'v) match_prob set" where
  "match_prob_of_rp rp \<equiv>
    (case rp of
      (t, Var x) \<Rightarrow> {(t, Var x)}
    | (t, Fun f ls) \<Rightarrow> {(u, Fun f ls) | s u. s \<in> {t} \<union> \<mu> ` W t \<and> s \<unrhd> u \<and> is_Fun u})"

text \<open>The next two lemmas correspond to Theorem 10 (Solving Redex Problems) of ``Deciding Innermost Loops''.\<close>
lemma match_prob_of_rp_sound:
  assumes sol: "match_solution (u, l') (i, \<sigma>)"
    and mp: "(u, l') \<in> match_prob_of_rp (t, l)"
  shows "\<exists>i C. redex_solution (t, l) (i, \<sigma>, C)"
proof -
  from sol[unfolded match_solution_def]
  have sol: "u \<cdot> \<mu> ^^ i = l' \<cdot> \<sigma>" by simp
  show ?thesis 
  proof (cases l)
    case (Var x)
    from mp[unfolded match_prob_of_rp_def] have "(u,l') = (t,l)" using Var by auto
    with sol have "t \<cdot> \<mu> ^^ i = \<box>\<langle>l\<cdot>\<sigma>\<rangle>" by simp
    then show ?thesis unfolding redex_solution_def split by blast
  next
    case (Fun f ls)
    from mp[unfolded match_prob_of_rp_def] obtain s where 
      s: "s \<in> {t} \<union> \<mu> ` W t" and su: "s \<unrhd> u" 
      and l': "l' = l" unfolding Fun by auto
    note sol = sol[unfolded l']
    from su obtain C where su: "s = C\<langle>u\<rangle>" ..
    from s have "\<exists> D n. t \<cdot> \<mu> ^^ n = D\<langle>s\<rangle>"
    proof
      assume s: "s \<in> {t}"
      show ?thesis by (rule exI[of _ \<box>], rule exI[of _ 0], insert s, auto)
    next
      assume "s \<in> \<mu> ` W t"
      then obtain x i where x: "x \<in> vars_term (t \<cdot> \<mu> ^^ i)" and s: "s = \<mu> x" unfolding vars_iteration_def by auto
      from x have "\<exists> C. t \<cdot> \<mu> ^^ i = C\<langle>Var x\<rangle>" 
      proof (induct i arbitrary: x)
        case 0
        then have "x \<in> vars_term t" by simp
        from supteq_Var[OF this] obtain C where t: "t = C\<langle>Var x\<rangle>" ..          
        then show ?case by auto
      next
        case (Suc i)
        have id0: "t \<cdot> \<mu> ^^ Suc i = t \<cdot> \<mu> ^^ i \<cdot> \<mu>" unfolding subst_power_Suc by auto
        from Suc have "x \<in> vars_term (t \<cdot> \<mu> ^^ i \<cdot> \<mu>)" unfolding id0 by simp
        from this[unfolded vars_term_subst[of "t \<cdot> \<mu> ^^ i"]]
        obtain y where x: "x \<in> vars_term (\<mu> y)" and y: "y \<in> vars_term (t \<cdot> \<mu> ^^ i)" by auto
        from Suc(1)[OF y] obtain C where id1: "t \<cdot> \<mu> ^^ i = C\<langle>Var y\<rangle>" by auto
        from supteq_Var[OF x] obtain D where id2: "\<mu> y = D\<langle>Var x\<rangle>" ..
        show ?case 
          by (rule exI[of _ "(C \<cdot>\<^sub>c \<mu>) \<circ>\<^sub>c D"], unfold id0 id1, simp add: id2)
      qed
      then obtain C where id: "t \<cdot> \<mu> ^^ i = C\<langle>Var x\<rangle>" ..      
      show ?thesis
      proof (intro exI)
        have "t \<cdot> \<mu> ^^ (Suc i) = t \<cdot> \<mu> ^^ i \<cdot> \<mu>" unfolding subst_power_Suc by simp
        also have "... = (C \<cdot>\<^sub>c \<mu>)\<langle>\<mu> x\<rangle>" unfolding id by simp
        finally show "t \<cdot> \<mu> ^^ Suc i = (C \<cdot>\<^sub>c \<mu>)\<langle>s\<rangle>" unfolding s .
      qed
    qed
    then obtain D n where ts: "t \<cdot> \<mu> ^^ n = D\<langle>s\<rangle>" by blast
    let ?E = "D \<circ>\<^sub>c C"
    have "t \<cdot> (\<mu> ^^ (n + i)) = (t \<cdot> \<mu> ^^ n) \<cdot> \<mu> ^^ i" unfolding subst_power_compose_distrib
      by simp
    also have "... = ?E\<langle>u\<rangle> \<cdot> \<mu> ^^ i" unfolding ts su by simp
    also have "... = (?E \<cdot>\<^sub>c \<mu>^^i)\<langle> u \<cdot> \<mu> ^^ i\<rangle>" by simp
    finally show ?thesis unfolding sol redex_solution_def split by blast
  qed
qed

lemma match_prob_of_rp_complete:
  assumes sol: "redex_solution (t, l) (i, \<sigma>, C)"
  shows "\<exists>\<tau> u j. (u, l) \<in> match_prob_of_rp (t, l) \<and> match_solution (u, l) (j, \<tau>)"
proof -
  from sol[unfolded redex_solution_def]
  have sol: "t \<cdot> \<mu> ^^ i = C\<langle>l \<cdot> \<sigma>\<rangle>" by simp
  show ?thesis 
  proof (cases l)
    case (Var x)
    then have mem: "(t,Var x) \<in> match_prob_of_rp (t,Var x)" unfolding match_prob_of_rp_def by auto
    show ?thesis unfolding Var
    proof (intro exI conjI, rule mem, unfold match_solution_def split)
      show "t \<cdot> \<mu> ^^ 0 = Var x \<cdot> (\<lambda> _. t)" by simp
    qed
  next
    case (Fun f ls)    
    let ?mp = "\<lambda> t. {u. \<exists> s. s \<in> {t} \<union> \<mu> ` W t \<and> s \<unrhd> u \<and> is_Fun u}"
    have mps: "match_prob_of_rp (t,l) = (\<lambda> u. (u,l)) ` ?mp t" unfolding match_prob_of_rp_def Fun by auto
    let ?mpsol = "\<lambda> t u j. u \<in> ?mp t \<and> u \<cdot> \<mu> ^^ j = l \<cdot> \<sigma>"
    let ?ex = "\<lambda> t. \<exists> u j. ?mpsol t u j"
    let ?sol = "\<lambda> t i C. t \<cdot> \<mu> ^^ i = C\<langle>l \<cdot> \<sigma>\<rangle>"
    let ?p = "\<lambda> (t,i,C). ?sol t i C \<longrightarrow> ?ex t"
    let ?m = "\<lambda> (t,i,C). i + size C"
    have "?p (t,i,C)" 
    proof (induct rule: wf_induct[of _ ?p, OF wf_measure, of ?m])
      case (1 tiC)
      obtain t i C where tiC: "tiC = (t,i,C)"  by (cases tiC, auto)
      note 1 = 1[THEN spec, THEN mp, unfolded tiC]
      show ?case unfolding tiC split
      proof (intro impI)
        assume sol: "?sol t i C"
        show "?ex t"
        proof (cases t)
          case (Var x)
          from sol obtain j where i: "i = Suc j" unfolding Fun Var by (cases i, cases C, auto)
          have sol: "?sol (\<mu> x) j C" unfolding sol[symmetric] i Var by (auto simp: subst_compose)
          let ?tiC = "(\<mu> x,j,C)"
          have "(?tiC,t,i,C) \<in> measure ?m" unfolding Var i by auto
          from 1[OF this, unfolded split, THEN mp, OF sol]
          obtain u k where sol: "?mpsol (\<mu> x) u k" by auto
          from sol have mem: "u \<in> ?mp (\<mu> x)" and id: "u \<cdot> \<mu> ^^ k = l \<cdot> \<sigma>" by auto
          from mem obtain s where s: "s \<in> {\<mu> x} \<union> \<mu> ` W (\<mu> x)" and mores: "s \<unrhd> u" "is_Fun u" by auto
          from s have s: "s \<in> \<mu> ` W t"
          proof 
            assume "s \<in> {\<mu> x}"
            then have s: "s = \<mu> x" by simp
            show "s \<in> \<mu> ` W t" unfolding vars_iteration_def
              by (rule, rule s, unfold Var, rule, rule, rule exI[of _ 0], auto)
          next
            assume "s \<in> \<mu> ` W (\<mu> x)"
            from this[unfolded vars_iteration_def] obtain i where s: "s \<in> \<mu> ` vars_term (\<mu> x \<cdot> \<mu> ^^ i)" by auto
            have id: "vars_term (\<mu> x \<cdot> \<mu> ^^ i) = vars_term (t \<cdot> \<mu> ^^ Suc i)" unfolding Var by (simp add: subst_compose)
            show "s \<in> \<mu> ` W t" unfolding vars_iteration_def using s[unfolded id] by blast
          qed
          show ?thesis
            by (intro exI, rule conjI[OF _ id], rule, rule exI[of _ s], insert s mores, auto)
        next
          case (Fun f ts)
          show ?thesis
          proof (cases C)
            case Hole
            from sol have sol: "t \<cdot> \<mu> ^^ i = l \<cdot> \<sigma>" unfolding Hole by auto
            show ?thesis
              by (intro exI, rule conjI[OF _ sol], rule, rule exI[of _ t], unfold Fun, auto)
          next
            case (More g bef D aft)
            let ?n = "length bef"
            from arg_cong[OF sol, of "length o args"] have len: "?n < length ts" unfolding Fun More by auto
            have "ts ! ?n \<cdot> \<mu> ^^ i = args (t \<cdot> \<mu> ^^ i) ! ?n" unfolding Fun 
              by (simp add: nth_map[OF len])
            also have "... = args (C\<langle>l\<cdot>\<sigma>\<rangle>) ! ?n" using sol by simp
            also have "... = D\<langle>l\<cdot>\<sigma>\<rangle>" unfolding More by simp
            finally have sol: "?sol (ts ! ?n) i D" .
            have "((ts ! ?n, i, D), t, i, C) \<in> measure ?m" unfolding More by simp
            from 1[OF this, unfolded split, THEN mp, OF sol]
            obtain u k where sol: "?mpsol (ts ! ?n) u k" by auto
            from sol have mem: "u \<in> ?mp (ts ! ?n)" and id: "u \<cdot> \<mu> ^^ k = l \<cdot> \<sigma>" by auto
            from mem obtain s where s: "s \<in> {ts ! ?n} \<union> \<mu> ` W (ts ! ?n)" and mores: "s \<unrhd> u" "is_Fun u" by auto
            from len have mem: "ts ! ?n \<in> set ts" by auto
            from s have u: "u \<in> ?mp t" 
            proof
              assume "s \<in> {ts ! ?n}"
              then have s: "s = ts ! ?n" by simp
              show ?thesis
              proof (rule, rule exI[of _ t], intro conjI)
                show "t \<unrhd> u" unfolding Fun using mem mores(1)
                  unfolding s by auto
              qed (insert mores, auto)
            next
              assume "s \<in> \<mu> ` W (ts ! ?n)"
              from this[unfolded vars_iteration_def] obtain i where s: "s \<in> \<mu> ` vars_term (ts ! ?n \<cdot> \<mu> ^^ i)" by auto
              from mem have "vars_term (ts ! ?n) \<subseteq> vars_term t" unfolding Fun by auto
              with s have "s \<in> \<mu> ` vars_term (t \<cdot> \<mu> ^^ i)" unfolding vars_term_subst by auto
              then have "s \<in> \<mu> ` W t" unfolding vars_iteration_def by auto
              with mores show ?thesis by auto
            qed
            with id have "?mpsol t u k" by auto
            then show ?thesis by blast
          qed
        qed
      qed
    qed                
    with sol show ?thesis unfolding mps match_solution_def by blast
  qed
qed

abbreviation "V_incr \<equiv> v_incr \<mu>"

lemma subst_V_incr: assumes \<mu>: "\<mu> x = Var y" shows "(x \<in> V_incr) = (y \<in> V_incr)"
proof
  assume "y \<in> V_incr"
  from later[OF \<mu> this] show "x \<in> V_incr" .
next
  assume "x \<in> V_incr"
  from this \<mu> show "y \<in> V_incr"
    by (cases rule: v_incr.cases, auto)
qed
end 

typedef ('f,'v)subst_incr = "{(\<mu> :: ('f,'v)subst, vs, W). v_incr \<mu> = vs \<and> finite (subst_domain \<mu>) \<and> 
  (\<forall> t. set (W t) = vars_iteration \<mu> t)}"
proof 
  show "(Var, {}, vars_term_list) \<in> 
    {(\<mu>, vs, W). v_incr \<mu> = vs \<and> finite (subst_domain \<mu>) \<and> (\<forall> t. set (W t) = vars_iteration \<mu> t)}" 
  unfolding v_incr_def' vars_iteration_def by auto
qed

setup_lifting type_definition_subst_incr
lift_definition si_v_incr :: "('f,'v)subst_incr \<Rightarrow> 'v set" is "fst o snd" .
lift_definition si_subst :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)subst" is fst .
lift_definition si_W :: "('f,'v)subst_incr \<Rightarrow> ('f,'v)term \<Rightarrow> 'v list" is "snd o snd" .

lemma si_v_incr: "si_v_incr \<sigma>_incr = v_incr (si_subst \<sigma>_incr)"
  by (transfer, auto)

lemma finite_si_subst: "finite (subst_domain (si_subst \<sigma>_incr))"
  by (transfer, auto)

lemma si_W: "set (si_W \<sigma>_incr t) = vars_iteration (si_subst \<sigma>_incr) t"
  by (transfer, auto)

locale fixed_subst_incr =
  fixes \<mu>_incr :: "('f,'v)subst_incr"

sublocale fixed_subst_incr \<subseteq> fixed_subst "si_subst \<mu>_incr" .

context fixed_subst_incr
begin
abbreviation "\<mu> \<equiv> si_subst \<mu>_incr"
abbreviation "V_sincr \<equiv> si_v_incr \<mu>_incr"
lemma V_sincr[simp]: "V_sincr = V_incr" by (simp add: si_v_incr)

function
  simplify_mp ::
    "('f, 'v) gmatch_prob \<Rightarrow> ('f, 'v) gmatch_prob \<Rightarrow> (('f, 'v) gmatch_prob \<times> nat) option"
where
  "simplify_mp [] solved = Some (solved, 0)"
| "simplify_mp ((s, Var x) # mp) solved = simplify_mp mp ((s,Var x) # solved)"
| "simplify_mp ((Fun g ts, Fun f ls) # mp) solved = do {
    guard (f = g);
    pairs \<leftarrow> zip_option ts ls;
    simplify_mp (pairs @ mp) solved
  }"
| "simplify_mp ((Var x, Fun f ls) # mp) solved = do {
    guard (x \<in> V_sincr);
    let m = map (\<lambda>(s, l). (s \<cdot> \<mu>, l));
    (smp, i) \<leftarrow> simplify_mp (m ((Var x, Fun f ls) # mp)) (m solved); 
    Some (smp, Suc i) 
  }"
  by pat_completeness auto

termination
proof -
  let ?f = "\<lambda>(t, l). v_incr_measure \<mu> t"
  let ?R = "measures [\<lambda>(mp, sp). size_list size (map snd mp), 
                      \<lambda>(mp, sp). size_list ?f mp]"
  show ?thesis
  proof 
    fix s x and mp solved :: "('f,'v) gmatch_prob"
    show "((mp,(s,Var x) # solved), (s, Var x) # mp, solved) \<in> ?R"
      by (rule measures_lesseq[OF _ measures_less], simp_all add: o_def)
  next
    fix g::"'f"
      and ts::"('f, 'v) term list" and f ls mp and solved pairs :: "('f,'v) gmatch_prob"
    assume "f = g" and d: "zip_option ts ls = Some pairs"
    show "((pairs @ mp, solved), (Fun g ts, Fun f ls) # mp, solved) \<in> ?R"
      by (rule measures_less) (insert d zip_size_aux[of ts ls], auto simp: o_def)
  next
    fix x f and ls :: "('f,'v)term list" and mp solved :: "('f,'v)gmatch_prob"
      and mu :: "('f,'v)gmatch_prob \<Rightarrow> ('f,'v)gmatch_prob"
    assume x: "x \<in> V_sincr" and mu: "mu = map (\<lambda>(s,y). (s \<cdot> \<mu>, y))"
    from x have x: "x \<in> v_incr \<mu>" by simp
    let ?mu = "(\<lambda>(s,y). (s \<cdot> \<mu>, y))"
    have id: "size o snd o ?mu = size o snd"
      by (intro ext, auto)
    have one: "?f (?mu (Var x, Fun f ls)) < ?f ((Var x, Fun f ls))" unfolding split term.simps
      using v_incr_measure_less[OF x] by simp
    have two: "size_list ?f (map ?mu mp) \<le> size_list ?f mp"
      unfolding size_list_map
      by (rule size_list_pointwise, force)
    from one two 
    have main: "size_list ?f (map ?mu ((Var x, Fun f ls) # mp)) < size_list ?f ((Var x, Fun f ls) # mp)" 
      by auto
    have [simp]: "\<And> x. snd (case x of (s, x) \<Rightarrow> (s \<cdot> \<mu>, x)) = snd x" by (case_tac x, auto)
    show "((mu ((Var x, Fun f ls) # mp), mu solved), (Var x, Fun f ls) # mp, solved) \<in> ?R" unfolding mu
      by (rule measures_lesseq[OF _ measures_less], simp add: id, insert main, 
        auto simp: o_def)
  qed simp
qed
end

declare fixed_subst_incr.simplify_mp.simps[code]

context fixed_subst_incr
begin
lemma simplify_mp_solved_form:
  assumes res: "simplify_mp mp1 mp2 = Some (mp3, i)" 
    and sf: "gmatch_solved_form mp2"
  shows "gmatch_solved_form mp3"
proof -
  let ?P = "\<lambda>mp1 mp2. \<forall> mp3i. simplify_mp mp1 mp2 = Some mp3i \<longrightarrow> gmatch_solved_form mp2 \<longrightarrow> gmatch_solved_form (fst mp3i)"
  have "?P mp1 mp2"
  proof (induct rule: simplify_mp.induct[of ?P])
    case (1 mp2)
    then show ?case by simp
  next
    case (2 s x mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3
      assume res: "simplify_mp ((s, Var x) # mp1) mp2 = Some mp3" and 
        sf: "gmatch_solved_form mp2"
      show "gmatch_solved_form (fst mp3)"
      proof (rule 2[THEN spec[of _ mp3], THEN mp, THEN mp])
        show "simplify_mp mp1 ((s, Var x) # mp2) = Some mp3"
          using res by simp
      next
        show "gmatch_solved_form ((s, Var x) # mp2)" using sf unfolding gmatch_solved_form_def
          by auto
      qed
    qed
  next
    case (3 g ts f ls mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3
      assume res: "simplify_mp ((Fun g ts, Fun f ls) # mp1) mp2 = Some mp3"
        and sf: "gmatch_solved_form mp2"
      then have fg: "f = g" by (cases "f = g", auto)
      note res = res[unfolded fg]
      from res obtain pairs where dec: "zip_option ts ls = Some pairs"
        by (cases "zip_option ts ls", auto)
      from res dec have res: "simplify_mp (pairs @ mp1) mp2 = Some mp3" by auto
      show "gmatch_solved_form (fst mp3)"
        using 3[OF fg dec] sf res by auto
    qed
  next
    case (4 x f ls mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3
      assume res: "simplify_mp ((Var x, Fun f ls) # mp1) mp2 = Some mp3"
        and sf: "gmatch_solved_form mp2"
      then have x: "x \<in> V_sincr" by (cases "x \<in> V_incr", auto)
      let ?mu = "map (\<lambda>(s,y). (s \<cdot> \<mu>, y))"
      from sf have sf: "gmatch_solved_form (?mu mp2)" unfolding gmatch_solved_form_def by auto
      let ?l = "simplify_mp (?mu ((Var x, Fun f ls) # mp1)) (?mu mp2)"
      obtain res where l: "?l = Some res" using res x by (cases ?l, auto)
      from res x l have "fst res = fst mp3" by (cases res, auto)
      with 4[OF x, THEN spec, THEN mp[OF _ l]] sf 
        show "gmatch_solved_form (fst mp3)" by auto
    qed
  qed
  with assms
  show ?thesis by simp
qed

lemma simplify_mp_solution:
  assumes "simplify_mp mp1 mp2 = mp3i"
  shows "(mp3i = None \<longrightarrow> \<not> gmatch_solution (mp1 @ mp2) (n,\<sigma>)) \<and> (\<forall> mp3 i. mp3i = Some (mp3,i) \<longrightarrow> gmatch_solution (mp1 @ mp2) (n + i, \<sigma>) = gmatch_solution mp3 (n,\<sigma>) \<and> (\<forall> k. k < i \<longrightarrow> \<not> gmatch_solution (mp1 @ mp2) (k,\<sigma>)))"
proof -
  let ?sol = "\<lambda> mp n. gmatch_solution mp (n, \<sigma>)"
  let ?eq = "\<lambda> mp1 mp2 mp3 n i. ?sol (mp1 @ mp2) (n + i) = ?sol mp3 n"
  let ?small = "\<lambda> mp1 mp2 i. \<forall> k. (k < i \<longrightarrow> \<not> ?sol (mp1 @ mp2) k)"
  let ?snd = "\<lambda> mp1 mp2 mp3i n. \<forall> mp3 i. mp3i = Some (mp3,i) \<longrightarrow> ?eq mp1 mp2 mp3 n i \<and> ?small mp1 mp2 i"
  let ?fst = "\<lambda> mp1 mp2 mp3i n. mp3i = None \<longrightarrow> \<not> ?sol (mp1 @ mp2) n"
  let ?both = "\<lambda> mp1 mp2 mp3i n. ?fst mp1 mp2 mp3i n \<and> ?snd mp1 mp2 mp3i n"
  let ?res = "\<lambda> mp1 mp2 mp3i. simplify_mp mp1 mp2 = mp3i"
  let ?P = "\<lambda> mp1 mp2. \<forall> mp3i n. ?res mp1 mp2 mp3i \<longrightarrow> ?both mp1 mp2 mp3i n"
  have "?P mp1 mp2" 
  proof (induct rule: simplify_mp.induct[of ?P])
    case (1 mp2)
    show ?case by simp
  next
    case (2 s x mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3i n
      assume "?res ((s,Var x) # mp1) mp2 mp3i"
      then have "?res mp1 ((s,Var x) # mp2) mp3i" by auto
      from 2[THEN spec, THEN spec, THEN mp[OF _ this]]
      show "?both ((s,Var x) # mp1) mp2 mp3i n"
        unfolding gmatch_solution_def by auto
    qed
  next
    case (3 g ts f ls mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3i n
      assume res: "?res ((Fun g ts, Fun f ls) # mp1) mp2 mp3i"
      show "?both ((Fun g ts, Fun f ls) # mp1) mp2 mp3i n"
      proof (cases "f = g")
        case False
        then show ?thesis using res unfolding gmatch_solution_def match_solution_def by auto
      next
        case True
        show ?thesis
        proof (cases "zip_option ts ls")
          case None
          {
            fix f g :: "('f,'v)term \<Rightarrow> ('f,'v)term"
            have "map f ts \<noteq> map g ls" 
            proof 
              assume "map f ts = map g ls"
              from arg_cong[OF this, of length] and None show False by simp
            qed
          } 
          with True None res show ?thesis
            unfolding gmatch_solution_def match_solution_def
            by (auto) metis
        next
          case (Some pairs)
          from Some have len: "length ts = length ls" by auto
          from Some have pairs: "pairs = zip ts ls" by auto
          from res have res: "?res (pairs @ mp1) mp2 mp3i" using True Some by auto
          from len have len: "length ts = length (map (\<lambda> t. t \<cdot> \<sigma>) ls)" by simp
          have main: "\<And> n. match_solution (Fun g ts, Fun g ls) (n,\<sigma>) = gmatch_solution (zip ts ls) (n,\<sigma>)" 
            unfolding gmatch_solution_def match_solution_def split set_zip eval_term.simps term.simps
            unfolding map_nth_eq_conv[OF len]
            by (insert len, auto)
          note rec = 3[OF True Some, THEN spec, THEN spec, THEN mp[OF _ res], of n]
          show ?thesis
          proof (cases mp3i)
            case None
            with rec show ?thesis using main unfolding True pairs gmatch_solution_def by auto
          next
            case (Some mp3)
            then obtain mp i where mp3i: "mp3i = Some (mp,i)" by (cases mp3, auto)
            with rec show ?thesis unfolding True pairs
              by (auto simp: main gmatch_solution_def)
          qed
        qed
      qed
    qed
  next
    case (4 x f ls mp1 mp2)
    show ?case
    proof (intro allI impI)
      fix mp3i n
      assume res: "?res ((Var x, Fun f ls) # mp1) mp2 mp3i"
      show "?both ((Var x, Fun f ls) # mp1) mp2 mp3i n"
      proof (cases "x \<in> V_incr")
        case False
        have "\<not> match_solution (Var x, Fun f ls) (n, \<sigma>)"
        proof
          assume "match_solution (Var x, Fun f ls) (n, \<sigma>)"
          then have "Var x \<cdot> (\<mu> ^^ n) = Fun f ls \<cdot> \<sigma>" 
            unfolding match_solution_def by auto
          then have "is_Fun (Var x \<cdot> (\<mu> ^^ n))" by auto
          with False show False by auto
        qed
        with res False show ?thesis unfolding gmatch_solution_def by auto
      next
        case True
        let ?mp1 = "((Var x, Fun f ls) # mp1)"
        let ?mu = "(\<lambda>(s,y). (s \<cdot> \<mu>, y))"
        let ?mmp1 = "map ?mu ?mp1"
        let ?mmp2 = "map ?mu mp2"
        let ?f = "(\<lambda>(smp, i). Some (smp, Suc i))"
        from True res 
        have res: "simplify_mp ?mmp1 ?mmp2 \<bind> ?f = mp3i" by (simp add: Let_def)
        obtain mp3i' where mp3i': "simplify_mp ?mmp1 ?mmp2 = mp3i'" by auto
        with res have res: "mp3i' \<bind> ?f = mp3i" by simp
        obtain pairs where pairs: "pairs = ?mp1 @ mp2" by auto
        have id: "?both ((Var x, Fun f ls) # mp1) mp2 mp3i n = (?both pairs [] mp3i n)" unfolding pairs gmatch_solution_def by auto
        from 4[OF _ refl, THEN spec, THEN spec, THEN mp[OF _ mp3i']]
          have rec: "\<And> n. ?both (map ?mu pairs) [] mp3i' n"
          unfolding pairs gmatch_solution_def using True by auto
        show ?thesis unfolding id
        proof (cases mp3i')
          case None
          with res have res: "mp3i = None" by auto
          have "\<not> ?sol pairs n" 
          proof 
            assume sol: "?sol pairs n"
            then obtain m where n: "n = Suc m" unfolding gmatch_solution_def match_solution_def pairs
              by (cases n, auto)
            from sol[unfolded n] have "?sol (map ?mu pairs) m"
              unfolding gmatch_solution_def match_solution_def pairs by auto
            with rec[of m] None show False by auto
          qed
          with res show "?both pairs [] mp3i n" by auto
        next
          case (Some mpi')
          then obtain mp i where mpi': "mpi' = (mp,i)" by (cases mpi', auto)
          with Some have mp3i': "mp3i' = Some (mp,i)" by auto
          with res have mp3i: "mp3i = Some (mp, Suc i)" by auto
          from rec have id: "\<And> n. ?sol (map ?mu pairs) (n + i) = ?sol mp n" unfolding mp3i' by auto
          from rec have not: "\<And> k. k < i \<Longrightarrow> \<not> ?sol (map ?mu pairs) k" unfolding mp3i' by auto
          {
            fix k
            assume k: "k < Suc i"
            have "\<not> ?sol pairs k"
            proof (cases k)
              case (Suc l)
              from not[of l] k show ?thesis unfolding Suc gmatch_solution_def match_solution_def by auto
            next
              case 0
              then show ?thesis unfolding gmatch_solution_def match_solution_def pairs by auto
            qed
          } note not = this
          have id: "\<And> n. ?sol mp n = ?sol pairs (Suc n + i)" unfolding id[symmetric]
            unfolding gmatch_solution_def match_solution_def by auto
          then show "?both pairs [] mp3i n" unfolding mp3i using not by auto                
        qed
      qed
    qed
  qed
  with assms show ?thesis by auto
qed

lemma simplify_mp_complete:
  assumes "gmatch_solution mp (n, \<sigma>)"
  shows "\<exists>smp i k. simplify_mp mp [] = Some (smp, i) \<and> n = i + k \<and> gmatch_solution smp (k, \<sigma>)"
proof (cases "simplify_mp mp []")
  case None
  from simplify_mp_solution[OF None] assms
  show ?thesis by simp
next
  case (Some smpi)
  then obtain smp i where s: "simplify_mp mp [] = Some (smp,i)" by (cases smpi, auto)
  note main = simplify_mp_solution[OF s, THEN conjunct2, THEN spec, THEN spec, THEN mp[OF _ refl], of _ \<sigma>]
  show ?thesis
  proof (cases "n < i")
    case True
    with main assms show ?thesis by auto
  next
    case False
    then have "n = i + (n - i)" by auto
    then obtain k where n: "n = i + k" by auto
    then have n': "n = k + i" by simp
    show ?thesis
    proof (intro exI conjI, rule s, rule n)
      show "gmatch_solution smp (k,\<sigma>)" using main[of k] assms[unfolded n'] by simp
    qed
  qed
qed

lemma simplify_mp_sound: 
  assumes res: "simplify_mp mp [] = Some (smp, i)" 
    and sol: "gmatch_solution smp (n, \<sigma>)"
  shows "gmatch_solution mp (n + i, \<sigma>)"
  using simplify_mp_solution[OF res] sol by auto
end


fun ident_prob_of_smp :: "('f, 'v) gmatch_prob \<Rightarrow> ('f, 'v) ident_prob list" where
  "ident_prob_of_smp [] = []"
| "ident_prob_of_smp ((t, l) # other) = map (\<lambda>(s, _). (t, s)) (filter (\<lambda>(_, s). s = l) other) @ ident_prob_of_smp other"

lemma ident_prob_of_smp: 
  "set (ident_prob_of_smp smp) = { (fst (smp ! i), fst (smp ! j)) | i j. i < j \<and> j < length smp \<and> snd (smp ! i) = snd (smp ! j)}" (is "_ = ?s smp")
proof (induct smp)
  case (Cons tx smp)
  obtain t x where tx: "tx = (t,x)" by (cases tx, auto)
  let ?one = "(\<lambda>(s,u). (t,s)) ` {y \<in> set smp. case y of (u,s) \<Rightarrow> s = x}"
  let ?p = "\<lambda> i j xs uv. i < j \<and> j < length xs \<and> snd (xs ! i) = snd (xs ! j) \<and> uv = (fst (xs ! i), fst (xs ! j))"
  have "set (ident_prob_of_smp (tx # smp)) = ?one \<union> ?s smp" 
    unfolding tx using Cons by simp
  also have "... = ?s ((t,x)  # smp)" (is "?l = ?r")    
  proof -
    {
      fix u v 
      assume "(u,v) \<in> ?one"
      then have mem: "(v,x) \<in> set smp" and u: "u = t" by auto
      then obtain i where mem: "smp ! i = (v,x)" and i: "i < length smp" unfolding set_conv_nth by auto
      have "(u,v) \<in> ?r"
        by (rule, rule exI[of _ 0], rule exI[of _ "Suc i"], insert mem i u, auto)
    } then have "?one \<subseteq> ?r" ..
    moreover
    { 
      fix u v
      assume "(u,v) \<in> ?s smp"
      then obtain i j where p: "?p i j smp (u,v)" by auto
      have "(u,v) \<in> ?r"
        by (rule, rule exI[of _ "Suc i"], rule exI[of _ "Suc j"], insert p, auto)
    } then have "?s smp \<subseteq> ?r" ..
    moreover
    {
      fix u v 
      assume "(u,v) \<in> ?r"
      then obtain i j where p: "?p i j ((t,x) # smp) (u,v)" by auto
      from p obtain j' where j: "j = Suc j'" by (cases j, auto)
      have "(u,v) \<in> ?l"
      proof (cases i)
        case (Suc i')
        have "(u,v) \<in> ?s smp"
          by (rule, rule exI[of _ i'], rule exI[of _ j'], insert p Suc j, auto)
        then show ?thesis by simp
      next
        case 0
        have "(u,v) \<in> ?one"
          unfolding set_conv_nth using p unfolding j 0 by force
        then show ?thesis by simp
      qed
    } then have "?r \<subseteq> ?l" ..
    ultimately show ?thesis by blast
  qed
  finally show ?case unfolding tx .
qed simp

context fixed_subst
begin
lemma ident_prob_of_smp_complete:
  assumes sol: "gmatch_solution smp (n,\<sigma>)"
    and mem: "(s, t) \<in> set (ident_prob_of_smp smp)"
  shows "ident_solution (s,t) n"
proof -
  from mem[unfolded ident_prob_of_smp]
  obtain i j where ij: "i < j" "j < length smp" 
    and snd: "snd (smp ! i) = snd (smp ! j)" 
    and fst: "s = fst (smp ! i)" "t = fst (smp ! j)" by auto
  from ij have ij: "i < length smp" "j < length smp" by auto
  then have "smp ! i \<in> set smp" "smp ! j \<in> set smp" by auto
  with sol[unfolded gmatch_solution_def] 
  have sol: "match_solution (smp ! i) (n,\<sigma>)" "match_solution (smp ! j) (n,\<sigma>)" by auto
  from fst obtain si where si: "smp ! i = (s,si)" by (cases "smp ! i", auto)
  from fst obtain sj where sj: "smp ! j = (t,sj)" by (cases "smp ! j", auto)
  from snd si sj have sj: "smp ! j = (t,si)" by auto
  from sol[unfolded si sj] show ?thesis unfolding match_solution_def ident_solution_def by auto
qed

lemma ident_prob_of_smp_sound: 
  assumes smp: "gmatch_solved_form smp"
    and sol: "\<And>s t. (s, t) \<in> set (ident_prob_of_smp smp) \<Longrightarrow> \<exists>m\<le>n. ident_solution (s, t) m"
  shows "\<exists>\<sigma>. gmatch_solution smp (n, \<sigma>)"
  unfolding gmatch_solution_def
proof (rule exI, clarify)
  fix t x
  assume mem: "(t,x) \<in> set smp"
  with smp[unfolded gmatch_solved_form_def] obtain x' where x: "x = Var x'" by (cases x, auto)
  let ?smp = "(map (\<lambda>(t,x). (the_Var x, t)) smp)"
  let ?\<sigma> = "\<lambda> x. the (map_of ?smp x) \<cdot> \<mu> ^^ n" 
  from mem x have mem': "(x',t) \<in> set ?smp" by force
  have "t \<cdot> \<mu> ^^ n = ?\<sigma> x'" 
  proof (cases "map_of ?smp x'")
    case None
    from this[unfolded map_of_eq_None_iff] and mem' have False by force
    then show ?thesis by auto
  next
    case (Some s)
    from map_of_SomeD[OF this] obtain y' where me: "(s,y') \<in> set smp"
      and "the_Var y' = x'" by auto
    with smp[unfolded gmatch_solved_form_def] have y': "y' = Var x'" by (cases y', auto)
    with me have me: "(s,Var x') \<in> set smp" by auto
    from mem[unfolded x] me obtain i j where ij: "i < length smp" "j < length smp"
      and smpij: "smp ! i = (t,Var x')" "smp ! j = (s,Var x')" unfolding set_conv_nth by auto
    note sol = sol[unfolded ident_prob_of_smp]
    show ?thesis unfolding Some option.sel 
    proof (cases "i = j")
      case True
      with smpij have "s = t" by simp
      then show "t \<cdot> \<mu> ^^ n = s \<cdot> \<mu> ^^ n" by simp
    next
      case False
      then have "i < j \<or> j < i" by arith
      then have "\<exists> m \<le> n. t \<cdot> \<mu> ^^ m = s \<cdot> \<mu> ^^ m"
      proof
        assume lt: "i < j"
        have "\<exists> m \<le> n. ident_solution (t,s) m"
          by (rule sol, insert lt ij smpij, force)
        then show ?thesis unfolding ident_solution_def by auto
      next
        assume lt: "j < i"
        have "\<exists> m \<le> n. ident_solution (s,t) m"
          by (rule sol, insert lt ij smpij, force)
        then show ?thesis unfolding ident_solution_def by auto
      qed
      then obtain m where m: "m \<le> n" and id: "t \<cdot> \<mu> ^^ m = s \<cdot> \<mu> ^^ m" by auto
      from m have "n = m + (n - m)" by auto
      then obtain k where n: "n = m + k" by auto
      show "t \<cdot> \<mu> ^^ n = s \<cdot> \<mu> ^^ n" unfolding n subst_power_compose_distrib
        using id by simp
    qed
  qed
  then show "match_solution (t,x) (n, ?\<sigma>)" 
    unfolding match_solution_def split x by simp
qed
end

context fixed_subst_incr
begin  

definition gmatch_to_idents :: "('f, 'v) gmatch_prob \<Rightarrow> (nat \<times> ('f, 'v) ident_prob list) option" where
  "gmatch_to_idents mp \<equiv> do {
    (smp, i) \<leftarrow> simplify_mp mp [];
    Some (i, ident_prob_of_smp smp)
  }"

lemma gmatch_to_idents_complete:
  assumes sol: "gmatch_solution mp (n, \<sigma>)"
  shows "\<exists>i idps. gmatch_to_idents mp = Some (i, idps) \<and> (\<forall>idp\<in>set idps. \<exists>n. ident_solution idp n)"
proof -
  from sol have "gmatch_solution mp (n,\<sigma>)" unfolding gmatch_solution_def by auto
  from simplify_mp_complete[OF this] obtain smp i k
    where res: "simplify_mp mp [] = Some (smp, i)" and n: "n = i + k" 
    and sol: "gmatch_solution smp (k,\<sigma>)" by auto
  from simplify_mp_solved_form[OF res] have sf: "gmatch_solved_form smp"
    unfolding gmatch_solved_form_def by auto
  from ident_prob_of_smp_complete[OF sol]
  show ?thesis
    by (force simp: gmatch_to_idents_def res)
qed

lemma gmatch_to_idents_sound: 
  assumes res: "gmatch_to_idents mp = Some (i, idps)"
  and sol: "\<And>idp. idp \<in> set idps \<Longrightarrow> ident_solution idp (ns idp)"
  shows "\<exists>\<sigma>. gmatch_solution mp (max_list (map ns idps) + i, \<sigma>)"
proof -
  from sol have  sol: "\<And>idp. idp \<in> set idps \<Longrightarrow> ident_solution idp (ns idp)" by auto
  let ?n = "max_list (map ns idps)"
  note res = res[unfolded gmatch_to_idents_def]
  from res obtain smpi where res1: "simplify_mp mp [] = Some smpi"
    by (cases "simplify_mp mp []", auto)
  obtain smp j where smpi: "smpi = (smp,j)" by (cases smpi, auto)
  note res1 = res1[unfolded smpi]
  from simplify_mp_solved_form[OF res1] have sf: "gmatch_solved_form smp"
    unfolding gmatch_solved_form_def by auto
  note res = res[unfolded res1]
  from res have res2: "ident_prob_of_smp smp = idps"  and j: "j = i" by auto
  have sol: "\<exists> \<sigma>. gmatch_solution smp (?n, \<sigma>)"
  proof (rule ident_prob_of_smp_sound[OF sf, unfolded res2])
    fix s t
    assume mem: "(s,t) \<in> set idps"
    show "\<exists> m \<le> ?n. ident_solution (s,t) m"
      by (rule, rule conjI[OF max_list sol[OF mem]], insert mem, auto)
  qed
  then obtain \<sigma> where sol: "gmatch_solution smp (?n,\<sigma>)" by auto
  from simplify_mp_sound[OF res1[unfolded smpi] sol]
  show ?thesis unfolding j gmatch_solution_def by auto
qed

definition match_to_idents :: "('f, 'v) match_prob \<Rightarrow> (nat \<times> ('f, 'v) ident_prob list) option" where
  "match_to_idents t_l \<equiv> gmatch_to_idents [t_l]"

lemma match_to_idents_complete:
  assumes sol: "match_solution t_l (n, \<sigma>)"
  shows "\<exists>i idps. match_to_idents t_l = Some (i, idps) \<and> (\<forall>idp\<in>set idps. \<exists>n. ident_solution idp n)"
proof -
  from sol have sol: "gmatch_solution [t_l] (n,\<sigma>)" unfolding gmatch_solution_def by auto
  from gmatch_to_idents_complete[OF sol] show ?thesis unfolding match_to_idents_def .
qed

lemma match_to_idents_sound: 
  assumes res: "match_to_idents (t, l) = Some (i, idps)"
  and sol: "\<And>idp. idp \<in> set idps \<Longrightarrow> ident_solution idp (ns idp)"
  shows "\<exists>\<sigma>. match_solution (t, l) (max_list (map ns idps) + i, \<sigma>)"
proof -
  from gmatch_to_idents_sound[OF res[unfolded match_to_idents_def] sol]
  show ?thesis unfolding gmatch_solution_def by auto
qed
end

section \<open>solving identity problems\<close>

context fixed_subst
begin
fun conflicts :: "('f, 'v) term \<times> ('f, 'v) term \<times> nat \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term \<times> nat) list" where
  "conflicts (s, Var x, Suc n) = conflicts (s, \<mu> x, n)"
| "conflicts (Var x, Var y, 0) = (if x = y then [] else [(Var x, Var y, 0)])"
| "conflicts (Fun f ts, Var y, 0) = [(Var y, Fun f ts, 0)]"
| "conflicts (Var x, Fun g ss, n) = [(Var x, Fun g ss, n)]"
| "conflicts (Fun f ts, Fun g ss, n) = 
    (if f = g \<and> length ts = length ss 
      then concat (map (\<lambda>(s, t). conflicts (s, t, n)) (zip ts ss))
      else [(Fun f ts, Fun g ss, n)])"

lemma conflicts_fun:
  assumes "(f,length ss) = (g,length ts)"
  shows "set (conflicts (Fun f ss, Fun g ts,n)) = \<Union> {set (conflicts (ss ! i, ts ! i, n)) | i. i < length ts}"
  using assms
  by (force simp: set_zip)

lemma term_subst_eq_via_conflicts: 
   "(s \<cdot> \<sigma> = t \<cdot> \<mu> ^^ n \<cdot> \<sigma>) = (\<forall> u v m. (u,v,m) \<in> set (conflicts (s,t,n)) \<longrightarrow> (u \<cdot> \<sigma> = v \<cdot> \<mu> ^^ m \<cdot> \<sigma>))"
proof (induct rule: conflicts.induct[of "\<lambda> (s,t,n). (s \<cdot> \<sigma> = t \<cdot> \<mu> ^^ n \<cdot> \<sigma>) = ((\<forall> u v m. (u,v,m) \<in> set (conflicts (s,t,n)) \<longrightarrow> (u \<cdot> \<sigma> = v \<cdot> \<mu> ^^ m \<cdot> \<sigma>)))" "(s,t,n)", unfolded split])
  case (2 x y)
  show ?case by (cases "x = y", auto)
next
  case (5 f ss g ts n)
  show ?case
  proof (cases "(f,length ss) = (g,length ts)")
    case False
    then show ?thesis by auto
  next
    case True
    then have f: "f = g" and l: "length ss = length ts" by auto
    let ?f = "\<lambda> t. t \<cdot> \<sigma>"
    let ?g = "\<lambda> t. t \<cdot> \<mu> ^^ n \<cdot> \<sigma>"
    have "(Fun f ss \<cdot> \<sigma> = (Fun g ts) \<cdot> \<mu> ^^ n \<cdot> \<sigma>) = (map (\<lambda> t. t \<cdot> \<sigma>) ss = map (\<lambda> t. t \<cdot> \<mu> ^^ n \<cdot> \<sigma>) ts)" (is "?l = _") unfolding f by auto
    also have "... = (\<forall> i < length ts. ss ! i \<cdot> \<sigma> = ts ! i \<cdot> \<mu> ^^ n \<cdot> \<sigma>)" (is "_ = ?r")
      using nth_map_conv[OF l, of ?f ?g] map_nth_conv[of ?f ss ?g ts] unfolding l by blast
    finally have id: "?l = ?r" .
    from l have id3: "set (zip ss ts) = {(ss ! i, ts ! i) | i. i < length ts}"
      unfolding set_zip by auto
    note 5 = 5[unfolded f l id3, OF conjI[OF refl refl] _ refl]
    from 5 have 5: "\<And> i. i < length ts \<Longrightarrow> (ss ! i \<cdot> \<sigma> = ts ! i \<cdot> \<mu> ^^ n \<cdot> \<sigma>) = (\<forall> u v m. (u,v,m) \<in> set (conflicts (ss ! i, ts ! i, n)) \<longrightarrow> u \<cdot> \<sigma> = v \<cdot> \<mu> ^^ m \<cdot> \<sigma>)" by blast
    let ?l = "\<forall> u v m. (u,v,m) \<in> \<Union> {set (conflicts (ss ! i, ts ! i, n)) | i. i < length ts} \<longrightarrow> u \<cdot> \<sigma> = v \<cdot> \<mu> ^^ m \<cdot> \<sigma>"
    show ?thesis unfolding id conflicts_fun[OF True] l 
    proof
      assume ?l
      show ?r
      proof (intro allI impI)
        fix i
        assume i: "i < length ts"
        show "ss ! i \<cdot> \<sigma> = ts ! i \<cdot> \<mu> ^^ n \<cdot> \<sigma>"
          unfolding 5[OF i] using \<open>?l\<close> i by blast
      qed
    next
      assume ?r
      show ?l
      proof (intro allI impI)
        fix u v m
        assume "(u,v,m) \<in> \<Union>{set (conflicts (ss ! i, ts ! i, n)) | i. i < length ts}"
        then obtain i where mem: "(u,v,m) \<in> set (conflicts (ss ! i, ts ! i, n))" and i: "i < length ts"
          by auto
        from 5[OF i] mem show "u \<cdot> \<sigma> = v \<cdot> \<mu> ^^ m \<cdot> \<sigma>" using \<open>?r\<close> i by blast
      qed
    qed
  qed
qed (auto simp: subst_compose)

definition conflict_terms :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) terms" where
  "conflict_terms s t = \<Union>((\<lambda> u. {v . u \<unrhd> v}) ` (subst_range \<mu> \<union> {s,t}))"

lemma conflict_terms_subst: "conflict_terms s (\<mu> x) \<subseteq> conflict_terms s (Var x)"
  "conflict_terms (\<mu> x) s \<subseteq> conflict_terms (Var x) s"
proof -
  have "subst_range \<mu> \<union> {s,\<mu> x} \<subseteq> subst_range \<mu> \<union> {s,Var x}"
    by (cases "x \<in> subst_domain \<mu>", auto simp: subst_domain_def)
  then show "conflict_terms s (\<mu> x) \<subseteq> conflict_terms s (Var x)"
  "conflict_terms (\<mu> x) s \<subseteq> conflict_terms (Var x) s"
    unfolding conflict_terms_def by auto
qed 

lemma conflict_terms_refl: "s \<in> conflict_terms s t" "t \<in> conflict_terms s t"
  unfolding conflict_terms_def by auto

lemma conflict_terms_arg: assumes "i < length ss"
  shows "conflict_terms (ss ! i) t \<subseteq> conflict_terms (Fun f ss) t" "conflict_terms t (ss ! i) \<subseteq> conflict_terms t (Fun f ss)" 
proof -
  from assms have "ss ! i \<in> set ss" by auto 
  then have "{v. ss ! i \<unrhd> v} \<subseteq> {v. Fun f ss \<unrhd> v}" "vars_term (ss ! i) \<subseteq> vars_term (Fun f ss)" by auto
  then show "conflict_terms (ss ! i) t \<subseteq> conflict_terms (Fun f ss) t" "conflict_terms t (ss ! i) \<subseteq> conflict_terms t (Fun f ss)" 
    unfolding conflict_terms_def
    unfolding image_Un by auto
qed

lemma conflict_terms_mono:
  assumes "{u,v} \<subseteq> conflict_terms s t"
  shows "conflict_terms u v \<subseteq> conflict_terms s t" (is "?c u v \<subseteq> _")
proof -
  note c = conflict_terms_def
  {
    fix u s
    assume "u \<in> ?c s s" 
    then have "?c u u \<subseteq> ?c s s" unfolding c by (auto intro: supteq_trans)
  } note main = this
  {
    fix u s t
    assume "u \<in> ?c s t"
    then have "u \<in> ?c s s \<or> u \<in> ?c t t" unfolding c by auto
    with main[of u s] main[of u t] have "?c u u \<subseteq> ?c s s \<union> ?c t t" by blast
    then have "?c u u \<subseteq> ?c s t" unfolding c by blast
  } note main = this
  from assms have mem: "u \<in> ?c s t" "v \<in> ?c s t" by auto
  from main[OF mem(1)] main[OF mem(2)] have "?c u u \<union> ?c v v \<subseteq> ?c s t" by auto
  then show ?thesis unfolding c by auto
qed


lemma conflicts: 
  assumes "(u,v,m) \<in> set (conflicts (s,t,n))"
  shows "({u,v} \<subseteq> conflict_terms s t \<and> eroot u \<noteq> eroot v \<and> (is_Var v \<longrightarrow> is_Var u \<and> m = 0)) \<and> (\<exists> k p . n = m + k \<and> p \<in> poss s \<and> p \<in> poss (t \<cdot> \<mu> ^^ k) \<and> ((s |_ p, t \<cdot> \<mu> ^^ k |_ p) = (u,v) \<or> (s |_ p, t \<cdot> \<mu> ^^ k |_ p) = (v,u) \<and> m = 0))"
proof -
  let ?ct = "\<lambda> s t. conflict_terms s t"
  let ?cp = "\<lambda> s t n. set (conflicts (s,t,n))"
  let ?k = "\<lambda> s t n u v m k p. n = m + k \<and> p \<in> poss s \<and> p \<in> poss (t \<cdot> \<mu> ^^ k) \<and> ((s |_ p, t \<cdot> \<mu> ^^ k |_ p) = (u,v) \<or> (s |_ p, t \<cdot> \<mu> ^^ k |_ p) = (v,u) \<and> m = 0)"
  let ?p = "\<lambda> s t u v m. {u,v} \<subseteq> ?ct s t \<and> eroot u \<noteq> eroot v \<and> (is_Var v \<longrightarrow> is_Var u \<and> m = 0)"
  let ?P = "\<lambda> s t n u v m. ?p s t u v m \<and> (\<exists> k p. ?k s t n u v m k p)"
  let ?P' = "\<lambda> (s,t,n). (\<forall> u v m. (u,v,m) \<in> ?cp s t n \<longrightarrow> ?P s t n u v m)"
  show ?thesis
  proof (induct rule: conflicts.induct[of ?P' "(s,t,n)", unfolded split, THEN spec, THEN spec, THEN spec, THEN mp[OF _ assms]])
    case (1 s x n)
    let ?s = s let ?t = "Var x" let ?n = "Suc n"
    let ?s' = s let ?t' = "\<mu> x" let ?n' = "n"
    show ?case
    proof (intro allI impI)
      fix u v m
      assume "(u,v,m) \<in> ?cp ?s ?t ?n"
      then have "(u,v,m) \<in> ?cp ?s' ?t' ?n'" by simp
      from 1[THEN spec, THEN spec, THEN spec, THEN mp[OF _ this]]
      obtain k p where p: "?p ?s' ?t' u v m" and k: "?k ?s' ?t' ?n' u v m k p" by blast
      show "?P ?s ?t ?n u v m"
        by (rule conjI[OF _ exI[of _ "Suc k"]], rule conjI[OF subset_trans[OF _ conflict_terms_subst(1)]], insert p k, auto simp: subst_compose)
    qed
  next
    case (2 x y)
    let ?s = "Var x" let ?t = "Var y" let ?n = 0
    show ?case
    proof (intro allI impI)
      fix u v m
      assume mem: "(u,v,m) \<in> ?cp ?s ?t ?n"
      then have xy: "x \<noteq> y" by (cases "x = y", auto)
      with mem have m: "m = 0" and disj: "u = Var x \<and> v = Var y \<or> u = Var y \<and> v = Var x" by auto
      from disj have ct: "{u,v} \<subseteq> ?ct ?s ?t" using conflict_terms_refl by auto
      from disj ct xy have p: "?p ?s ?t u v m" unfolding m by auto
      show "?P ?s ?t ?n u v m"
        by (rule conjI[OF p], rule exI, rule exI[of _ "[]"], insert disj m, auto)
    qed
  next
    case (3 f ts y)
    let ?s = "Fun f ts" let ?t = "Var y" let ?n = 0
    show ?case
    proof (intro allI impI)
      fix u v m
      assume mem: "(u,v,m) \<in> ?cp ?s ?t ?n"
      then have uvm: "u = ?t" "v = ?s" "m = ?n" by auto
      from uvm have ct: "{u,v} \<subseteq> ?ct ?s ?t" using conflict_terms_refl by auto
      from ct uvm have p: "?p ?s ?t u v m" by auto
      show "?P ?s ?t ?n u v m"
        by (rule conjI[OF p], rule exI, rule exI[of _ "[]"], insert uvm, auto)
    qed
  next 
    case (4 x g ss n)
    let ?s = "Var x" let ?t = "Fun g ss" let ?n = n
    show ?case
    proof (intro allI impI)
      fix u v m
      assume mem: "(u,v,m) \<in> ?cp ?s ?t ?n"
      then have uvm: "u = ?s" "v = ?t" "m = ?n" by auto
      from uvm have ct: "{u,v} \<subseteq> ?ct ?s ?t" using conflict_terms_refl by auto
      from ct uvm have p: "?p ?s ?t u v m" by auto
      show "?P ?s ?t ?n u v m"
        by (rule conjI[OF p], rule exI, rule exI[of _ "[]"], insert uvm, auto)
    qed
  next
    case (5 f ss g ts n)
    let ?s = "Fun f ss" let ?t = "Fun g ts" let ?n = n
    show ?case
    proof (intro allI impI)
      fix u v m
      assume mem: "(u,v,m) \<in> ?cp ?s ?t ?n"
      show "?P ?s ?t ?n u v m"
      proof (cases "(f,length ss) = (g,length ts)")
        case False
        with mem have uvm: "u = ?s" "v = ?t" "m = ?n" by auto
        from uvm have ct: "{u,v} \<subseteq> ?ct ?s ?t" using conflict_terms_refl by auto
        from ct uvm False have p: "?p ?s ?t u v m" by auto
        show "?P ?s ?t ?n u v m"
          by (rule conjI[OF p], rule exI, rule exI[of _ "[]"], insert uvm, auto)
      next
        case True
        from conflicts_fun[OF this, of n] mem
        obtain i where i: "i < length ts" and mem: "(u,v,m) \<in> ?cp (ss ! i) (ts ! i) n" by auto
        have "?P (ss ! i) (ts ! i) n u v m"
          by (rule 5[OF _ _ refl, THEN spec, THEN spec, THEN spec, THEN mp[OF _ mem]], insert True i, auto simp: set_zip)
        then obtain k p where p: "?p (ss ! i) (ts ! i) u v m" and k: "?k (ss ! i) (ts ! i) n u v m k p" by auto
        let ?p = "i # p"
        show ?thesis 
        proof (intro conjI exI)
          show "?p \<in> poss (?t \<cdot> \<mu> ^^ k)" using k i by auto
        next
          have "{u,v} \<subseteq> ?ct (ss ! i) (ts ! i)" using p by auto
          also have "... \<subseteq> ?ct ?s (ts ! i)" by (rule conflict_terms_arg, insert i True, auto)
          also have "... \<subseteq> ?ct ?s ?t" by (rule conflict_terms_arg[OF i])
          finally show "{u,v} \<subseteq> ?ct ?s ?t" .
        qed (insert k p i True, auto)
      qed
    qed
  qed
qed

lemma conflicts_neq: assumes "(u,v,m) \<in> set (conflicts (s,t,n))"
  shows "u \<noteq> v \<cdot> \<mu> ^^ m" 
proof -
  from conflicts[OF assms]
  have "eroot u \<noteq> eroot v" "is_Var v \<Longrightarrow> is_Var u \<and> m = 0" by auto
  then show ?thesis
    by (cases v, (cases u, auto)+)
qed

lemma term_eq_via_conflicts_empty: 
   "s = t \<cdot> \<mu> ^^ n \<longleftrightarrow> set (conflicts (s, t, n)) = {}" (is "_ \<longleftrightarrow> ?C = {}")
proof -
  have "(s = t \<cdot> \<mu> ^^ n) = (s \<cdot> Var = t \<cdot> \<mu> ^^ n \<cdot> Var)" by simp
  note main = this[unfolded term_subst_eq_via_conflicts[of s Var t]]
  show ?thesis 
  proof
    assume id: "s = t \<cdot> \<mu> ^^ n"
    {
      fix uvm
      assume "uvm \<in> ?C"
      then obtain u v m where mem: "(u,v,m) \<in> ?C" by (cases uvm rule: prod.exhaust) auto
      with id[unfolded main] have "u = v \<cdot> \<mu> ^^ m" by simp
      with conflicts_neq[OF mem] have False by simp
    }
    then show "?C = {}" by fastforce
  next
    assume "?C = {}" then show "s = t \<cdot> \<mu> ^^ n" unfolding main by auto
  qed
qed   
end

context fixed_subst_incr
begin

lemma finite: "finite (subst_domain \<mu>)"
  by (rule finite_si_subst)

definition nident_solution :: "('f, 'v) nident_prob \<Rightarrow> nat \<Rightarrow> bool" where
  "nident_solution ip n \<equiv> case ip of (s, t, m) \<Rightarrow> s \<cdot> (\<mu> ^^ n) = t \<cdot> \<mu> ^^ m \<cdot> \<mu> ^^ n"

(* comments:
   - one can add conflict (x,y) with x,y \<notin> dom \<mu> 
     (but this will be detected one step later)
   - one can drop case (x,f(..)) with x \<notin> V_incr, but this may take a while
     until a duplicate is created, but for paper this is a nice result     
*)

function ident_solve' :: "('f, 'v) nident_prob set \<Rightarrow> ('f, 'v) nident_prob \<Rightarrow> nat option" where
  "ident_solve' cps st = (let cp = set (conflicts st) in
    if (\<exists>f ss t n. (Fun f ss, t,n) \<in> cp) then None
    else if (\<exists>u v n m. (u, v, n) \<in> cp \<and> (u, v, m) \<in> cps) then None
    else do {
      is \<leftarrow> mapM (\<lambda>(u, v, m). ident_solve' (insert (u, v, m) cps) (u \<cdot> \<mu>, v, Suc m)) (conflicts st);
      Some (max_list (map Suc is))
    })"
  by pat_completeness auto

termination
proof -  
  let ?Rl = "\<lambda> s t. conflict_terms s t \<inter> {Var x | x. True}"
  let ?Rr = "\<lambda> s t. conflict_terms s t"
  let ?Rm = "\<lambda> cps. (\<lambda> (u,v,_). (u,v)) ` cps"
  let ?rel = "\<lambda>(cps,(s,t,_)). card ((?Rl s t \<times> ?Rr s t) - ?Rm cps)"
  show ?thesis
  proof
    show "wf (measure ?rel)"
      by (rule wf_measure)
  next
    fix cps stn cp uvm u v vm m
    assume id: "cp = set (conflicts stn)"
    and id2: "(u,vm) = uvm"
        "(v,m) = vm"
    and mem: "uvm \<in> set (conflicts stn)"
    and nmem: "\<not> (\<exists> u v n m. (u,v,n) \<in> cp \<and> (u,v,m :: nat) \<in> cps)"
    and no_fun: "\<not> (\<exists> f ss t n. (Fun f ss, t, n) \<in> cp)"   
    from id2 mem have mem: "(u,v,m) \<in> set (conflicts stn)" by auto
    with no_fun[unfolded id] obtain x where u: "u = Var x" by (cases u, auto)
    obtain s t n where stn: "stn = (s,t,n)" by (cases stn, auto)
    note mem = mem[unfolded stn u]
    note nmem = nmem[unfolded id stn]
    let ?x = "Var x :: ('f,'v)term"
    from conflicts[OF mem] have xv: "{?x,v} \<subseteq> conflict_terms s t" and x: "?x \<in> conflict_terms s t" and v: "v \<in> conflict_terms s t" by auto
    from x have xvar: "?x \<in> ?Rl s t" by force
    let ?Left = "?Rl (?x \<cdot> \<mu>) v \<times> ?Rr (?x \<cdot> \<mu>) v - ?Rm (insert (?x, v, m) cps)"
    let ?Right = "?Rl s t \<times> ?Rr s t - ?Rm cps"
    show "((insert (u,v,m) cps, u \<cdot> \<mu>, v, Suc m), (cps,stn)) \<in> measure ?rel" 
      unfolding stn in_measure split u
    proof (rule psubset_card_mono)
      show "?Left \<subset> ?Right"
      proof
        show "?Left \<subseteq> ?Right" 
        proof
          fix y w
          assume "(y,w) \<in> ?Left"
          then have y: "y \<in> ?Rl (?x \<cdot> \<mu>) v" and w: "w \<in> ?Rr (?x \<cdot> \<mu>) v" and yw: "(y,w) \<notin> ?Rm cps" by auto
          show "(y,w) \<in> ?Right"
          proof(rule DiffI[OF SigmaI yw])
            show "w \<in> ?Rr s t" using w conflict_terms_subst(2)[of x v] v conflict_terms_mono[OF xv] by auto
          next
            show "y \<in> ?Rl s t" using y conflict_terms_subst(2)[of x v] v conflict_terms_mono[OF xv] by auto               
          qed
        qed
      next
        have "(?x, v) \<in> ?Right" using xvar v nmem mem by force
        moreover have "(?x, v) \<notin> ?Left" using nmem by auto
        ultimately show "?Left \<noteq> ?Right" by auto
      qed
    next
      have fin: "finite (conflict_terms s t)" 
        unfolding conflict_terms_def subst_range.simps
        using finite_subterms[of s] finite_subterms[of t]
        by (auto intro: finite finite_subterms)
      then show "finite ?Right" by auto
    qed
  qed
qed

definition ident_solve :: "('f, 'v) ident_prob \<Rightarrow> nat option" where
  "ident_solve \<equiv> \<lambda>(s, t). ident_solve' {} (s, t, 0)"


(* obvious from termination proof, but has to be proven separately *)
lemma ident_solve'_bound_main: fixes S T :: "('f,'v)term"
  defines ct: "ct \<equiv> conflict_terms S T"
  defines vct: "vct \<equiv> ct \<inter> {Var x | x. True}"
  defines vct_ct: "vct_ct \<equiv> vct \<times> ct"
  defines t3: "t3 \<equiv> (\<lambda> (u :: ('f,'v)term,v :: ('f,'v)term ,m :: nat). (u,v))"
  defines VCT: "VCT \<equiv> insert (S,T) ( (\<lambda> (u,v). (u \<cdot> \<mu>,v)) ` vct_ct)"
  assumes res: "ident_solve' cps stn = Some i"
  and cps: "t3 ` cps \<subseteq> vct_ct"
  and ST: "(\<lambda> (s,t,n). (s,t)) stn \<in> VCT"
  shows "i + card (t3 ` cps) \<le> card (vct_ct)"
proof -  
  note d = ct vct vct_ct split VCT
  from res cps ST show ?thesis
  proof (induct cps stn arbitrary: i rule: ident_solve'.induct)
    case (1 cps st i)
    obtain s t n where st: "st = (s,t,n)" by (cases st, force)
    note 1 = 1[unfolded st split]
    from 1(2) have sol: "ident_solve' cps (s,t,n) = Some i" .
    note simp = ident_solve'.simps[of "cps" st, unfolded Let_def sol st]
    let ?cp = "set (conflicts (s,t,n))"
    let ?c1 = "\<exists> f ss t n. (Fun f ss, t, n) \<in> ?cp"
    from simp have c1: "?c1 = False" by (cases ?c1, auto)
    note simp = simp[unfolded this]
    let ?c5 = "\<exists> u v n m. (u,v,n) \<in> ?cp \<and> (u, v,m) \<in> cps"
    from simp have c5: "?c5 = False" by (cases ?c5, auto)
    note simp = simp[unfolded this]
    let ?recs = "mapM (\<lambda>(u,v,m). ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m)) (conflicts (s,t,n))"
    obtain iis where recs: "?recs = Some iis" using simp by (cases ?recs, auto)
    note simp = simp[unfolded this]
    let ?res = "map (\<lambda> i. Suc i) iis"
    have i: "i = max_list ?res" using simp by simp
    have fin: "finite (conflict_terms S T)" 
      unfolding conflict_terms_def subst_range.simps
      using finite_subterms[of S] finite_subterms[of T]
      by (auto intro: finite finite_subterms)
    then have fin: "finite vct_ct" unfolding d by auto
    from card_mono[OF fin 1(3)]
    have le: "card (t3 ` cps) \<le> card vct_ct" .
    show ?case
    proof (cases "?res = []")
      case True 
      then show ?thesis unfolding i using le by simp
    next
      case False
      from max_list_mem[OF False] i have i: "i \<in> set (map Suc iis)" by auto
      then obtain j where j: "j \<in> set iis" and i: "i = Suc j" by auto
      from j[unfolded set_conv_nth] obtain k where j: "j = iis ! k" and k: "k < length iis"
        by auto
      from mapM_Some[OF recs, THEN conjunct1, THEN arg_cong[of _ _ length]] 
      have len: "length iis = length (conflicts (s,t,n))" by simp
      obtain u v m where uv: "conflicts (s,t,n) ! k = (u,v,m)" by (cases "conflicts (s,t,n) ! k", auto)
      from k[unfolded len] have mem: "(u,v,m) \<in> set (conflicts (s,t,n))" unfolding set_conv_nth uv[symmetric] by blast      
      from conflicts[OF mem] have uvc: "{u,v} \<subseteq> conflict_terms s t"
        by auto
      from c1 mem obtain x where ux: "u = Var x" by (cases u, auto)
      from 1(4) have "(s,t) \<in> VCT" by auto
      then have "(s,t) = (S,T) \<or> (\<exists> u. (u,t) \<in> vct_ct \<and> s = u \<cdot> \<mu>)" (is "_ \<or> ?u") unfolding VCT by auto
      then have memvct: "(u,v) \<in> vct_ct" unfolding VCT
      proof
        assume "(s,t) = (S,T)"
        with uvc ux show ?thesis unfolding d by force
      next
        assume ?u
        then obtain u' where u't: "(u',t) \<in> vct_ct" and s: "s = u' \<cdot> \<mu>" by auto
        then obtain y where u': "u' = Var y" and u't: "{u',t} \<subseteq> ct" unfolding d by (cases u', auto)
        from conflict_terms_subst(2)[of y t] have "conflict_terms s t \<subseteq> conflict_terms u' t" unfolding s u' by auto
        with uvc ux conflict_terms_mono[OF u't[unfolded d]] show ?thesis unfolding d by auto
      qed
      then have VCT: "(u \<cdot> \<mu>, v) \<in> VCT" unfolding VCT by auto
      from memvct 1(3) have subset: "t3 ` insert (u,v,m) cps \<subseteq> vct_ct" unfolding t3 by auto
      from mapM_Some_idx[OF recs k[unfolded len], unfolded uv split] j 
      have sol: "ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m) = Some j" by auto
      note IH = 1(1)[OF refl _ (* _ _ *) _ mem refl refl sol subset VCT, unfolded c1 (* c2 c4 *) c5]
      have "card (insert (u,v) (t3 ` cps)) = Suc (card (t3 ` cps))"
      proof (rule card_insert_disjoint[OF finite_subset[OF 1(3) fin]])
        from c5 mem show "(u,v) \<notin> t3 ` cps" unfolding t3 by auto
      qed
      then have card: "card (t3 ` insert (u,v,m) cps) = Suc (card (t3 ` cps))" unfolding t3 by simp
      have "i + card (t3 ` cps) = Suc j + card (t3 ` cps)" unfolding i by simp
      also have "... = j + card (t3 ` insert (u,v,m) cps)" unfolding card by simp        
      also have "... \<le> card vct_ct" using IH by simp
      finally show ?thesis .
    qed
  qed
qed

lemma ident_solve'_bound:
  fixes s t :: "('f,'v)term"
  defines ct: "ct \<equiv> conflict_terms s t"
  defines vct: "vct \<equiv> ct \<inter> {Var x | x. True}"
  assumes res: "ident_solve' {} (s,t,0) = Some i"
  shows "i \<le> card (vct \<times> ct)"
proof -
  from ident_solve'_bound_main[OF res, of s t]
  show ?thesis  unfolding vct ct by auto
qed


lemma ident_solve'_sound: 
  shows "ident_solve' cps st = Some i \<longrightarrow> nident_solution st i"
proof (induct cps st arbitrary: i rule: ident_solve'.induct)
  case (1 cps st i)
  obtain s t n where st: "st = (s,t,n)" by (cases st, force)
  note 1 = 1[unfolded st]
  show ?case unfolding st
  proof (intro impI)
    assume sol: "ident_solve' cps (s,t,n) = Some i"
    note simp = ident_solve'.simps[of "cps" st, unfolded Let_def sol st]
    let ?cp = "set (conflicts (s,t,n))"
    let ?c1 = "\<exists> f ss t n. (Fun f ss, t, n) \<in> ?cp"
    from simp have c1: "?c1 = False" by (cases ?c1, auto)
    note simp = simp[unfolded this]
    let ?c5 = "\<exists> u v n m. (u,v,n) \<in> ?cp \<and> (u, v,m) \<in> cps"
    from simp have c5: "?c5 = False" by (cases ?c5, auto)
    note simp = simp[unfolded this]
    let ?recs = "mapM (\<lambda>(u,v,m). ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m)) (conflicts (s,t,n))"
    obtain iis where recs: "?recs = Some iis" using simp by (cases ?recs, auto)
    note simp = simp[unfolded this]
    let ?res = "map (\<lambda> i. Suc i) iis"
    have i: "i = max_list ?res" using simp by simp
    show "nident_solution (s,t,n) i" unfolding nident_solution_def split
      term_subst_eq_via_conflicts[of s]
    proof (intro allI impI)
      fix u v m
      assume uv: "(u,v,m) \<in> ?cp"
      then obtain idx where idx: "idx < length (conflicts (s,t,n))" and uvi: "conflicts (s,t,n) ! idx = (u,v,m)" 
        unfolding set_conv_nth by auto
      from mapM_Some_idx[OF recs idx, unfolded uvi split] obtain j where 
        sol: "ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m) = Some j" and j: "j = iis ! idx" by auto
      from 1[OF refl, THEN mp[OF _ sol], OF _ _ uv] c1 (* c2 c4 *) c5
      have "nident_solution (u \<cdot> \<mu>, v, Suc m) j" by auto
      from this[unfolded nident_solution_def split]
      have "u \<cdot> \<mu> ^^ Suc j = v \<cdot> \<mu> ^^ (Suc m + j)"  unfolding subst_power_compose_distrib by simp
      also have "... = v \<cdot> \<mu> ^^ (m + Suc j)" by auto
      also have "... = v \<cdot> \<mu> ^^ m \<cdot> \<mu> ^^ Suc j" unfolding subst_power_compose_distrib by simp
      finally have sol: "u \<cdot> \<mu> ^^ Suc j = v \<cdot> \<mu> ^^ m \<cdot> \<mu> ^^ Suc j" .        
      from idx j have "Suc j \<in> set ?res" unfolding mapM_Some[OF recs, THEN conjunct1] by auto
      from max_list[OF this] have "Suc j \<le> i" unfolding i .
      then have "i = Suc j + (i - Suc j)" by auto
      then obtain k where i: "i = Suc j + k" ..
      from arg_cong[OF sol, of "\<lambda> u. u \<cdot> \<mu> ^^ k"]
      show "u \<cdot> \<mu> ^^ i = v \<cdot> \<mu> ^^ m \<cdot> \<mu> ^^ i" unfolding i subst_power_compose_distrib by simp
    qed
  qed
qed

lemma ident_solution_subt:
  assumes sol: "ident_solution (S,T) m"
    and p: "p \<in> poss (S \<cdot> \<mu> ^^ n)" "p \<in> poss (T \<cdot> \<mu> ^^ n)"
  shows "S \<cdot> \<mu> ^^ n |_ p \<cdot> \<mu> ^^ m = T \<cdot> \<mu> ^^ n |_ p \<cdot> \<mu> ^^ m"
proof -
  let ?sol = "\<lambda> s t n. s \<cdot> \<mu> ^^ n = t \<cdot> \<mu> ^^ n"
  from sol have sol: "?sol S T m" unfolding ident_solution_def by auto
  from arg_cong[OF sol, of "\<lambda> s. s \<cdot> \<mu> ^^ n"]
  have "?sol S T (m + n)" unfolding subst_power_compose_distrib by simp
  then have "?sol S T (n + m)" by (simp add: ac_simps)
  then have sol: "?sol (S \<cdot> \<mu> ^^ n) (T \<cdot> \<mu> ^^ n) m" unfolding subst_power_compose_distrib by simp
  show ?thesis
    unfolding subt_at_subst [OF p(1), symmetric]
      and subt_at_subst [OF p(2), symmetric]
      and sol ..
qed

lemma ident_solve'_complete:
  assumes SOL: "ident_solution (S,T) M"
  shows "\<forall> p n. p \<in> poss (S \<cdot> \<mu> ^^ n) 
      \<longrightarrow>  p \<in> poss (T \<cdot> \<mu> ^^ n)
      \<longrightarrow> ((S \<cdot> \<mu> ^^ n) |_ p, (T \<cdot> \<mu> ^^ n) |_ p) \<in> {(s,t \<cdot> \<mu> ^^ N), (t \<cdot> \<mu> ^^ N, s)}
      \<longrightarrow> (\<forall> u v m. (u,v,m) \<in> cps \<longrightarrow> (\<exists> p' n'. (m > 0 \<longrightarrow> is_Fun v) \<and> p' \<le>\<^sub>p p \<and> n' < n \<and> p' \<in> poss (S \<cdot> \<mu> ^^ n') \<and> p' \<in> poss (T \<cdot> \<mu> ^^ n') \<and> eroot u \<noteq> eroot v \<and> ((S \<cdot> \<mu> ^^ n') |_ p', (T \<cdot> \<mu> ^^ n') |_ p') \<in> {(u,v \<cdot> \<mu> ^^ m),(v \<cdot> \<mu> ^^ m,u)}))
      \<longrightarrow> (ident_solve' cps (s,t,N) \<noteq> None)" (is "?P s t N cps")
proof (induct rule: ident_solve'.induct[of "\<lambda> cps (s,t,N). ?P s t N cps" cps "(s,t,N)", unfolded split])
  case (1 cps st)
  obtain s t N where st: "st = (s,t,N)" by (cases st, force)
  note 1 = 1[unfolded st split]
  let ?sol = "\<lambda> s t N n. s \<cdot> \<mu> ^^ n = t \<cdot> \<mu> ^^ N \<cdot> \<mu> ^^ n"
  let ?cp = "set (conflicts (s,t,N))"
  let ?P = "\<lambda> u' v' m p'' n' P N. (m > 0 \<longrightarrow> is_Fun v') \<and> p'' \<le>\<^sub>p P \<and> n' < N \<and> p'' \<in> poss (S \<cdot> \<mu> ^^ n') \<and> p'' \<in> poss (T \<cdot> \<mu> ^^ n') \<and> eroot u' \<noteq> eroot v' \<and> (S \<cdot> \<mu> ^^ n' |_ p'', T \<cdot> \<mu> ^^ n' |_ p'') \<in> {(u',v' \<cdot> \<mu> ^^ m), (v' \<cdot> \<mu> ^^ m, u')}"
  let ?Q = "\<lambda> u' v' m P N. \<exists> p'' n'. ?P u' v' m p'' n' P N"
  note SOL = ident_solution_subt[OF SOL]
  show ?case unfolding st split
  proof (intro allI impI)
    fix p n
    assume p: "p \<in> poss (S \<cdot> \<mu> ^^ n)" "p \<in> poss (T \<cdot> \<mu> ^^ n)"
      and st: "(S \<cdot> \<mu> ^^ n |_ p, T \<cdot> \<mu> ^^ n |_ p) \<in> {(s,t \<cdot> \<mu> ^^ N),(t \<cdot> \<mu> ^^ N,s)}"
      and CPS: "\<forall> u v m. (u,v,m) \<in> cps \<longrightarrow> ?Q u v m p n"
    from SOL[OF p] st have sol: "?sol s t N M" by auto
    {
      fix u v m
      assume "(u,v,m) \<in> cps"
      from CPS[THEN spec, THEN spec, THEN spec, THEN mp[OF _ this]]
      obtain p' n' where p': "p' \<in> poss (S \<cdot> \<mu> ^^ n')" "p' \<in> poss (T \<cdot> \<mu> ^^ n')"
        and id: "(S \<cdot> \<mu> ^^ n' |_ p', T \<cdot> \<mu> ^^ n' |_ p') \<in> {(u,v \<cdot> \<mu> ^^ m),(v \<cdot> \<mu> ^^ m, u)}" by blast
      from SOL[OF p'] id have "?sol u v m M" by auto
    } note sol_cps = this
    note simp = ident_solve'.simps[of cps "(s,t,N)", unfolded Let_def]
    let ?c1 = "\<exists> f ss t n. (Fun f ss, t, n) \<in> ?cp"
    let ?c5 = "\<exists> u v n m. (u,v,n) \<in> ?cp \<and> (u, v,m) \<in> cps"
    from sol[unfolded term_subst_eq_via_conflicts[of s]]
    have cps: "\<And> u v m. (u,v,m) \<in> ?cp \<Longrightarrow> ?sol u v m M" by auto
    {
      assume ?c1
      then obtain f ss t n where cp: "(Fun f ss, t,n) \<in> ?cp" by auto
      from arg_cong[OF cps[OF this], of eroot] conflicts[OF cp, THEN conjunct1] have False by auto
    }
    then have c1: "?c1 = False" by blast
    note simp = simp[unfolded c1]
    {
      assume ?c5
      then obtain u v n1 n2 where cp: "(u,v,n1) \<in> ?cp" "(u,v,n2) \<in> cps" by auto
      from conflicts[OF cp(1)] obtain k1 q where 
        n1: "N = n1 + k1" and
        var: "is_Var v \<longrightarrow> n1 = 0" and
        eroot: "eroot u \<noteq> eroot v"  and
        q: "q \<in> poss s" "q \<in> poss (t \<cdot> \<mu> ^^ k1)"  and
        uv: "(u = s |_ q \<and> v = (t \<cdot> \<mu> ^^ k1 |_ q)) \<or> (v = s |_ q \<and> u = (t \<cdot> \<mu> ^^ k1 |_ q) \<and> n1 = 0)" by auto
      from CPS[THEN spec, THEN spec, THEN spec, THEN mp[OF _ cp(2)]]
      obtain p' n' where P: "?P u v n2 p' n' p n" by auto
      then have "n' < n" by auto
      then have  "\<exists> k. k > 0 \<and> n = n' + k" by presburger
      then obtain k where k: "k > 0" and n: "n = n' + k" by auto
      from P have "p' \<le>\<^sub>p p" by auto
      then obtain q' where pp': "p = p' @ q'" unfolding less_eq_pos_def by auto
      let ?\<sigma> = "\<mu> ^^ k"
      let ?p = "q' @ q"
      from P have p': "p' \<in> poss (S \<cdot> \<mu> ^^ n')" "p' \<in> poss (T \<cdot> \<mu> ^^ n')" by simp_all
      have p'1: "p' \<in> poss (S \<cdot> \<mu> ^^ n' \<cdot> ?\<sigma>)" using poss_imp_subst_poss[OF p'(1)] .
      have p'2: "p' \<in> poss (T \<cdot> \<mu> ^^ n' \<cdot> ?\<sigma>)" using poss_imp_subst_poss[OF p'(2)] .
      from P have uv': "(u,v \<cdot> \<mu> ^^ n2) \<in> {((S \<cdot> \<mu> ^^ n' |_ p'), T \<cdot> \<mu> ^^ n' |_ p')}\<^sup>\<leftrightarrow>" by auto
      then have "(u \<cdot> ?\<sigma> |_ ?p, v \<cdot> \<mu> ^^ n2 \<cdot> ?\<sigma> |_ ?p) \<in> {((S \<cdot> \<mu> ^^ n' |_ p' \<cdot> ?\<sigma>) |_ ?p, (T \<cdot> \<mu> ^^ n' |_ p' \<cdot> ?\<sigma>) |_ ?p)}\<^sup>\<leftrightarrow>" 
        (is "?pair \<in> ?set")
        by auto 
      have "?set = {(S \<cdot> \<mu> ^^ n' \<cdot> ?\<sigma> |_ (p' @ ?p), T \<cdot> \<mu> ^^ n' \<cdot> ?\<sigma> |_ (p' @ ?p))}\<^sup>\<leftrightarrow>"
        unfolding subt_at_subst[OF p'(1), symmetric] subt_at_subst[OF p'(2), symmetric]
        unfolding subt_at_append[OF p'1] subt_at_append[OF p'2] ..
      also have "... = {(S \<cdot> \<mu> ^^ n |_ (p' @ ?p), T \<cdot> \<mu> ^^ n |_ (p' @ ?p))}\<^sup>\<leftrightarrow>"
        unfolding n subst_power_compose_distrib by simp
      also have "... = {(S \<cdot> \<mu> ^^ n |_ (p @ q), T \<cdot> \<mu> ^^ n |_ (p @ q))}\<^sup>\<leftrightarrow>" unfolding pp' by simp
      also have "... = {(S \<cdot> \<mu> ^^ n |_ p |_ q, T \<cdot> \<mu> ^^ n |_ p |_ q)}\<^sup>\<leftrightarrow>" 
        unfolding subt_at_append[OF p(1)]  subt_at_append[OF p(2)] ..
      also have "... = {(u,v \<cdot> \<mu> ^^ n1)}\<^sup>\<leftrightarrow>" using uv 
        st[unfolded n1 add.commute[of n1] subst_power_compose_distrib subst_subst]  
        by (auto simp: subt_at_subst[OF q(2)])
      finally have mem: "?pair \<in> {(u,v \<cdot> \<mu> ^^ n1)}\<^sup>\<leftrightarrow>" using \<open>?pair \<in> ?set\<close> by simp
      obtain pp \<sigma> v' where pp: "pp = ?p" and \<sigma>: "\<sigma> = ?\<sigma>" and v': "v' = v \<cdot> \<mu> ^^ n2" by auto
      from mem have mem: "(u \<cdot> \<sigma> |_ pp, v' \<cdot> \<sigma> |_ pp) \<in> {(u,v \<cdot> \<mu> ^^ n1)}\<^sup>\<leftrightarrow>" unfolding pp \<sigma> v' by auto
      (* now consider positions *)
      have "(pp \<in> poss (u \<cdot> \<sigma>) \<inter> poss (v' \<cdot> \<sigma>)) = (pp \<in> poss (S \<cdot> \<mu> ^^ n' \<cdot> \<sigma> |_p') \<inter> poss (T \<cdot> \<mu> ^^ n' \<cdot> \<sigma> |_ p'))" unfolding subt_at_subst[OF p'(1)] subt_at_subst[OF p'(2)] pp \<sigma> v' 
        using  uv' by auto
      also have "... = (pp \<in> poss (S \<cdot> \<mu> ^^ n |_ p') \<inter> poss (T \<cdot> \<mu> ^^ n |_ p'))" unfolding n subst_power_compose_distrib  \<sigma> by simp
      also have "..."
      proof -
        have "S \<cdot> \<mu> ^^ n |_ (p' @ q') = S \<cdot> \<mu> ^^ n |_ p' |_ q'" "T \<cdot> \<mu> ^^ n |_ p' |_ q' = T \<cdot> \<mu> ^^ n |_ (p' @ q')" unfolding 
          subt_at_append[OF p(1)[unfolded pp' poss_append_poss, THEN conjunct1]]
          subt_at_append[OF p(2)[unfolded pp' poss_append_poss, THEN conjunct1]] by auto
        then have one: "q \<in> poss (S \<cdot> \<mu> ^^ n |_ p' |_ q')" "q \<in> poss (T \<cdot> \<mu> ^^ n |_ p' |_ q')" using q st 
          unfolding pp' n1 add.commute[of n1] subst_power_compose_distrib by auto
        show ?thesis using 
          pos_append_poss[OF p(1)[unfolded pp' poss_append_poss, THEN conjunct2] one(1)] 
          pos_append_poss[OF p(2)[unfolded pp' poss_append_poss, THEN conjunct2] one(2)] unfolding pp
          by auto
      qed
      finally have pos: "pp \<in> poss (u \<cdot> \<sigma>)" "pp \<in> poss (v' \<cdot> \<sigma>)" by auto
      have False
      proof (cases "n1 = n2")
        case True
        let ?\<tau> = "\<sigma> \<circ>\<^sub>s \<sigma>" let ?q = "pp @ pp" 
        from mem[unfolded True v'[symmetric]]
        have "(u \<cdot> \<sigma> |_ pp) = u \<and> (v' \<cdot> \<sigma> |_ pp) = v' \<or> (u \<cdot> \<sigma> |_ pp) = v' \<and> (v' \<cdot> \<sigma> |_ pp) = u" by auto
        then have "(u \<cdot> ?\<tau> |_ ?q) = u \<and> (v' \<cdot> ?\<tau> |_ ?q) = v' \<and> ?q \<in> poss (u \<cdot> ?\<tau>) \<and> ?q \<in> poss (v' \<cdot> ?\<tau>)"
        proof
          assume "(u \<cdot> \<sigma> |_ pp) = u \<and> (v' \<cdot> \<sigma> |_ pp) = v'"
          then have id: "(u \<cdot> \<sigma> |_ pp) = u" "(v' \<cdot> \<sigma> |_ pp) = v'" by auto
          note it = arg_cong[where f = "\<lambda> t. t \<cdot> \<sigma> |_ pp"]
          show ?thesis
            unfolding poss_append_poss
            unfolding subst_subst_compose
            unfolding subt_at_append[OF poss_imp_subst_poss[OF pos(1)]] subt_at_subst[OF pos(1)]
            unfolding subt_at_append[OF poss_imp_subst_poss[OF pos(2)]] subt_at_subst[OF pos(2)]
            unfolding it[OF id(1)] it[OF id(2)] 
            unfolding id 
            using pos by auto
        next
          assume "(u \<cdot> \<sigma> |_ pp) = v' \<and> (v' \<cdot> \<sigma> |_ pp) = u"
          then have id: "(u \<cdot> \<sigma> |_ pp) = v'" "(v' \<cdot> \<sigma> |_ pp) = u" by auto
          note it = arg_cong[where f = "\<lambda> t. t \<cdot> \<sigma> |_ pp"]
          show ?thesis
            unfolding poss_append_poss
            unfolding subst_subst_compose
            unfolding subt_at_append[OF poss_imp_subst_poss[OF pos(1)]] subt_at_subst[OF pos(1)]
            unfolding subt_at_append[OF poss_imp_subst_poss[OF pos(2)]] subt_at_subst[OF pos(2)]
            unfolding it[OF id(1)] it[OF id(2)] 
            unfolding id 
            using pos by auto
        qed
        then have urec: "u \<cdot> ?\<tau> |_ ?q = u" and upos: "?q \<in> poss (u \<cdot> ?\<tau>)" and
              vrec: "v' \<cdot> ?\<tau> |_ ?q = v'" and vpos: "?q \<in> poss (v' \<cdot> ?\<tau>)" by auto
        note uiter = iterate_term[OF urec upos, THEN conjunct1, unfolded subst_pow_mult]
        note viter = iterate_term[OF vrec vpos, THEN conjunct1, unfolded subst_pow_mult]
        let ?it = "\<lambda> u n :: nat. u \<cdot> \<mu> ^^ ((k + k) * n) |_ ?q ^ n"
        from eroot var have "u \<noteq> v'" unfolding v' True by (cases v, auto)
        then have neq: "\<And> n. ?it u n \<noteq> ?it v' n" using uiter viter unfolding \<sigma> subst_power_compose_distrib[symmetric] 
          unfolding subst_pow_mult by auto
        from sol_cps[OF cp(2)] have "?sol u v n2 M" by simp
        then have "?sol u v' 0 M" unfolding v' by simp
        from arg_cong[OF this, of "\<lambda> s. s \<cdot> \<mu> ^^ ((k + k - 1)* M)"] 
        have "?sol u v' 0 (M + ( k + k - 1) * M)" unfolding subst_power_compose_distrib by simp
        with k have "?sol u v' 0 ((k + k) * M)" by (cases k, auto)
        with neq[of M] show False by auto
      next
        case False
        then have "n1 > 0 \<or> n2 > 0" by auto        
        with P var have nvar: "is_Fun v" by auto
        with cp(1) c1 obtain x where u: "u = Var x" by (cases u, simp, cases v, auto)
        from arg_cong[OF sol_cps[OF cp(2)], of "\<lambda> t. t \<cdot> \<mu>^^n1"] 
          arg_cong[OF cps[OF cp(1)], of "\<lambda> t. t \<cdot> \<mu> ^^ n2"] 
        have id: "u \<cdot> \<mu> ^^ (M + n2) = u \<cdot> \<mu> ^^ (M + n1)" 
          unfolding subst_subst subst_power_compose_distrib[symmetric] 
          by (simp add: ac_simps)
        let ?n1 = "min n1 n2" let ?n2 = "max n1 n2 - ?n1"
        have id: "u \<cdot> \<mu> ^^ (M + ?n1) \<cdot> \<mu> ^^ ?n2 = u \<cdot> \<mu> ^^ (M + ?n1) \<and> ?n2 > 0" (is "?id \<and> _")
        proof (cases "n1 < n2")
          case True
          then have id1: "?n1 = n1" and id2: "?n2 = n2 - n1" by auto
          show ?thesis using id unfolding id2 unfolding id1 using True
            unfolding subst_subst subst_power_compose_distrib[symmetric] by simp
        next
          case False with \<open>n1 \<noteq> n2\<close> 
          have True: "n2 < n1" by simp
          then have id1: "?n1 = n2" and id2: "?n2 = n1 - n2" by auto
          show ?thesis using id unfolding id2 unfolding id1 using True
            unfolding subst_subst subst_power_compose_distrib[symmetric] by simp
        qed          
        then have ?id "?n2 > 0" by auto
        then obtain n3 where n3: "?n2 = Suc n3" by (cases ?n2, auto)
        from iterate_term[of _ _ "[]", simplified, OF \<open>?id\<close>]
        have id: "\<And> k. u \<cdot> \<mu> ^^ (M + ?n1 + k + n3 * k) = u \<cdot> \<mu> ^^ (M + ?n1)" unfolding n3
          unfolding subst_pow_mult subst_subst subst_power_compose_distrib[symmetric] 
          by (simp add: ac_simps)
        from mem
        have "(u \<cdot> \<sigma> |_ pp) = u \<and> (v' \<cdot> \<sigma> |_ pp) = v \<cdot> \<mu> ^^ n1 \<or> (u \<cdot> \<sigma> |_ pp) = v \<cdot> \<mu> ^^ n1 \<and> (v' \<cdot> \<sigma> |_ pp) = u" 
          (is "?one \<or> ?two") by auto
        then have "\<exists> i j. u \<cdot> \<mu> ^^ i \<rhd> u \<cdot> \<mu> ^^ j"
        proof
          assume ?two
          then have v\<sigma>: "v' \<cdot> \<sigma> |_ pp = u" "u \<cdot> \<sigma> |_ pp = v \<cdot> \<mu> ^^ n1" by auto
          from nvar have nvar: "is_Fun (v' \<cdot> \<sigma>)" unfolding v' by auto
          from subt_at_imp_supteq[OF pos(2)] have "v' \<cdot> \<sigma> \<unrhd> u" unfolding v\<sigma> .
          moreover have "v' \<cdot> \<sigma> \<noteq> u" unfolding u using nvar by auto
          ultimately have supt: "v' \<cdot> \<sigma> \<rhd> u" by auto
          from supt_subst[OF supt] have supt: "v' \<cdot> \<sigma> \<cdot> \<mu> ^^ n1 \<rhd> u \<cdot> \<mu> ^^ n1" .
          from subt_at_imp_supteq[OF pos(1)] have supteq: "u \<cdot> \<sigma> \<unrhd> v \<cdot> \<mu> ^^ n1" unfolding v\<sigma> .
          from supteq_subst[OF supteq, of "\<sigma> \<circ>\<^sub>s \<mu> ^^ n2"] have supteq: "u \<cdot> \<sigma> \<cdot> \<sigma> \<cdot> \<mu> ^^ n2 \<unrhd> v' \<cdot> \<sigma> \<cdot> \<mu> ^^ n1"
            unfolding v' \<sigma> subst_subst subst_power_compose_distrib[symmetric]
            by (simp add: ac_simps)
          from supteq_supt_trans[OF supteq supt] show ?thesis 
            unfolding \<sigma> subst_subst subst_power_compose_distrib[symmetric]
            by blast
        next
          assume ?one
          then have v\<sigma>: "v' \<cdot> \<sigma> |_ pp = v \<cdot> \<mu> ^^ n1" "u \<cdot> \<sigma> |_ pp = u" by auto
          from subt_at_imp_supteq[OF pos(1)] have "u \<cdot> \<sigma> \<unrhd> u" unfolding v\<sigma> by auto
          moreover have "u \<cdot> \<sigma> \<noteq> u" 
          proof
            assume "u \<cdot> \<sigma> = u" 
            then have "u \<cdot> \<sigma> |_ [] = u" by auto
            from iterate_term[OF this, simplified] have "u \<cdot> \<mu> ^^ (k * M) = u" unfolding \<sigma> subst_pow_mult by auto
            then have "u \<cdot> \<mu> ^^ (M + (k - 1) * M) = u" using k by (cases k, auto)
            from this[unfolded subst_power_compose_distrib subst_subst_compose cps[OF cp(1)]]
            show False unfolding u using nvar by auto
          qed
          ultimately have supt: "u \<cdot> \<sigma> \<rhd> u \<cdot> \<mu> ^^ 0" by auto
          then show ?thesis unfolding \<sigma> by blast
        qed
        then obtain i j where supt: "u \<cdot> \<mu> ^^ i \<rhd> u \<cdot> \<mu> ^^ j" by auto
        {
          fix k n
          from supt_subst[OF supt]
          have supt: "u \<cdot> \<mu> ^^ (i + k) \<rhd> u \<cdot> \<mu> ^^ (j + k)" 
            unfolding subst_power_compose_distrib by auto
          from supt_size[OF supt] have gt: "size (u \<cdot> \<mu> ^^ (i + k)) > size (u \<cdot> \<mu> ^^ (j + k))" by auto
          with size_subst[of "u \<cdot> \<mu> ^^ (i + k)" "\<mu> ^^ n"]
          have "size (u \<cdot> \<mu> ^^ (i + k) \<cdot> \<mu> ^^ n) > size (u \<cdot> \<mu> ^^ (j + k))" by simp
          then have "size (u \<cdot> \<mu> ^^ (i + k + n)) > size (u \<cdot> \<mu> ^^ (j + k))" 
            unfolding  subst_power_compose_distrib by auto
          then have "u \<cdot> \<mu> ^^ (i + k + n) \<noteq> u \<cdot> \<mu> ^^ (j + k)" by auto
        } note neq = this
        from arg_cong[OF id[of i], of "\<lambda> t. t \<cdot> \<mu> ^^ j"] neq[of "M + min n1 n2" "j + n3 * i"]
        show False 
          unfolding \<sigma> subst_subst subst_power_compose_distrib[symmetric]
          by (simp add: field_simps)
      qed
    }
    then have c5: "?c5 = False" by auto
    note simp = simp[unfolded c5]  
    let ?recsM = "mapM (\<lambda>(u,v,m). ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m)) (conflicts (s,t,N))"
    let ?res = "?recsM \<bind> (\<lambda> is. Some (max_list (map (\<lambda> i. Suc i) is)))"
    from simp
    have id: "ident_solve' cps (s,t,N) = ?res"
      by simp
    {
      fix u v m
      assume mem: "(u,v,m) \<in> ?cp"
      from conflicts[OF mem] obtain p' k where N: "N = m + k" and var: "is_Var v \<longrightarrow> m = 0" and eroot: "eroot u \<noteq> eroot v" and p': "p' \<in> poss s" "p' \<in> poss (t \<cdot> \<mu> ^^ k)" and uv: 
        "u = s |_ p' \<and> v = t \<cdot> \<mu> ^^ k |_ p' \<or> v = s |_ p' \<and> u = t \<cdot> \<mu> ^^ k |_ p' \<and> m = 0" (is "?one \<or> ?two") by blast
      from c1 c5 have cs: "\<not> ?c1" "\<not> ?c5" by simp_all
      note poss = poss_imp_subst_poss[of _ _ \<mu>]
      from poss[OF p(1)] poss[OF p(2)] have pp: "p \<in> poss (S \<cdot> \<mu> ^^ Suc n)" "p \<in> poss (T \<cdot> \<mu> ^^ Suc n)"
        unfolding subst_power_Suc by simp_all
      note pp' =  poss[OF p'(1)] poss[OF p'(2)]  
      have "(S \<cdot> \<mu> ^^ Suc n |_ p, T \<cdot> \<mu> ^^ Suc n |_ p) \<in> {(s \<cdot> \<mu>, t \<cdot> \<mu> ^^ (m + k) \<cdot> \<mu>), (t \<cdot> \<mu> ^^ (m + k) \<cdot> \<mu>, s \<cdot> \<mu>)}" unfolding subst_power_Suc  
        using st unfolding N by (auto simp: subt_at_subst[OF p(1)] subt_at_subst[OF p(2)])
      then have "(S \<cdot> \<mu> ^^ Suc n |_ p, T \<cdot> \<mu> ^^ Suc n |_ p) \<in> {(s \<cdot> \<mu>, t \<cdot> \<mu> ^^ k \<cdot> \<mu> ^^ Suc m), (t \<cdot> \<mu> ^^ k \<cdot> \<mu> ^^ Suc m, s \<cdot> \<mu>)}" (is "(?S,?T) \<in> {(?s,?t),(?t,?s)}")
        unfolding add.commute[of m] subst_power_compose_distrib subst_power_Suc by simp
      then have ST: "?S = ?s \<and> ?T = ?t \<or> ?S = ?t \<and> ?T = ?s" (is "?one' \<or> ?two'") by auto
      let ?S' = "S \<cdot> \<mu> ^^ Suc n |_ (p @ p')"
      let ?T' = "T \<cdot> \<mu> ^^ Suc n |_ (p @ p')"
      have pp'S: "p @ p' \<in> poss (S \<cdot> \<mu> ^^ (Suc n))" 
        by (rule pos_append_poss[OF pp(1)], insert ST p', auto)
      have pp'T: "p @ p' \<in> poss (T \<cdot> \<mu> ^^ (Suc n))" 
        by (rule pos_append_poss[OF pp(2)], insert ST p', auto)
      from imageI[OF st, of "\<lambda>(s,t). (s \<cdot> \<mu> |_ p', t \<cdot> \<mu> |_ p')", unfolded split] 
      have "(?S', ?T') \<in> {(s \<cdot> \<mu> |_ p', t \<cdot> \<mu> ^^ N \<cdot> \<mu> |_ p'), (t \<cdot> \<mu> ^^ N \<cdot> \<mu> |_ p', s \<cdot> \<mu> |_ p')}" (is "_ \<in> ?l")
        unfolding image_insert split
        unfolding subt_at_subst[OF p(1), symmetric] subt_at_subst[OF p(2), symmetric] 
        unfolding subst_power_Suc[symmetric] subst_subst
        unfolding subt_at_append[OF pp(1)] subt_at_append[OF pp(2)] by auto 
      moreover have "?l = {(u \<cdot> \<mu>, v \<cdot> \<mu> ^^ Suc m), (v \<cdot> \<mu> ^^ Suc m, u \<cdot> \<mu>)}"
        using uv unfolding N unfolding subt_at_subst[OF p'(1)]
        unfolding add.commute[of m] subst_power_compose_distrib subst_subst_compose
        unfolding subst_subst[of _ _ \<mu>] subst_power_Suc[symmetric]
        unfolding subt_at_subst[OF p'(2)] by auto
      ultimately
      have S'T': "(?S',?T') \<in> {(u \<cdot> \<mu>, v \<cdot> \<mu> ^^ Suc m), (v \<cdot> \<mu> ^^ Suc m, u \<cdot> \<mu>)}" by simp
      have "ident_solve' (insert (u,v,m) cps) (u \<cdot> \<mu>, v, Suc m) \<noteq> None"
      proof (rule 1[OF refl cs mem refl refl, THEN spec, THEN spec, THEN mp, THEN mp, THEN mp, THEN mp],
        rule pp'S, rule pp'T, rule S'T', intro allI impI)
        fix u' v' m'
        assume "(u',v',m') \<in> insert (u,v,m) cps"
        then show "?Q u' v' m' (p @ p') (Suc n)"
        proof
          assume "(u',v',m') = (u,v,m)"
          then have uv': "u' = u" "v' = v" "m' = m" by auto
          show ?thesis unfolding uv'
          proof (intro exI conjI)
            show "p @ p' \<in> poss (S \<cdot> \<mu> ^^ n)"
              by (rule pos_append_poss[OF p(1)], insert st p', unfold N add.commute[of m] 
                subst_power_compose_distrib, auto)
          next
            show "p @ p' \<in> poss (T \<cdot> \<mu> ^^ n)"
              by (rule pos_append_poss[OF p(2)], insert st p', unfold N add.commute[of m] 
                subst_power_compose_distrib, auto)
          next
            show "(S \<cdot> \<mu> ^^ n |_ (p @ p'), T \<cdot> \<mu> ^^ n |_ (p @ p')) \<in> {(u,v \<cdot> \<mu> ^^ m), (v \<cdot> \<mu> ^^ m, u)}"
              using uv st unfolding subt_at_append[OF p(1)] subt_at_append[OF p(2)] N add.commute[of m] 
              subst_power_compose_distrib subst_subst 
              by (auto simp: subt_at_subst[OF p'(2)])
          qed (insert eroot var, auto)
        next
          assume "(u',v',m') \<in> cps"
          from CPS[THEN spec, THEN spec, THEN spec, THEN mp[OF _ this]]            
          obtain p'' n' where P: "?P u' v' m' p'' n' p n" by auto
          then have "p'' \<le>\<^sub>p p" by simp
          also have "... \<le>\<^sub>p p @ p'" unfolding less_eq_pos_def by blast
          finally have "?P u' v' m' p'' n' (p @ p') (Suc n)" using P by auto
          then show ?thesis by blast
        qed
      qed
    } note ind = this
    then have "?recsM \<noteq> None" unfolding mapM_None by auto
    then show "ident_solve' cps (s,t,N) \<noteq> None" unfolding simp by (simp split: bind_splits)
  qed
qed

declare ident_solve'.simps[simp del]

lemma ident_solve: 
  "ident_solve st = Some i \<Longrightarrow> ident_solution st i"
  "ident_solve st = None \<Longrightarrow> \<not>(\<exists>i. ident_solution st i)"
proof -
  assume sol: "ident_solve st = Some i"
  obtain s t where st: "st = (s,t)" by force
  from ident_solve'_sound[THEN mp[OF _ sol[unfolded st ident_solve_def split]]] show "ident_solution st i"
    unfolding ident_solution_def nident_solution_def st by auto
next
  assume non: "ident_solve st = None"
  obtain s t where st: "st = (s,t)" by force
  from non[unfolded ident_solve_def st split]
    ident_solve'_complete[of s t _ s t 0 "{}", THEN spec[of _ "[]"], THEN spec[of _ 0]]
  show "\<not> (\<exists> i. ident_solution st i)" unfolding st by auto
qed

lemma identity_problem_explicit_bound: fixes s t :: "('f,'v)term"
  defines ct: "ct \<equiv> conflict_terms s t"
  defines vct: "vct \<equiv> ct \<inter> {Var x | x. True}"
  defines n: "n \<equiv> card (vct \<times> ct)"
  shows "(\<exists> i. s \<cdot> \<mu>^^i = t \<cdot> \<mu>^^i) = (s \<cdot> \<mu>^^ n = t \<cdot> \<mu> ^^ n)" (is "?ex = ?n")
proof
  assume ?ex 
  with ident_solve(2)[of "(s,t)", unfolded ident_solution_def split]
  obtain i where sol: "ident_solve (s,t) = Some i" by (cases "ident_solve (s,t)", auto)
  with ident_solve'_bound[of s t i] have i: "i \<le> n" 
    unfolding ident_solve_def split n vct ct by simp
  then have "n = i + (n - i)" by simp
  then obtain k where n: "n = i + k" by auto
  from ident_solve(1)[OF sol, unfolded ident_solution_def split]
  have "s \<cdot> \<mu> ^^ i = t \<cdot> \<mu> ^^ i" .
  from arg_cong[OF this, of "\<lambda> t. t \<cdot> \<mu> ^^ k"] show ?n unfolding n
    unfolding subst_power_compose_distrib by simp
qed blast
end

end

