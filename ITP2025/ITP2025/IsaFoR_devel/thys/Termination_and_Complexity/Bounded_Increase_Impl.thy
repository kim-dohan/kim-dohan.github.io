(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Bounded_Increase_Impl
imports 
  Ord.Non_Inf_Order_Impl
  CR.Orthogonality_Impl
  Bounded_Increase 
  Dependency_Graph_Impl
  Innermost_Usable_Rules_Impl
  Generalized_Usable_Rules_Impl
begin

hide_const Fresh.fresh

text \<open>this theory contains executable function which checks whether the rules of the
  induction calculus have been correctly applied\<close>

section \<open>checking equivalence and subsumption of constraints\<close>

text \<open>replace [] \<longrightarrow> \<phi> by \<phi>\<close>
fun deep_normalize_cc' :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "deep_normalize_cc' (CC_impl [] c) = deep_normalize_cc' c"
| "deep_normalize_cc' (CC_impl cs c) = CC_impl (map deep_normalize_cc' cs) (deep_normalize_cc' c)"
| "deep_normalize_cc' (CC_cond s c) = (CC_cond s c)"
| "deep_normalize_cc' (CC_all s c) = (CC_all s (deep_normalize_cc' c))"
| "deep_normalize_cc' (CC_rewr s c) = (CC_rewr s c)"

text \<open>replace [] \<longrightarrow> \<phi> by \<phi> and unique names for bound variables\<close>
definition deep_normalize_cc :: "('v list \<Rightarrow> 'v) \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "deep_normalize_cc fresh c \<equiv> fresh.normalize_alpha fresh (deep_normalize_cc' c)"

lemma (in fixed_trs_dep_order_fresh) deep_normalize_cc: "\<sigma> \<Turnstile> deep_normalize_cc fresh c = \<sigma> \<Turnstile> c"
  unfolding deep_normalize_cc_def normalize_alpha
  by (induct c arbitrary: \<sigma> rule: deep_normalize_cc'.induct, auto)

text \<open>basic subsumption test which checks for less hypothesis in implications\<close>
function(sequential) check_subsumes' :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> bool" where
  "check_subsumes' (CC_impl cs c) (CC_impl ds d) = (check_subsumes' c d \<and> (\<forall> c \<in> set cs. \<exists> d \<in> set ds. check_subsumes' d c))"
| "check_subsumes' c (CC_impl ds d) = check_subsumes' c d"
| "check_subsumes' (CC_all x c) (CC_all y d) = (x = y \<and> check_subsumes' c d)"
| "check_subsumes' c d = (c = d)"
  by pat_completeness auto

termination
proof 
  fix x y c d :: "('f,'v)cond_constraint" and ds cs :: "('f,'v)cond_constraint list"
  assume x: "x \<in> set ds" and y: "y \<in> set cs" 
  from size_simps(1)[OF x] size_simps(1)[OF y]
  show "((x, y), CC_impl cs c, CC_impl ds d) \<in> measure (\<lambda> (x,y). size x + size y)"
    by auto
qed auto

lemma (in fixed_trs_dep_order_fresh) check_subsumes': assumes "check_subsumes' c d"
  shows "c \<longrightarrow>cc d"
proof 
  fix \<sigma>
  assume "\<sigma> \<Turnstile> c"
  with assms show "\<sigma> \<Turnstile> d"
  proof (induct c d arbitrary: \<sigma> rule: check_subsumes'.induct)
    case (1 cs c ds d \<sigma>)
    show ?case unfolding cc_models.simps
    proof
      assume ds: "Ball (set ds) ((\<Turnstile>) \<sigma>)"
      from 1(3) have subs: "check_subsumes' c d" by auto
      have "Ball (set cs) ((\<Turnstile>) \<sigma>)"
      proof
        fix c
        assume c: "c \<in> set cs"
        with 1(3) obtain d where "d \<in> set ds" and "check_subsumes' d c" by auto
        with 1(2)[OF c this] ds show "\<sigma> \<Turnstile> c" by auto
      qed
      with 1(4) have "\<sigma> \<Turnstile> c" by simp
      from 1(1)[OF subs this] show "\<sigma> \<Turnstile> d" .
    qed
  qed auto
qed

(* text main subsumption test: it uses check_subsumes' after normalization *)
definition check_subsumes :: "('v list \<Rightarrow> 'v) \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> bool" where
  "check_subsumes fresh c d \<equiv> let n = deep_normalize_cc fresh
    in check_subsumes' (n c) (n d)"

lemma (in fixed_trs_dep_order_fresh) check_subsumes: assumes "check_subsumes fresh c d"
  shows "c \<longrightarrow>cc d"
proof -
  from check_subsumes'[OF assms[unfolded check_subsumes_def Let_def]]
  have deep: "deep_normalize_cc fresh c \<longrightarrow>cc deep_normalize_cc fresh d" .
  show ?thesis
  proof
    fix \<sigma>
    assume model: "\<sigma> \<Turnstile> c"
    show "\<sigma> \<Turnstile> d" using cc_implies_substE[OF deep, unfolded deep_normalize_cc, OF model] .
  qed
qed  

section \<open>executable versions of previously defined functions\<close>

definition initial_conditions_gen_impl where
  "initial_conditions_gen_impl p bef_len aft_len P st \<equiv>
  let pairs = \<lambda>n. generate_lists n P; all = [bef @ st # aft. bef <- pairs bef_len, aft <- pairs aft_len]
  in filter (\<lambda> bef_st_aft. \<forall>i<bef_len + aft_len. p (bef_st_aft ! i) (bef_st_aft ! Suc i)) all"

lemma initial_conditions_gen_impl[simp]: "set (initial_conditions_gen_impl p bef aft P st) = 
  initial_conditions_gen p bef aft (set P) st" 
  unfolding initial_conditions_gen_def initial_conditions_gen_impl_def Let_def by auto

abbreviation fresh_xx where "fresh_xx \<equiv> fresh_string ''xx''" (* fix prefix of fresh variables to xx *)

text \<open>instead of real dependency graph (DG) in constraint_present / initial_conditions, 
  here we use some estimation (iedg = innermost estimated dependency graph)\<close>
definition check_constraint_present :: "('dpp,'f :: {showl, compare_order},string)dpp_ops \<Rightarrow> 'dpp \<Rightarrow>
  'f \<Rightarrow> ('f,string)rules \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
  (('f,string)cond_constraint \<times> ('f,string)rules) list \<Rightarrow>
  (condition_type \<Rightarrow> ('f,string)rule \<Rightarrow> showsl check)" where
  "check_constraint_present I dpp constant p bef aft ccs \<equiv> let
    edg = is_iedg_edge_dpp I dpp;
    init_conds = initial_conditions_gen_impl (\<lambda> st uv. edg st (fst uv)) bef aft p
  in (\<lambda> ct st. check_allm (\<lambda> sts. check (\<exists> (c,uvs) \<in> set ccs. disjoint_variant sts uvs \<and> check_subsumes fresh_xx c (constraint_of constant ct uvs bef)) 
    (showsl_lit (STR ''did not find '') \<circ> 
     showsl_lit (case ct of Bound \<Rightarrow> STR ''bound'' | Strict \<Rightarrow> STR ''strict'' | Non_Strict \<Rightarrow> STR ''non-strict'') \<circ> 
     showsl_lit (STR '' constraint for sequence '') \<circ> showsl_rules sts)) (init_conds st))"

text \<open>pretty printer for constraints, to display error messages\<close>
fun showsl_cc_aux :: "bool \<Rightarrow> ('f :: showl, 'v :: showl)cond_constraint \<Rightarrow> showsl" where
  "showsl_cc_aux b (CC_rewr s t) = (showsl s \<circ> showsl_lit (STR '' = '') \<circ> showsl t)"
| "showsl_cc_aux b (CC_cond stri (s,t)) = (showsl s \<circ> showsl_lit (if stri then STR '' > '' else STR '' >= '') \<circ> showsl t)"
| "showsl_cc_aux b (CC_all x c) = (let s = showsl_lit (STR ''ALL '') \<circ> showsl x \<circ> showsl_lit (STR ''. '') \<circ> showsl_cc_aux False c
    in (if b then showsl_lit (STR ''('') \<circ> s \<circ> showsl_lit (STR '')'') else s))"
| "showsl_cc_aux b (CC_impl cs c2) = (showsl_lit (STR ''('') \<circ> 
    showsl_list_gen id (STR ''True'') (STR '''') (STR '' and '') (STR '''') (map (\<lambda> c. showsl_cc_aux True c) cs) \<circ> showsl_lit (STR '' => '') \<circ> showsl_cc_aux True c2 \<circ> showsl_lit (STR '')''))"

definition showsl_cc :: "('f :: showl, 'v :: showl)cond_constraint \<Rightarrow> showsl" where
  "showsl_cc \<equiv> showsl_cc_aux False"

text \<open>Simplification proofs for conditional constraints, intermediate constraints 
  have to be provided for early error detection\<close>
datatype ('f,'v)cond_constraint_prf = 
  Final 
| Delete_Condition "('f,'v)cond_constraint" "('f,'v)cond_constraint_prf"
  (* new constraint and proof *)
| Different_Constructor "('f,'v)cond_constraint"
  (* the rewrite condition where there is a different constructor *)
| Same_Constructor "('f,'v)cond_constraint" "('f,'v)cond_constraint" "('f,'v)cond_constraint_prf"
  (* the rewrite condition where there is the same constructor + new total constraint + proof *)
| Variable_Equation 'v "('f,'v)term" "('f,'v)cond_constraint" "('f,'v)cond_constraint_prf"
  (* the subst. x / t + new total constraint + proof *)
| Funarg_Into_Var "('f,'v)cond_constraint" nat 'v "('f,'v)cond_constraint" "('f,'v)cond_constraint_prf"
  (* the rewrite condition + the index of the arg. + name of fresh var + new total constraint + proof *)
| Simplify_Condition "('f,'v)cond_constraint" "('f,'v)substL" "('f,'v)cond_constraint" "('f,'v)cond_constraint_prf"
  (* the quantified subformula + sigma + new total constraint + proof *)
| Induction "('f,'v)cond_constraint" "('f,'v)cond_constraint list" "(('f,'v)rule \<times> (('f,'v)term \<times> 'v list) list \<times> ('f,'v)cond_constraint \<times> ('f,'v)cond_constraint_prf) list"
  (* the rewrite condition + the conjunction that is used for induction + (renamed rule, subterm + ys - list, new constraint for rule, proof *)

lemma
  fixes P :: "('f, 'v) cond_constraint_prf \<Rightarrow> bool"
  assumes "P Final" and
  "\<And> c p. P p \<Longrightarrow> P (Delete_Condition c p)" and 
  "\<And> c. P(Different_Constructor c)" and 
  "\<And> c1 c2 p. P p \<Longrightarrow> P(Same_Constructor c1 c2 p)" and 
  "\<And> x t c p. P p \<Longrightarrow> P(Variable_Equation x t c p)" and 
  "\<And> c1 i x c2 p. P p \<Longrightarrow> P(Funarg_Into_Var c1 i x c2 p)" and 
  "\<And> c1 \<sigma> c2 p. P p \<Longrightarrow> P(Simplify_Condition c1 \<sigma> c2 p)" and 
  "\<And> c cs ics. (\<And> lr rs_ys c p. (lr,rs_ys,c,p) \<in> set ics \<Longrightarrow> P p) \<Longrightarrow> P(Induction c cs ics)"
shows cond_constraint_prf_induct[case_names
    Final Delete_Condition
    Different_Constructor
    Same_Constructor
    Variable_Equation
    Funarg_Into_Var
    Simplify_Condition
    Induction, induct type: cond_constraint_prf]:
    "P c"
proof (induct c)
  case (Induction)
  show ?case 
    by (rule assms(8), rule Induction, auto simp: snds.simps)
qed (insert assms, auto)

text \<open>for checking proofs, we need some more auxiliary algorithms\<close>

text \<open>check whether induction on subterm of rhs is possible, and whether provided variables are 
  indeed disjoint to the existing ones\<close>
definition check_rys where 
  "check_rys D rt r rys \<equiv> case rys of (r',ys) \<Rightarrow> do {
               check (root r' = rt) (showsl_lit (STR ''root of '') \<circ> showsl r' \<circ> showsl_lit (STR '' is not '') \<circ> showsl (the rt));
               check (r \<unrhd> r') (showsl r' \<circ> showsl_lit (STR '' is not a subterm of '') \<circ> showsl r);
               check_allm (\<lambda> f. check (\<not> D f) (showsl_lit (STR ''the defined symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' occurs in the subterm '') \<circ> showsl r' \<circ> showsl_lit (STR '' of the rhs'')))
                 (funas_args_term_list r');
               check_disjoint ys (vars_term_list r)
                 <+? (\<lambda> y. showsl y \<circ> showsl_lit (STR '' occurs in '') \<circ> showsl r)
             }"

text \<open>extract outer quantors, required to deconstruct formula in Simplify-Condition\<close>
fun cc_unbound :: "('f,'v)cond_constraint \<Rightarrow> 'v list \<times> ('f,'v)cond_constraint" where
  "cc_unbound (CC_all x c) = (case cc_unbound c of (xs,d) \<Rightarrow> (x # xs,d))"
| "cc_unbound c = ([],c)"

lemma cc_unbound_bound: "cc_unbound c = (xs,d) \<Longrightarrow> cc_bound xs d = c"
proof (induction c arbitrary: xs d)
  case (all x c xs d)
  obtain ys e where c: "cc_unbound c = (ys,e)" by force
  with all(2) have xs: "xs = x # ys" and e: "e = d" by auto
  from all(1)[OF c[unfolded e]] have "cc_bound ys d = c" .
  then show ?case unfolding xs by auto
qed auto

text \<open>the main algorithm to check simplifications of conditional constraints.
 if successful, it returns the list of resulting constraints.
 Note, that we do subsumption checks all the time, e.g., 
 to be able to deal with duplicate premises, etc.\<close>
context 
  fixes R :: "('f :: showl,string)rules"
  and D :: "('f \<times> nat \<Rightarrow> bool)"
  and F :: "('f \<times> nat)list"
  and m_ortho :: bool
begin
function check_cc_prf :: "('f,string)cond_constraint \<Rightarrow> ('f,string)cond_constraint_prf \<Rightarrow> ('f,string)c_constraint list result" where
  "check_cc_prf cc Final = (case normalize_cc cc of 
    CC_impl [] (CC_cond stri st) \<Rightarrow> return [Unconditional_C stri st]
  | CC_impl [CC_cond stri uv] (CC_cond stri' st) \<Rightarrow> if stri = stri' then return [Conditional_C stri uv st] else
      error (showsl_lit (STR ''problem in final constraint: different relations for finalizing '') \<circ> showsl_cc cc)
  | _ \<Rightarrow> error (showsl_lit (STR ''problem in final constraint: it is neither a condition nor an implification of two conditions, but it is\<newline>'') \<circ> showsl_cc cc)
  )"
| "check_cc_prf c (Delete_Condition d prf) = do {
     \<comment> \<open>we perform subsumption check, which is at least as powerful as the original delete condition rule\<close>
     check (check_subsumes fresh_xx d c) 
       (showsl_lit (STR ''problem in delete conditions when switching from\<newline>'') \<circ> showsl_cc c \<circ> showsl_lit (STR '' to\<newline>'') \<circ> showsl_cc d);
     check_cc_prf d prf
   }"
| "check_cc_prf c (Different_Constructor d) = (case normalize_cc c of
     CC_impl cs c' \<Rightarrow> do {
       check (d \<in> set cs) (showsl_cc d \<circ> showsl_lit (STR ''\<newline>is not a premise of '') \<circ> showsl_cc c);
       (case d of
         CC_rewr (Fun f ss) (Fun g ts) \<Rightarrow> do {
           check (\<not> D (f,length ss)) (showsl f \<circ> showsl_lit (STR '' is defined''));
           check ((f,length ss) \<noteq> (g,length ts)) (showsl_lit (STR ''the root '') \<circ> showsl f \<circ> showsl_lit (STR '' is identical on both sides''));
           return []
         }
       | _ \<Rightarrow> error (showsl_cc d \<circ> showsl_lit (STR '' is not a rewrite condition of the correct shape'')))}
     <+? (\<lambda> s. showsl_lit (STR ''problem in Different Constructor with rewrite condition '') \<circ> showsl_cc d \<circ> 
      showsl_lit (STR ''\<newline>on input constraint\<newline>'') \<circ> showsl_cc c \<circ> showsl_nl \<circ> s))"
| "check_cc_prf c (Same_Constructor d c' p) = (case normalize_cc c of
     CC_impl cs con \<Rightarrow> do { do {
       check (d \<in> set cs) (showsl_cc d \<circ> showsl_lit (STR ''\<newline>is not a premise of '') \<circ> showsl_cc c);
       (case d of
         CC_rewr (Fun f ss) (Fun g ts) \<Rightarrow> do {
           check (\<not> D (f,length ss)) (showsl f \<circ> showsl_lit (STR '' is defined''));
           check ((f,length ss) = (g,length ts)) (showsl f \<circ> showsl_lit (STR '' and '') \<circ> showsl g \<circ> showsl_lit (STR '' are not identical''));
           let ds = cs @ map (\<lambda> (s,t). CC_rewr s t) (zip ss ts);
           let d' = CC_impl ds con;
           check (check_subsumes fresh_xx c' d') (showsl_lit (STR ''new constraint is '') \<circ> showsl_cc c' \<circ> showsl_lit (STR ''\<newline>but expected was '') \<circ> showsl_cc d')
         }
       | _ \<Rightarrow> error (showsl_cc d \<circ> showsl_lit (STR '' is not a rewrite condition of the correct shape'')))}
     <+? (\<lambda> s. showsl_lit (STR ''problem in Same Constructor with rewrite condition '') \<circ> showsl_cc d \<circ> 
         showsl_lit (STR ''\<newline> when switching from\<newline>'') \<circ> showsl_cc c \<circ> showsl_lit (STR '' to\<newline>'') \<circ> showsl_cc c' \<circ> showsl_nl \<circ> s);
     check_cc_prf c' p})"
| "check_cc_prf c (Variable_Equation x t d p) = (case normalize_cc c of
     CC_impl cs con \<Rightarrow> do { do {
       check (CC_rewr (Var x) t \<in> set cs \<or> CC_rewr t (Var x) \<in> set cs \<and> (\<forall> f \<in> funas_term t. \<not> D f)) 
         (showsl_lit (STR ''could not find '') \<circ> showsl_cc (CC_rewr (Var x) t) \<circ> showsl_lit (STR '' or reversed as a premise of\<newline>'') \<circ> showsl_cc c);
       let c' = fresh.cc_subst_apply fresh_xx c (Var(x := t), vars_term_list t);
       check (check_subsumes fresh_xx d c') (showsl_lit (STR ''new constraint is '') \<circ> showsl_cc d \<circ> showsl_lit (STR ''\<newline>but expected was '') \<circ> showsl_cc c')
       }
     <+? (\<lambda> s. showsl_lit (STR ''problem in Variable Equation with substitution '') \<circ> showsl x \<circ> showsl_lit (STR ''/'') \<circ> showsl t \<circ> showsl_lit (STR '' to switch from\<newline>'') 
         \<circ> showsl_cc c \<circ> showsl_lit (STR ''\<newline>to\<newline>'') \<circ> showsl_cc d \<circ> showsl_nl \<circ> s);
     check_cc_prf d p})" 
| "check_cc_prf c (Funarg_Into_Var c' i x d p) = (case normalize_cc c of
     CC_impl cs con \<Rightarrow> do { do {
       check (c' \<in> set cs) (showsl_cc c' \<circ> showsl_lit (STR ''\<newline>is not a premise of '') \<circ> showsl_cc c);
       check (x \<notin> set (vars_cc_list c)) (showsl_lit (STR ''variable '') \<circ> showsl x \<circ> showsl_lit (STR '' is not fresh''));
       (case c' of
         CC_rewr (Fun f ss) q \<Rightarrow> do {
           check (i < length ss) (showsl_lit (STR ''invalid position''));
           let (bef,p,aft) = (take i ss, ss ! i, drop (Suc i) ss);
           check_subseteq (funas_term_list p) F <+? (\<lambda> f. showsl_lit (STR ''function symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' is not allowed in argument''));
           let px = CC_rewr p (Var x);
           let fq = CC_rewr (Fun f (bef @ Var x # aft)) q;
           let ds = px # fq # cs; 
           let d' = CC_impl ds con;
           check (check_subsumes fresh_xx d d') (showsl_lit (STR ''new constraint is '') \<circ> showsl_cc d \<circ> showsl_lit (STR ''\<newline>but expected was '') \<circ> showsl_cc d')
         }
       | _ \<Rightarrow> error (showsl_cc c' \<circ> showsl_lit (STR '' is not a rewrite condition of the correct shape'')))}
     <+? (\<lambda> s. showsl_lit (STR ''problem in introducing fresh variable '') \<circ> showsl x \<circ> showsl_lit (STR '' on '') \<circ> showsl (Suc i) \<circ> showsl_lit (STR ''-th argument of lhs of '')
       \<circ> showsl_cc c' \<circ> showsl_lit (STR '' to switch from '') \<circ> 
       showsl_cc c \<circ> showsl_lit (STR ''to\<newline>'') \<circ> showsl_cc d \<circ> showsl_nl \<circ> s);
     check_cc_prf d p})"
| "check_cc_prf c (Simplify_Condition bc \<sigma> d p) = (case normalize_cc c of
     CC_impl cs \<psi> \<Rightarrow> do { do {
       check (bc \<in> set cs) (showsl_cc bc \<circ> showsl_lit (STR ''\<newline>is not a premise of '') \<circ> showsl_cc c);
       let (ys,cc) = cc_unbound bc;
       let (\<phi>',\<psi>') = (case normalize_cc cc of CC_impl \<phi>' \<psi>' \<Rightarrow> (\<phi>',\<psi>'));
       let dom_ran = mk_subst_domain \<sigma>;
       check_subseteq (map fst dom_ran) ys 
         <+? (\<lambda> y. showsl y \<circ> showsl_lit (STR '' is in the domain of sigma, but not a bound variable ''));
       check_allm (\<lambda> fn. do {
           check (\<not> D fn) (showsl_lit (STR ''symbol '') \<circ> showsl fn \<circ> showsl_lit (STR '' is not allowed in range of sigma, as it is defined''));
           check (fn \<in> set F) (showsl_lit (STR ''symbol '') \<circ> showsl fn \<circ> showsl_lit (STR '' is not allowed in range of sigma, as it is not in F''))
         }) (concat (map (\<lambda> x_t. funas_term_list (snd x_t)) dom_ran));
       let vs = remdups (concat (map (\<lambda> x_t. vars_term_list (snd x_t)) dom_ran));
       let sigma = (\<lambda> c. fresh.cc_subst_apply fresh_xx c (mk_subst Var \<sigma>, vs));
       check_allm (\<lambda> c. check (\<exists> c' \<in> set cs. check_subsumes fresh_xx c' (sigma c))
         (showsl_cc (sigma c) \<circ> showsl_lit (STR ''\<newline>is not contained as premise of the input implication''))) \<phi>';
       let d' = CC_impl (sigma \<psi>' # cs) \<psi>;
       check (check_subsumes fresh_xx d d') (showsl_lit (STR ''new constraint is '') \<circ> showsl_cc d \<circ> showsl_lit (STR ''\<newline>but expected was '') \<circ> showsl_cc d')
     }
     <+? (\<lambda> s. showsl_lit (STR ''problem in Simplify Condition with substitution '') \<circ> showsl \<sigma> \<circ> showsl_lit (STR '' on IH\<newline>'') \<circ> showsl_cc bc
      \<circ> showsl_lit (STR ''\<newline>to switch from\<newline>'') \<circ> showsl_cc c \<circ> showsl_lit (STR ''\<newline>to\<newline>'') \<circ> showsl_cc d \<circ> showsl_nl \<circ> s);
     check_cc_prf d p })"
| "check_cc_prf c (Induction d ccs ihs) = (case normalize_cc c of
     CC_impl cs c' \<Rightarrow> do { do {
       check m_ortho (showsl_lit (STR ''CR or minimality required''));
       check_allm (\<lambda> cc. check (cc \<in> set cs) (showsl_cc cc \<circ> showsl_lit (STR ''\<newline>is not a premise of '') \<circ> showsl_cc c)) (d # ccs);
       (case d of
         CC_rewr (Fun f xs) q \<Rightarrow> do {
           let cs = vars_cc_list (CC_impl (CC_rewr (Fun f xs) q # ccs) c');
           check ((\<forall> x \<in> set xs. is_Var x) \<and> distinct (map the_Var xs)) 
             (showsl_lit (STR ''arguments of '') \<circ> showsl (Fun f xs) \<circ> showsl_lit (STR '' are not different variables''));
           let xs' = map the_Var xs;
           let rt = root (Fun f xs);
           check (mgu (Fun f xs) q = None) (showsl_lit (STR ''lhs and rhs unify''));
           check_allm (\<lambda> lr. check (root (fst lr) = rt \<longrightarrow> (\<exists> lr' \<in> set (map (\<lambda> (r,_). r) ihs). lr =\<^sub>v lr' \<and> isOK(check_disjoint cs (vars_rule_list lr')))) 
              (showsl_lit (STR ''could not find variable renamed version of rule '') \<circ> showsl_rule lr)) R;
           check_allm (\<lambda> ((l,r),rys,cc,_). do {
             let cc' = fresh.cc_rule_constraint fresh_xx f (args l) r q xs' ccs c' rys;
             check_allm (check_rys D rt r) rys;
             check (check_subsumes fresh_xx cc cc') (showsl_lit (STR ''new constraint is '') \<circ> showsl_cc cc \<circ> showsl_lit (STR ''\<newline>but expected was '') \<circ> showsl_cc cc')
           } <+? (\<lambda> s. showsl_lit (STR ''problem in constraint for rule '') \<circ> showsl_rule (l,r) \<circ> showsl_nl \<circ> s) 
           ) ihs
         }
       | _ \<Rightarrow> error (showsl_cc d \<circ> showsl_lit (STR '' is not a rewrite condition of the correct shape'')))}
     <+? (\<lambda> s. showsl_lit (STR ''problem in Induction rule with rewrite condition '') \<circ> showsl_cc d \<circ> showsl_lit (STR '' to switch from\<newline>'') 
       \<circ> showsl_cc c \<circ> showsl_lit (STR ''\<newline>to\<newline>'') \<circ>  
       showsl_list_gen (\<lambda>(_,_,c,_).showsl_cc c \<circ> showsl_nl) (STR '''') (STR '''') (STR '''') (STR '''') ihs \<circ> s);
   fcss <- Error_Monad.mapM (\<lambda> (_,_,c,p). check_cc_prf c p) ihs;
   return (concat fcss)})
"
  by pat_completeness auto

termination
proof
  let ?rel = "measure (\<lambda> (d :: ('f,string)cond_constraint, prf :: ('f,string)cond_constraint_prf). size prf)"
  fix c d ccs ihs x xa ya xb yb xc yc
  show "x \<in> set ihs \<Longrightarrow>
       (xa, ya) = x \<Longrightarrow>
       (xb, yb) = ya \<Longrightarrow>
       (xc, yc) = yb \<Longrightarrow>
       ((xc, yc), c, Induction d ccs ihs) \<in> ?rel"
    by (induct ihs, auto)
qed auto
end

text \<open>soundness of check_cc_prf.
  it is proven via soundness of the simplification rules (thm. cc_simplify), where we just have to show that
  all the preconditions are met. This will be done by induction on the simplification proof.\<close>
lemma check_cc_prf: assumes "fixed_trs_dep_order \<pi> R Q F S NS" and "check_cc_prf RR (defined R) FF m_ortho cc prf = return fcss" and 
  "Ball (set fcss) (cc_satisfied F S NS)" and F: "F = set FF" and R: "R = set RR" 
  and ortho: "m_ortho \<Longrightarrow> m \<or> CR (rstep R)"
  shows "fixed_trs_dep_order.cc_valid R Q F S NS nfs m cc"
proof -
  let ?chk = "check_cc_prf RR (defined R) FF m_ortho"
  let ?UR = "(\<lambda> _ . R) :: ('a,string)term \<Rightarrow> ('a,string)trs"
  obtain c :: "'a" where True by auto
  (* first enter the locales *)
  interpret fixed_trs_dep_order \<pi> R Q F S NS nfs m c by fact
  interpret fixed_trs_dep_order_fresh \<pi> R Q F S NS nfs m fresh_xx c ?UR
    by (unfold_locales, rule fresh_string, auto)
  (* next proof the result by induction on prf *)
  from assms have "?chk cc prf = return fcss" and "Ball (set fcss) (cc_satisfied F S NS)" by auto
  then show "cc_valid cc"
  proof (induct "prf" arbitrary: cc fcss)
    case (Final cc fcss)
    let ?n = "normalize_cc cc"
    obtain cs c where n: "?n = CC_impl cs c" unfolding normalize_cc_def by auto
    note check = Final(1)[simplified, unfolded n, simplified]
    have "cc_valid ?n"
    proof (cases cs)
      case Nil
      with check
      obtain stri st where c: "c = CC_cond stri st" using check by (cases c, auto)
      with Nil check have "fcss = [Unconditional_C stri st]" by auto
      with Final(2) have "cc_valid c" unfolding c cc_valid_def normal_F_subst_def by (cases st, cases stri, auto simp: rel_of_def)
      with Nil show ?thesis unfolding n by auto
    next
      case (Cons c1 ccs)
      with check 
      obtain stri st where c1: "c1 = CC_cond stri st" using check by (cases c1, auto)
      from Cons c1 check have ccs: "ccs = []" by (cases ccs, auto)
      note Cons = Cons[unfolded c1 ccs]
      from Cons check obtain stri' uv where c: "c = CC_cond stri' uv" using check by (cases c, auto)
      from check Cons c have c: "c = CC_cond stri uv" by (cases "stri = stri'", auto)
      from Cons c check have "fcss = [Conditional_C stri st uv]" by auto
      with Final(2) show "cc_valid ?n" unfolding n Cons c 
        by (cases st, cases uv, cases stri, auto simp: cc_valid_def normal_F_subst_def rel_of_def)
    qed
    then show ?case by (rule normalize_cc_valid)
  next
    case (Delete_Condition c p d fcss)
    from Delete_Condition(2)[simplified]
    have sub: "check_subsumes fresh_xx c d" 
      and rec: "?chk c p = return fcss" by auto
    from Delete_Condition(1)[OF rec Delete_Condition(3)] have "cc_valid c" .
    from cc_impliesE[OF check_subsumes[OF sub] this]
    show "cc_valid d" .
  next
    case (Different_Constructor c d fcc)
    obtain ds d' where d: "normalize_cc d = CC_impl ds d'" unfolding normalize_cc_def by auto
    note check = Different_Constructor(1)[simplified, unfolded d, simplified]
    from check obtain s t where c: "c = CC_rewr s t" by (cases c, auto)
    note check = check[unfolded c, simplified]
    from check obtain f ss where s: "s = Fun f ss" by (cases s, auto)
    note check = check[unfolded s, simplified]
    from check obtain g ts where t: "t = Fun g ts" by (cases t, auto)
    note check = check[unfolded t, simplified]
    show ?case
      by (rule cc_simplify[OF constructor_different[OF d]], insert check, auto)
  next
    case (Same_Constructor d c' p c fcc)
    obtain cs con where c: "normalize_cc c = CC_impl cs con" unfolding normalize_cc_def by auto
    note check = Same_Constructor(2)[simplified, unfolded c, simplified]
    from check obtain s t where d: "d = CC_rewr s t" by (cases d, auto)
    note check = check[unfolded d, simplified]
    from check obtain f ss where s: "s = Fun f ss" by (cases s, auto)
    note check = check[unfolded s, simplified]
    from check obtain ts where t: "t = Fun f ts" by (cases t, auto)
    note check = check[unfolded t Let_def, simplified]
    from check have "?chk c' p = return fcc" by auto
    from Same_Constructor(1)[OF this Same_Constructor(3)] have c': "cc_valid c'" by auto
    show ?case
      by (rule cc_simplify[OF constructor_same[OF c, of c' ss ts]], rule check_subsumes, insert check c', auto)
  next
    case (Variable_Equation x t d p c fcc)
    obtain cs con where c: "normalize_cc c = CC_impl cs con" unfolding normalize_cc_def by auto
    note check = Variable_Equation(2)[simplified, unfolded c Let_def, simplified]
    from check have "?chk d p = return fcc" by auto
    from Variable_Equation(1)[OF this Variable_Equation(3)] have d: "Ball (set [d]) cc_valid" by auto    
    show ?case
    proof (rule cc_simplify[OF _ d])
      from check have "CC_rewr (Var x) t \<in> set cs \<or> CC_rewr t (Var x) \<in> set cs \<and> (\<forall>f\<in>funas_term t. \<not> defined R f)" by auto
      then show "cc_simplify c [d]"
      proof
        assume mem: "CC_rewr (Var x) t \<in> set cs"
        show ?thesis
          by (rule variable_left[OF c check_subsumes refl mem], insert check, auto)
      next
        assume "CC_rewr t (Var x) \<in> set cs \<and> (\<forall>f\<in>funas_term t. \<not> defined R f)"
        then have mem: "CC_rewr t (Var x) \<in> set cs" and d: "(\<forall>f\<in>funas_term t. \<not> defined R f)" by auto
        show ?thesis
          by (rule variable_right[OF c check_subsumes refl mem], insert check d, auto)
      qed
    qed
  next
    case (Funarg_Into_Var c' i x d p c fcc)
    obtain cs con where c: "normalize_cc c = CC_impl cs con" unfolding normalize_cc_def by auto
    note check = Funarg_Into_Var(2)[simplified, unfolded c, simplified]
    from check obtain s t where c': "c' = CC_rewr s t" by (cases c', auto)
    note check = check[unfolded c', simplified]
    from check obtain f ss where s: "s = Fun f ss" by (cases s, auto)
    note check = check[unfolded s Let_def, simplified]
    from check have "?chk d p = return fcc" by auto
    from Funarg_Into_Var(1)[OF this Funarg_Into_Var(3)] have d: "Ball (set [d]) cc_valid" by auto 
    from check have mem: "CC_rewr (Fun f ss) t \<in> set cs" and i: "i < length ss" by auto
    from mem id_take_nth_drop[OF i] have mem: "CC_rewr (Fun f (take i ss @ ss ! i # drop (Suc i) ss)) t \<in> set cs" by auto
    from check have x: "x \<notin> vars_cc c" by auto
    show ?case
      by (rule cc_simplify[OF fun_arg_into_var[OF c check_subsumes x mem] d], insert check F, auto)
  next
    case (Simplify_Condition bc \<sigma> d p c fcs)
    obtain cs con where c: "normalize_cc c = CC_impl cs con" unfolding normalize_cc_def by auto
    obtain ys cc where unb: "cc_unbound bc = (ys,cc)" by force
    obtain \<phi>' \<psi>' where cc: "normalize_cc cc = CC_impl \<phi>' \<psi>'" unfolding normalize_cc_def by auto
    note check = Simplify_Condition(2)[simplified, unfolded c, simplified, unfolded unb, simplified, unfolded cc Let_def, simplified]
    from check have "?chk d p = return fcs" by auto
    from Simplify_Condition(1)[OF this Simplify_Condition(3)] have valid: "Ball (set [d]) cc_valid" by simp
    from check cc_unbound_bound[OF unb] have mem: "cc_bound ys cc \<in> set cs" by auto
    let ?\<sigma> = "mk_subst Var \<sigma>"
    let ?vs = "remdups (concat (map (\<lambda>x_t. vars_term_list (snd x_t)) (mk_subst_domain \<sigma>)))"
    let ?\<sigma>vs = "(?\<sigma>, ?vs)"
    from check have subs: "check_subsumes fresh_xx d  (CC_impl (fresh.cc_subst_apply fresh_xx \<psi>' ?\<sigma>vs # cs) con)" by auto
    {
      fix c
      assume c: "c \<in> set \<phi>'"
      with check obtain d where d: "d \<in> set cs"
        and check: "check_subsumes fresh_xx d
               (fresh.cc_subst_apply fresh_xx c ?\<sigma>vs)" by auto
      from check_subsumes[OF check] d have "\<exists> d \<in> set cs. d \<longrightarrow>cc fresh.cc_subst_apply fresh_xx c ?\<sigma>vs" by blast
    } note subs2 = this
    show ?case
      by (rule cc_simplify[OF simplify_condition[OF c mem cc _ _ _ _ check_subsumes[OF subs]] valid],
        insert check subs2, auto simp: range_vars_def mk_subst_domain F)
  next
    case (Induction d ccs ihs c fcss)
    obtain cs con where c: "normalize_cc c = CC_impl cs con" unfolding normalize_cc_def by auto
    note check = Induction(2)[simplified, unfolded c Let_def, simplified]
    from check obtain s q where d: "d = CC_rewr s q" by (cases d, auto)
    note check = check[unfolded d, simplified]
    from check obtain f xs where s: "s = Fun f xs" by (cases s, auto)
    note check = check[unfolded s, simplified]
    define xs' where "xs' = map the_Var xs"
    note check = check[unfolded xs'_def[symmetric]]
    from check have dist: "distinct xs'" by auto
    from check have "\<And> x. x \<in> set xs \<Longrightarrow> is_Var x" by auto
    then have xs: "xs = map Var xs'" unfolding xs'_def map_map comp_def
      by (induct xs, auto)
    note check = check[unfolded xs, simplified]
    from check have mgu: "mgu (Fun f (map Var xs')) q = None" by auto
    from check have mem: "CC_rewr (Fun f (map Var xs')) q \<in> set cs" by auto
    from check have subset: "set ccs \<subseteq> set cs" by auto
    from check have m_ortho by auto
    let ?c = "CC_impl (CC_rewr (Fun f (map Var xs')) q # ccs) con"
    let ?ccs = "map (\<lambda> (_,_,c,_). c) ihs"
    show ?case
    proof (rule cc_simplify[OF induction[OF c mgu mem subset _ dist ortho[OF \<open>m_ortho\<close>]]])
      (* consider constraint for each rule *)
      fix ls r
      assume len: "length xs' = length ls"
        and mem: "(Fun f ls, r) \<in> R"
      with R check obtain lr' info where ihs: "(lr',info) \<in> set ihs" and
          eq: "(Fun f ls, r) =\<^sub>v lr'" and 
          disj: "vars_rule lr' \<inter> vars_cc ?c = {}" 
        by (auto simp: ac_simps)
      obtain l' r' where lr': "lr' = (l',r')" by force
      from eq_rule_mod_varsE[OF eq[unfolded lr']] obtain ls' where l': "l' = Fun f ls'" by (cases l', auto)
      obtain rys c p where info: "info = (rys,c,p)" by (cases info, auto)
      note id = l' info lr'
      note ihs = ihs[unfolded id]
      note eq = eq[unfolded id]
      note disj = disj[unfolded id]
      from ihs have c: "c \<in> set ?ccs" by force
      from check ihs have subs: "check_subsumes fresh_xx c
        (fresh.cc_rule_constraint fresh_xx f ls' r' q xs' ccs con rys)"
        by auto
      show "\<exists>d ls' r' rs_ys_list.
              (Fun f ls, r) =\<^sub>v (Fun f ls', r') \<and>
              vars_rule (Fun f ls', r') \<inter> vars_cc ?c = {} \<and>
              d \<in> set ?ccs \<and>
              d \<longrightarrow>cc fresh.cc_rule_constraint fresh_xx f ls' r' q xs' ccs con rs_ys_list \<and>
              (\<forall>(r, ys)\<in>set rs_ys_list.
                  root r = Some (f,length xs') \<and> r' \<unrhd> r \<and> vars_term r' \<inter> set ys = {} \<and> (\<forall>fn\<in>funas_args_term r. \<not> defined R fn))"
      proof (intro exI conjI, rule eq, rule disj, rule c, rule check_subsumes[OF subs], clarify)
        fix r ys
        assume "(r,ys) \<in> set rys"
        with check ihs have check: "isOK(check_rys (defined R) (Some (f, length xs')) r' (r,ys))" by force
        from this[unfolded check_rys_def]
        show "root r = Some (f, length xs') \<and> r' \<unrhd> r \<and> vars_term r' \<inter> set ys = {} \<and> (\<forall>fn\<in>funas_args_term r. \<not> defined R fn)" by auto
      qed
    next
      {
        fix c 
        assume c: "c \<in> set ?ccs"
        then obtain r i p where mem: "(r,i,c,p) \<in> set ihs" by force
        let ?rec = "Error_Monad.mapM (\<lambda>(_, _, c, p). ?chk c p) ihs"
        from check obtain fcssl where rec: "?rec = return fcssl"
          by (cases ?rec, auto)
        with check have fcss: "fcss = concat fcssl" by auto
        note res = mapM_return[OF rec]
        from res mem obtain fcs where chk: "?chk c p = return fcs" by (cases "?chk c p", auto)
        with res mem have "set fcs \<subseteq> set fcss" unfolding fcss by auto
        with Induction(3) have valid: "Ball (set fcs) (cc_satisfied F S NS)" by auto
        have "cc_valid c" 
          by (rule Induction(1)[OF mem chk valid])
      }
      then show "Ball (set ?ccs) cc_valid" by auto
    qed
  qed
qed

text \<open>it is now easy, to check several simplification proofs\<close>
fun check_cc_prfs :: "('f,string)rules \<Rightarrow> ('f \<times> nat \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat) list \<Rightarrow> bool 
  \<Rightarrow> (('f :: showl,string)cond_constraint \<times> 'a \<times> ('f,string)cond_constraint_prf) list 
  \<Rightarrow> ('f,string)c_constraint list result" where
  "check_cc_prfs R D F m_ortho [] = return []"
| "check_cc_prfs R D F m_ortho ((c,_,prf) # cpfs) = (do {
    l1 <- check_cc_prf R D F m_ortho c prf;
    l2 <- check_cc_prfs R D F m_ortho cpfs;
    return (l1 @ l2)
   })"

lemma check_cc_prfs: assumes "fixed_trs_dep_order \<pi> R Q F S NS" and "check_cc_prfs RR (defined R) FF m_ortho ccpfs = return fcss" and 
  "Ball (set fcss) (cc_satisfied F S NS)" and F: "F = set FF" and R: "R = set RR"
  and ortho: "m_ortho \<Longrightarrow> m \<or> CR (rstep R)"
  shows "Ball (fst ` set ccpfs) (fixed_trs_dep_order.cc_valid R Q F S NS nfs m)"
proof -
  interpret fixed_trs_dep_order \<pi> R Q F S NS by fact
  let ?D = "defined R"
  from assms have "check_cc_prfs RR ?D FF m_ortho ccpfs = return fcss" and "Ball (set fcss) (cc_satisfied F S NS)" by auto
  then show "Ball (fst ` set ccpfs) cc_valid"
  proof (induct ccpfs arbitrary: fcss)
    case Nil then show ?case by auto
  next
    case (Cons cpf ccpfs)
    obtain c a p where cpf: "cpf = (c,a,p)" by (cases cpf, auto)
    note check = Cons(2)[unfolded cpf, simplified]
    from check obtain l1 where cp: "check_cc_prf RR ?D FF m_ortho c p = return l1" by (cases "check_cc_prf RR ?D FF m_ortho c p", auto)
    from check cp obtain l2 where ccpfs: "check_cc_prfs RR ?D FF m_ortho ccpfs = return l2" by (cases "check_cc_prfs RR ?D FF m_ortho ccpfs", auto)
    from check cp ccpfs have fcss: "fcss = l1 @ l2" by auto
    note valid = Cons(3)[unfolded fcss]
    from Cons(1)[OF ccpfs] valid check_cc_prf[OF assms(1) cp _ _ _ ortho, of nfs] F R show ?case unfolding cpf by auto
  qed
qed

text \<open>a datatype for storing the information, which conditional constraints are constructed and how they are simplified\<close>
datatype ('f,'v)cond_red_pair_prf = Cond_Red_Pair_Prf 
  'f (* bound constant *)
  "(('f,'v)cond_constraint \<times> ('f,'v)rules \<times> ('f,'v)cond_constraint_prf) list" (* initial constraints with pair-sequence and proof *)
  nat (* how many pairs before are considered *)
  nat (* how many pairs afterwards are considered *)

text \<open>eventually, the constraint checking procedure is combined with the conditional reduction pair processor into one algorithm.
  The parameter merge is used to indicate whether two problems should be returned (P - Pstrict, P - Pbound), or whether one
  merged problem is desired (P - (Pstrict \<inter> Pbound))\<close>
definition
  conditional_general_reduction_pair_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> (('f \<times> nat) list \<Rightarrow> ('f,string) non_inf_order) 
  \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules 
  \<Rightarrow> ('f,string)cond_red_pair_prf \<Rightarrow> bool \<Rightarrow> 'dpp \<Rightarrow> 'dpp list result"
where
  "conditional_general_reduction_pair_proc I grp Pstrict Pbound prof Merge dpp \<equiv> case prof of
    Cond_Red_Pair_Prf c ccs bef aft \<Rightarrow> let 
    p = dpp_ops.pairs I dpp;
    r = dpp_ops.rules I dpp;
    F = remdups (funas_trs_list r @ funas_args_trs_list p @ concat (map funas_term_list (dpp_ops.Q I dpp)));
    rp = grp F in
  check_return (do {
     non_inf_order.valid rp;
     check (dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''require well-formedness of TRS''));
     let is_def = dpp_spec.is_defined I dpp;
     check_varcond_subset p;
     check_allm (\<lambda>(l, r). do { \<comment> \<open>require that pairs have standard structure\<close>
        check_no_var l;
        check_no_var r;
        check_no_defined_root is_def r
      }) p;
     let ccs' = map (\<lambda> (c,uvs,prf). (c,uvs)) ccs;
     let check_present = check_constraint_present I dpp c p bef aft ccs';
     let (ps,pns) = dpp_ops.split_pairs I dpp Pstrict;
     let (pb,pnb) = dpp_ops.split_pairs I dpp Pbound;
     let pi = non_inf_order.af rp;
     let us = usable_rules_gen pi r p;
     check_allm (check_present Strict) ps;
     check_allm (check_present Non_Strict) pns;
     check_allm (check_present Bound) pb;
     check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost required''));
     check_allm (non_inf_order.ns rp) us 
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
     let m = dpp_ops.minimal I dpp;
     let ortho = isOK(check_weakly_orthogonal string_rename r);
     (do {
        fcs \<leftarrow> check_cc_prfs r (dpp_spec.is_defined I dpp) F (m \<or> ortho) ccs
           <+? (\<lambda>s. showsl_lit (STR ''problem when simplifying conditional constraints\<newline>'') \<circ> s);
        check_allm (non_inf_order.cc rp) fcs
          <+? (\<lambda> s. showsl_lit (STR ''problem when orienting final (conditional) constraints for pairs\<newline>'') \<circ> s)
     })
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the bounded increase processor with the following\<newline>'') \<circ>
     (non_inf_order.desc rp) \<circ> showsl_nl \<circ> s))
    (if Merge then [dpp_spec.delete_pairs I dpp (list_inter Pstrict Pbound)] else [dpp_spec.delete_pairs I dpp Pstrict, dpp_spec.delete_pairs I dpp Pbound])"

lemma conditional_general_reduction_pair_proc: fixes I :: "('a,'f :: {compare_order,countable,showl}, string)dpp_ops"
  assumes spec: "dpp_spec I"
    and grp: "generic_non_inf_order_impl grp"
    and proc: "conditional_general_reduction_pair_proc I (grp rp) Pstrict Pbound prof Merge d = return dpps"
    and rec: "\<And>d'. d' \<in> set dpps \<Longrightarrow> finite_dpp (dpp_ops.dpp I d')"
  shows "finite_dpp (dpp_ops.dpp I d)"
proof -
  obtain c ccs bef aft where prof: "prof = Cond_Red_Pair_Prf c ccs bef aft" by (cases prof, force)
  note proc = proc[unfolded prof conditional_general_reduction_pair_proc_def cond_red_pair_prf.simps]
  interpret dpp_spec I by fact
  let ?RB = "rules d"
  let ?PB = "pairs d"
  let ?Q = "Q d"
  let ?M = "M d"
  let ?o = "isOK(check_weakly_orthogonal string_rename ?RB)"
  let ?m_o = "?M \<or> ?o"
  define F where "F = remdups (funas_trs_list ?RB @ funas_args_trs_list ?PB @ concat (map funas_term_list ?Q))"
  let ?ctxt_closure = "non_inf_order.cc (grp rp F)"
  let ?NS = "non_inf_order.ns (grp rp F)"
  let ?pi = "non_inf_order.af (grp rp F)"
  obtain Ps Pns where split1: "dpp_ops.split_pairs I d Pstrict = (Ps,Pns)" by force
  obtain Pb Pub where split2: "dpp_ops.split_pairs I d Pbound = (Pb,Pub)" by force
  note proc = proc[unfolded Let_def split1 split2 F_def[symmetric], simplified]
  from proc have valid: "isOK (non_inf_order.valid (grp rp F))" by blast
  from proc have inn: "NF_terms (set (Q d)) \<subseteq> NF_trs (set (R d) \<union> set (Rw d))" by blast
  from proc have wwf: "wwf_qtrs (set ?Q) (set ?RB)" by simp
  from proc have dpps: "dpps = (if Merge then [delete_pairs d (list_inter Pstrict Pbound)] else [delete_pairs d Pstrict, delete_pairs d Pbound])" by blast
  from proc have "(\<forall>(l, r)\<in>set (P d) \<union> set (Pw d). vars_term r \<subseteq> vars_term l) \<and>
    (\<forall>(l, r)\<in>set (P d) \<union> set (Pw d). is_Fun l \<and> is_Fun r \<and> \<not> defined (set (R d) \<union> set (Rw d)) (the (root r)))" 
    by argo
  hence fun_ndef_vars: "\<And> s t. (s,t) \<in> set (P d) \<union> set (Pw d) \<Longrightarrow> 
    is_Fun s \<and> is_Fun t \<and> \<not> defined (set (R d) \<union> set (Rw d)) (the (root t))
    \<and> vars_term t \<subseteq> vars_term s" by auto 
  from proc obtain fcs where ccs: "check_cc_prfs (rules d) (defined (set (R d) \<union> set (Rw d))) F ?m_o ccs = return fcs"  by (cases "check_cc_prfs (rules d) (defined (set (R d) \<union> set (Rw d))) F ?m_o ccs", auto)
  note proc = proc[unfolded ccs, simplified]
  from proc have NS: "isOK(check_allm ?NS (usable_rules_gen (non_inf_order.af (grp rp F)) ?RB ?PB))" by auto
  from proc have ctxt_closure: "isOK(check_allm ?ctxt_closure fcs)" by auto
  let ?ccs' = "map (\<lambda> (c,uvs,prf). (c,uvs)) ccs"
  let ?present = "\<lambda> ct st. isOK(check_constraint_present I d c (pairs d) bef aft ?ccs' ct st)"
  from proc have presentS: "Ball (set Ps) (?present Strict)" by auto
  from proc have presentNS: "Ball (set Pns) (?present Non_Strict)" by auto
  from proc have presentB: "Ball (set Pb) (?present Bound)" by auto
  from generic_non_inf_order_impl.generate_non_inf_order[OF grp valid NS ctxt_closure] obtain S NS where
    non_inf: "non_inf_order_trs S NS (set F) ?pi" and 
    fcs: "Ball (set fcs) (cc_satisfied (set F) S NS)" and
    us: "set (usable_rules_gen ?pi ?RB ?PB) \<subseteq> NS" by force
  have inf: "infinite (UNIV :: string set)" by (rule infinite_UNIV_listI)
  interpret non_inf_order_trs S NS "set F" ?pi by fact
  have fixed_trs: "fixed_trs_dep_order ?pi (set ?RB) (set ?Q) (set F) S NS" 
    by (unfold_locales, insert inn wwf F_def inf, auto)
  let ?UR = "\<lambda> _ . set ?RB"
  interpret fixed_trs_dep_order ?pi "set ?RB" "set ?Q" "set F" S NS "NFS d" ?M c by fact
  interpret fixed_trs_dep_order_fresh ?pi "set ?RB" "set ?Q" "set F" S NS "NFS d" ?M fresh_xx c ?UR
    by (unfold_locales, rule fresh_string, auto)
  note us = us[unfolded usable_rules_gen[OF refl]]
  have d: "dpp d = (NFS d, M d, set (P d), set (Pw d), set ?Q, set (R d), set (Rw d))" by simp
  {
    fix dd 
    assume dd: "dd \<in> set [delete_pairs d Pstrict, delete_pairs d Pbound]"     
    have "finite_dpp (dpp dd)" 
    proof (cases Merge)
      case False
      with rec[unfolded dpps] dd show ?thesis by auto
    next
      case True
      (* if we only delete the intersection of Pbound and Pstrict, we have proven termination/finiteness 
         of a DP-problem with more pairs than both P-Pbound and P-Pstrict. By monotonicity this ensures termination
         of both of these DP-problems *)
      with rec[unfolded dpps] have "finite_dpp (dpp (delete_pairs d (list_inter Pstrict Pbound)))" by simp
      note fin = finite_dpp_mono[OF this[unfolded delete_P_Pw_sound] _ _ refl subset_refl refl]
      let ?dpp = "\<lambda> PS. (NFS d, M d, set (P d) - set PS, set (Pw d) - set PS, set (Q d), set (R d), set (Rw d))"
      from dd have "dpp dd = ?dpp Pstrict \<or> dpp dd = ?dpp Pbound" unfolding delete_P_Pw_sound[symmetric] by auto
      then obtain PS where dd: "dpp dd = ?dpp PS" and mono: "set Pstrict \<inter> set Pbound \<subseteq> set PS" by auto
      show ?thesis unfolding dd by (rule fin, insert mono, auto)
    qed
  } note finite = this
  show ?thesis unfolding d
  proof (rule conditional_general_reduction_pair_proc)
    show "set (R d) \<union> set (Rw d) = set (rules d)" by simp
    show "gen_usable_rules_pairs (set (P d) \<union> set (Pw d)) \<subseteq> NS" using us by simp
    show "set (P d) \<union> set (Pw d) \<subseteq> set Ps \<union> set Pns" using split1 by auto
    show "funas_args_trs (set (P d) \<union> set (Pw d)) \<subseteq> set F" unfolding F_def by auto
    from ccs have ccs: "check_cc_prfs (rules d) (defined (set (rules d))) F ?m_o ccs = Inr fcs" by simp
    show "Ball (fst ` set ccs) cc_valid"
      by (rule check_cc_prfs[OF fixed_trs ccs fcs refl refl], insert check_weakly_orthogonal[of string_rename "rules d"], auto)
    let ?DS = "(NFS d, M d, set (P d) - set Ps, set (Pw d) - set Ps, set ?Q, set (R d), set (Rw d))"
    have "dpp (delete_pairs d Pstrict) = ?DS"
      unfolding delete_P_Pw_sound using split1 by auto
    with finite[of "delete_pairs d Pstrict"] 
    show "finite_dpp ?DS" by simp
    let ?DB = "(NFS d, M d, set (P d) - set Pb, set (Pw d) - set Pb, set ?Q, set (R d), set (Rw d))"
    have "dpp (delete_pairs d Pbound) = ?DB"
      unfolding delete_P_Pw_sound using split2 by auto
    with finite[of "delete_pairs d Pbound"] 
    show "finite_dpp ?DB" by simp
  next
    fix s t
    assume "(s,t) \<in> set (P d) \<union> set (Pw d)"
    from fun_ndef_vars[OF this]
    have "is_Fun s \<and> is_Fun t" and ndef: "\<not> defined (set ?RB) (the (root t))" and "vars_term t \<subseteq> vars_term s" by auto
    show "is_Fun s \<and> is_Fun t" by fact
    show "vars_term t \<subseteq> vars_term s" by fact
    show "\<not> defined (applicable_rules (set ?Q) (set ?RB)) (the (root t))" using ndef
      by (rule ndef_applicable_rules)
  next
    {
      fix PP ct
      assume PP: "Ball (set PP) (?present ct)"
      have "Ball (set PP) (constraint_present bef aft (set (P d) \<union> set (Pw d)) ct (fst ` set ccs))" (is "Ball _ ?p")
      proof
        fix st
        assume "st \<in> set PP"
        with PP have st: "?present ct st" by auto
        note st = st[unfolded check_constraint_present_def Let_def]
        show "?p st" unfolding constraint_present_def
        proof (intro allI impI)
          fix sts
          assume sts: "sts \<in> initial_conditions bef aft (set (P d) \<union> set (Pw d)) st"
          have sts: "sts \<in> initial_conditions_gen (\<lambda>st uv. is_iedg_edge_dpp I d st (fst uv)) bef aft (set (P d) \<union> set (Pw d)) st"
            unfolding initial_conditions_def
            by (rule set_mp[OF initial_conditions_gen_mono sts[unfolded initial_conditions_def]], 
              insert is_iedg_edge_dpp_DG_sound[OF spec, where d = d], force)
          with st 
          obtain d uvs prof where mem: "(d,uvs,prof) \<in> set ccs" and  disj: "disjoint_variant sts uvs"
            and sub: "check_subsumes fresh_xx d (constraint_of c ct uvs bef)" by auto
          from mem check_subsumes[OF sub] disj
          show "\<exists>d uvs. disjoint_variant sts uvs \<and> d \<in> fst ` set ccs \<and> cc_implies d (constraint_of c ct uvs bef)" by force
        qed
      qed
    } note present = this
    show "Ball (set Ps) (constraint_present bef aft (set (P d) \<union> set (Pw d)) Strict (fst ` set ccs))"
      by (rule present[OF presentS])
    show "Ball (set Pns) (constraint_present bef aft (set (P d) \<union> set (Pw d)) Non_Strict (fst ` set ccs))"
      by (rule present[OF presentNS])
    show "Ball (set Pb) (constraint_present bef aft (set (P d) \<union> set (Pw d)) Bound (fst ` set ccs))"
      by (rule present[OF presentB])
  qed
qed

lemma conditional_general_reduction_pair_proc_len: 
  assumes "conditional_general_reduction_pair_proc I rp Pstrict Pbound prof Merge d = return dpps"
  shows "length dpps = (if Merge then 1 else 2)"
  using assms
  by (cases prof, cases Merge, auto simp: conditional_general_reduction_pair_proc_def Let_def)

end

