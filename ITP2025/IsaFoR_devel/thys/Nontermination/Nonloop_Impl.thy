(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Nonloop_Impl 
imports
  Nonloop
  Nontermination
  Innermost_Loops_Impl
  TRS.Q_Restricted_Rewriting_Impl
  TRS.Q_Relative_Rewriting
  Framework.QDP_Framework_Impl
  Show.Shows_Literal
begin

(* implementation types, functions, ... for several pattern related types, functions, ... *)
type_synonym ('f, 'v) pat_termI = "('f, 'v) term \<times> ('f, 'v) substL \<times> ('f, 'v) substL"

fun pat_termI :: "('f, 'v) pat_termI \<Rightarrow> nat \<Rightarrow> ('f, 'v) term" where
  "pat_termI (t, \<sigma>, \<mu>) n = t \<cdot> (mk_subst Var \<sigma>)^^n \<cdot> mk_subst Var \<mu>"

fun pat_term_of :: "('f, 'v) pat_termI \<Rightarrow> ('f, 'v) pat_term" where
  "pat_term_of (t, \<sigma>, \<mu>) = (t, mk_subst Var \<sigma>, mk_subst Var \<mu>)"

definition pat_dv_impl :: "('f, 'v) pat_termI \<Rightarrow> 'v list" where
  "pat_dv_impl p \<equiv>
    case p of (t, \<sigma>, \<mu>) \<Rightarrow> remdups (map fst (mk_subst_domain \<sigma> @ mk_subst_domain \<mu>))"

lemma pat_dv_impl[simp]: "set (pat_dv_impl p) = pat_dv (pat_term_of p)"
  by (cases p, unfold pat_dv_impl_def pat_dv_def, auto simp: mk_subst_domain)

definition vars_pat_term_impl :: "('f, 'v) pat_termI \<Rightarrow> 'v list"
  where "vars_pat_term_impl p \<equiv> case p of (s,\<sigma>,\<mu>) \<Rightarrow> remdups 
    (vars_term_list s @ vars_subst_impl \<sigma> @ vars_subst_impl \<mu>)"

lemma vars_pat_term_impl[simp]: "set (vars_pat_term_impl p) = vars_pat_term (pat_term_of p)" unfolding vars_pat_term_impl_def vars_pat_term_def by (cases p, auto)

definition pat_dom_renaming_impl :: "('f, 'v) pat_termI \<Rightarrow> ('f, 'v) substL \<Rightarrow> bool"
  where "pat_dom_renaming_impl p \<rho> \<equiv> let \<rho>' = mk_subst_domain \<rho>; xs = map Var (vars_pat_term_impl p) in
     is_renaming_impl \<rho> \<and> set (map fst \<rho>') \<subseteq> set (pat_dv_impl p) \<and>
     (\<forall> t \<in> set (map snd \<rho>'). t \<notin> set xs)"

lemma pat_dom_renaming_impl [simp]:
  "pat_dom_renaming_impl p \<rho> = pat_dom_renaming (pat_term_of p) (mk_subst Var \<rho>)"
  unfolding pat_dom_renaming_def pat_dom_renaming_impl_def Let_def
  by (auto simp: mk_subst_domain)

(* pretty printer for pattern *)
definition showsl_pat_term :: "('f :: showl, 'v :: showl) pat_termI \<Rightarrow> showsl" where
  "showsl_pat_term p \<equiv> case p of (s, \<sigma>, \<tau>) \<Rightarrow> showsl (s, mk_subst_domain \<sigma>, mk_subst_domain \<tau>)"

(* datatype for certificates of pattern equivalence proofs *)
datatype ('f,'v) pat_eqv_prf =
  Pat_Dom_Renaming "('f, 'v) substL"
| Pat_Irrelevant "('f, 'v) substL" "('f, 'v) substL"
| Pat_Simplify "('f, 'v) substL" "('f, 'v) substL"

(* and function to check equivalence proofs *)
fun
  check_pat_eqv_prf ::
    "('f, 'v) pat_eqv_prf \<Rightarrow> ('f :: showl, 'v :: showl) pat_termI \<Rightarrow> ('f, 'v) pat_termI result"
where 
  "check_pat_eqv_prf (Pat_Irrelevant \<sigma>' \<mu>') (t,\<sigma>,\<mu>) = do {
        let W = W_impl (mk_subst_domain \<sigma>) t; 
        let sig = mk_subst Var \<sigma>;
        let sig' = mk_subst Var \<sigma>';
        let mu = mk_subst Var \<mu>;
        let mu' = mk_subst Var \<mu>';
        check_allm (\<lambda> x. do {
           check (sig x = sig' x) (x,sig x, sig' x,''pumping'');
           check (mu x = mu' x) (x,mu x, mu' x,''closing'')
        }) W <+? (\<lambda> (x,t,t',sub). 
             showsl_lit (STR ''error in equivalence (irrelevant): for variable '') \<circ> showsl x \<circ> 
             showsl_lit (STR '' obtain different values for '') \<circ> showsl sub \<circ> showsl_lit (STR '' substitution: '') \<circ> 
             showsl t \<circ> showsl_lit (STR '' != '') \<circ> showsl t');
        return (t,\<sigma>',\<mu>')
     }"
|   "check_pat_eqv_prf (Pat_Simplify \<mu>1 \<mu>2) (t,\<sigma>,\<mu>) = do {
       check (subst_eq \<mu> (subst_compose_impl \<mu>1 \<mu>2)) (showsl_lit (STR ''mu != mu1 mu2''));
       check (commutes_impl \<mu>1 \<sigma>) (showsl_lit (STR ''sigma and mu1 do not commute''));
       return (t \<cdot> mk_subst Var \<mu>1, \<sigma>, \<mu>2)
     }"
|   "check_pat_eqv_prf (Pat_Dom_Renaming \<rho>) (t,\<sigma>,\<mu>) = do {
       check (pat_dom_renaming_impl (t,\<sigma>,\<mu>) \<rho>) (showsl_lit (STR ''rho is not a domain renaming for p''));
       let i\<rho> = is_inverse_renaming_impl \<rho>;
       let \<sigma>' = mk_subst_case (map (the_Var o mk_subst Var \<rho>) (map fst (mk_subst_domain \<sigma>)))
         (\<lambda> x. Var x \<cdot> mk_subst Var i\<rho> \<cdot> mk_subst Var \<sigma> \<cdot> mk_subst Var \<rho>) [];
       let \<mu>' = mk_subst_case (map (the_Var o mk_subst Var \<rho>) (map fst (mk_subst_domain \<mu>)))
         (\<lambda> x. Var x \<cdot> mk_subst Var i\<rho> \<cdot> mk_subst Var \<mu>) i\<rho>;
       return (t \<cdot> mk_subst Var \<rho>, \<sigma>', \<mu>')
     }"

locale fixed_subst_impl = 
  fixes \<mu> :: "('f, 'v) substL"

sublocale fixed_subst_impl \<subseteq> fixed_subst "mk_subst Var \<mu>" .

lemma check_pat_eqv_prf:
  assumes res: "check_pat_eqv_prf prf (p :: ('f :: showl,'v :: showl)pat_termI) = return q"
  shows "pat_termI p = pat_termI q"
proof (rule ext)
  fix n :: nat
  from res 
  show "pat_termI p n = pat_termI q n"
  proof (induct p rule: check_pat_eqv_prf.induct)
    case (1 \<sigma>' \<mu>' t \<sigma> \<mu>)
    interpret fixed_subst_impl \<sigma> .
    note 1 = 1[simplified, unfolded Let_def, simplified, unfolded W_impl]
    from 1 have q: "q = (t,\<sigma>',\<mu>')" by simp
    show ?case unfolding q pat_termI.simps 
    proof (rule pat_equivalence_lem_6)
      fix x
      assume "x \<in> pat_rv t (mk_subst Var \<sigma>)"
      from pat_rv_rev[OF this] have "x \<in> W t" unfolding vars_iteration_def by auto
      with 1 show "mk_subst Var \<sigma> x = mk_subst Var \<sigma>' x" by simp
    next
      fix x
      assume "x \<in> pat_rv t (mk_subst Var \<sigma>)"
      from pat_rv_rev[OF this] have "x \<in> W t" unfolding  vars_iteration_def by auto
      with 1 show "mk_subst Var \<mu> x = mk_subst Var \<mu>' x" by simp
    qed
  next
    case (2 \<mu>1 \<mu>2 t \<sigma> \<mu>)
    interpret fixed_subst_impl \<sigma> .
    note 2 = 2[simplified]
    from 2 have comm: "mk_subst Var \<mu>1 \<circ>\<^sub>s mk_subst Var \<sigma> = mk_subst Var \<sigma> \<circ>\<^sub>s mk_subst Var \<mu>1" by simp
    from 2 have q: "q = (t \<cdot> mk_subst Var \<mu>1, \<sigma>, \<mu>2)" by simp
    show ?case unfolding q pat_termI.simps 
      unfolding pat_equivalence_lem_9[OF comm, symmetric] using 2 by simp
  next
    case (3 \<rho> t \<sigma> \<mu>)
    note 3 = 3[simplified, unfolded Let_def, simplified]
    let ?i\<rho> = "is_inverse_renaming_impl \<rho>"
    let ?m = "mk_subst Var :: ('f,'v)substL \<Rightarrow> ('f,'v)subst"
    let ?\<sigma> = "?m \<sigma>"
    let ?\<mu> = "?m \<mu>"
    let ?\<rho> = "?m \<rho>"
    let ?d = mk_subst_domain 
    let ?d\<sigma> = "?d \<sigma>"
    let ?d\<mu> = "?d \<mu>"
    let ?\<sigma>' = "mk_subst_case (map (the_Var o ?\<rho>) (map fst ?d\<sigma>))
         (\<lambda> x. Var x \<cdot> ?m ?i\<rho> \<cdot> ?\<sigma> \<cdot> ?\<rho>) []"
    let ?\<mu>' = "mk_subst_case (map (the_Var o ?\<rho>) (map fst ?d\<mu>))
         (\<lambda> x. Var x \<cdot> ?m ?i\<rho> \<cdot> ?\<mu>) ?i\<rho>"
    from 3 have ren: "pat_dom_renaming (t, ?m \<sigma>, ?m \<mu>) (?m \<rho>)"
      and q: "q = (t \<cdot> ?m \<rho>, ?\<sigma>', ?\<mu>')" by auto    
    have subst_eq: "\<And> t t' \<sigma> \<sigma>'. t = t' \<Longrightarrow> \<sigma> = \<sigma>' \<Longrightarrow> t \<cdot> \<sigma> = t' \<cdot> \<sigma>'" by auto
    have subst_eq2: "\<And> \<sigma> \<sigma>'. \<sigma> = \<sigma>' \<Longrightarrow> \<sigma>^^n = \<sigma>'^^n" by auto
    have lambda: "\<And> p q. \<lbrakk>\<And> x. p x = q x\<rbrakk> \<Longrightarrow> (\<lambda> x. p x) = (\<lambda> x. q x)" by auto
    have if_c: "\<And> b1 b2 t1 t2 e1 e2. b1 = b2 \<Longrightarrow> t1 = t2 \<Longrightarrow> e1 = e2 \<Longrightarrow> (if b1 then t1 else e1) = (if b2 then t2 else e2)" by auto
    from ren have vren: "is_renaming ?\<rho>" unfolding pat_dom_renaming_def by auto
    note inv[simp] = is_inverse_renaming_impl[OF vren]
    {
      fix y and \<sigma> :: "('f,'v)substL"
      have "(Var y \<in> ?\<rho> ` subst_domain (?m \<sigma>)) = (y \<in> set (map (the_Var o ?\<rho>) (map fst (?d \<sigma>))))" (is "?l = ?r")
      proof -
        obtain s where s: "s = subst_domain (?m \<sigma>)" by auto
        have "?r = (y \<in> the_Var ` ?\<rho> ` s)" unfolding s
          by (force simp: mk_subst_domain)
        also have "... = (\<exists> x \<in> s. y = the_Var (?\<rho> x))" by auto
        also have "... = (\<exists> x \<in> s. Var y = ?\<rho> x)" 
        proof -
          {
            fix x
            obtain x' where "?\<rho> x = Var x'" using vren unfolding is_renaming_def by auto
            then have "(y = the_Var (?\<rho> x)) = (Var y = ?\<rho> x)" by auto
          }
          then show ?thesis by auto
        qed
        also have "... = (Var y \<in> ?\<rho> ` s)" by auto
        also have "... = ?l" unfolding s ..
        finally show ?thesis by simp
      qed
    } note dom = this
    show ?case unfolding q pat_termI.simps
      unfolding pat_equivalence_lem_4[OF ren, of n]
    proof (intro subst_eq subst_eq2, rule refl, rule refl)
      show "(\<lambda> y. if Var y \<in> ?\<rho> ` subst_domain ?\<sigma> then Var y \<cdot> is_inverse_renaming ?\<rho> \<cdot> ?\<sigma> \<cdot> ?\<rho> else Var y) = ?m ?\<sigma>'" unfolding mk_subst_case
        by (rule lambda, rule if_c, rule dom, auto)
    next
      show "(\<lambda> y. if Var y \<in> ?\<rho> ` subst_domain ?\<mu> then Var y \<cdot> is_inverse_renaming ?\<rho> \<cdot> ?\<mu> \<cdot> is_inverse_renaming ?\<rho> else Var y \<cdot> is_inverse_renaming ?\<rho>) = ?m ?\<mu>'"
        unfolding mk_subst_case
        by (rule lambda, rule if_c, rule dom, auto)
    qed
  qed 
qed

(* datatype for certificates of pattern rules *)
datatype pat_rule_pos = Pat_Base | Pat_Pump | Pat_Close

datatype ('f,'v) pat_rule_prf = 
  Pat_OrigRule "('f, 'v) rule" bool
| Pat_InitPump "('f, 'v) pat_rule_prf" "('f, 'v) substL" "('f, 'v) substL"
| Pat_InitPumpCtxt "('f, 'v) pat_rule_prf" "('f, 'v) substL" pos 'v
| Pat_Equiv "('f, 'v) pat_rule_prf" bool "('f, 'v) pat_eqv_prf"
| Pat_Narrow "('f, 'v) pat_rule_prf" "('f, 'v) pat_rule_prf" pos
| Pat_Inst "('f, 'v) pat_rule_prf" "('f, 'v) substL" pat_rule_pos
| Pat_Rewr "('f, 'v) pat_rule_prf" "('f, 'v) term \<times> ('f, 'v) rseq" pat_rule_pos 'v 
| Pat_Exp_Sigma "('f, 'v) pat_rule_prf" nat


type_synonym ('f, 'v) pat_ruleI = "('f, 'v) pat_termI \<times> ('f, 'v) pat_termI \<times> bool"

fun pat_rule_of :: "('f, 'v) pat_ruleI \<Rightarrow> ('f, 'v) pat_rule" where "pat_rule_of (p,q,b) = (pat_term_of p, pat_term_of q, b)"

definition showsl_pat_rule :: "('f :: showl, 'v :: showl)pat_ruleI \<Rightarrow> showsl"
  where "showsl_pat_rule pr \<equiv> case pr of (p1,p2,_) \<Rightarrow> showsl_pat_term p1 \<circ> showsl_lit (STR '' --> '') \<circ> showsl_pat_term p2"

(* the function which checks correct application of the inference rules to derive a pattern rule *)
context
  fixes R :: "('f :: showl, 'v :: showl)rules" and P :: "('f,'v)rules"
begin
fun check_pat_rule_prf :: "('f, 'v) pat_rule_prf \<Rightarrow> ('f, 'v) pat_ruleI result"
  where 
  "check_pat_rule_prf (Pat_OrigRule (l,r) isPair) = (
       if isPair then do { check ((l,r) \<in> set P) (showsl_rule (l,r) \<circ> showsl_lit (STR '' is not a pair'')) ; return ((l,[],[]),(r,[],[]),isPair) }
                 else do { check ((l,r) \<in> set R) (showsl_rule (l,r) \<circ> showsl_lit (STR '' is not a rule'')) ; return ((l,[],[]),(r,[],[]),isPair) })"
| "check_pat_rule_prf (Pat_InitPump pat \<sigma> \<theta>) = do {
      ((s,sig,tau),(t,sig',tau'),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        check (sig @ tau @ sig' @ tau' = []) (showsl_lit (STR ''substitutions must be empty''));
        check (s \<cdot> mk_subst Var \<theta> = t \<cdot> mk_subst Var \<sigma>) (showsl_lit (STR ''s theta != t sigma''));
        check (commutes_impl \<theta> \<sigma>) (showsl_lit (STR ''sigma and theta do not commute''));
        return ((s,\<sigma>,[]),(t,\<theta>,[]),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with initial pumping after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,sig,tau),(t,sig',tau'),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_InitPumpCtxt pat \<sigma> p z) = do {
      ((s,sig,tau),(t,sig',tau'),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        check (\<not> b) (showsl_lit (STR ''pairs not allowed in init pump ctxt''));
        check (sig @ tau @ sig' @ tau' = []) (showsl_lit (STR ''substitutions must be empty''));
        check (p \<in> poss t) (showsl_lit (STR ''p is not a valid position''));
        check (s = t |_ p \<cdot> mk_subst Var \<sigma>) (showsl_lit (STR ''s != t |_ p sigma''));
        check (z \<notin> set (vars_term_list s @ vars_term_list t @ vars_subst_impl \<sigma>)) (showsl_lit (STR ''z is not fresh''));
        let tz = replace_at t p (Var z);
        return ((s,\<sigma>,[]),(tz,(z,tz) # \<sigma>,[(z,t |_ p)]),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with initial pumping (with ctxt) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,sig,tau),(t,sig',tau'),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Equiv pat left eqv) = do {
      (pleft,pright,b) \<leftarrow> check_pat_rule_prf pat;
      do { 
        pnew \<leftarrow> check_pat_eqv_prf eqv (if left then pleft else pright);
        return (if left then (pnew,pright,b) else (pleft,pnew,b)) 
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern equivalence after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule (pleft,pright,b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Narrow pat1 pat2 p) = do {
      ((s,\<sigma>,\<mu>),(t,sig,mu),b1) \<leftarrow> check_pat_rule_prf pat1;
      ((u,sig1,mu1),(v,sig2,mu2),b2) \<leftarrow> check_pat_rule_prf pat2;
      do {
        check (subst_eq sig \<sigma> \<and> subst_eq sig1 \<sigma> \<and> subst_eq sig2 \<sigma> \<and> subst_eq mu \<mu> \<and> subst_eq mu1 \<mu> \<and> subst_eq mu2 \<mu>) 
          (showsl_lit (STR ''substitutions are not identical''));
        check (p \<in> poss t) (showsl_lit (STR ''p is not a valid position''));
        check (t |_ p = u) (showsl_lit (STR ''t |_ p != u''));
        check (b2 \<longrightarrow> p = []) (showsl_lit (STR ''there is a P step, so p must be epsilon''));
        return ((s,\<sigma>,\<mu>),(replace_at t p v,\<sigma>,\<mu>),b1 \<or> b2)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern narrowing after deriving correct pattern rules\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>,\<mu>),(t,sig,mu),b1)
                  \<circ> showsl_lit (STR ''\<newline>and\<newline>'') \<circ> showsl_pat_rule
                  ((u,sig1,mu1),(v,sig2,mu2),b2)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Inst pat \<rho> Pat_Base) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        let xs = map fst (mk_subst_domain \<sigma>s @ mk_subst_domain \<mu>s @ mk_subst_domain \<sigma>t @ mk_subst_domain \<mu>t);
        check_allm (\<lambda> x. check (x \<notin> set xs) (showsl_lit (STR ''domains not disjoint''))) (vars_subst_impl \<rho>);
        let \<rho>' = mk_subst Var \<rho>;
        return ((s \<cdot> \<rho>',subst_compose'_impl \<sigma>s \<rho>',subst_compose'_impl \<mu>s \<rho>'),(t \<cdot> \<rho>',subst_compose'_impl \<sigma>t \<rho>',subst_compose'_impl \<mu>t \<rho>'),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern instantiation (base) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Inst pat \<rho> Pat_Pump) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        check (commutes_impl \<rho> \<sigma>s) (showsl_lit (STR ''rho does not commute with sigma_s''));
        check (commutes_impl \<rho> \<mu>s) (showsl_lit (STR ''rho does not commute with mu_s''));
        check (commutes_impl \<rho> \<sigma>t) (showsl_lit (STR ''rho does not commute with sigma_t''));
        check (commutes_impl \<rho> \<mu>t) (showsl_lit (STR ''rho does not commute with mu_t''));
        return ((s,subst_compose_impl \<sigma>s \<rho>,\<mu>s),(t,subst_compose_impl \<sigma>t \<rho>, \<mu>t),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern instantiation (pumping) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Inst pat \<rho> Pat_Close) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      return ((s,\<sigma>s,subst_compose_impl \<mu>s \<rho>),(t,\<sigma>t,subst_compose_impl \<mu>t \<rho>),b)
   }"
| "check_pat_rule_prf (Pat_Rewr pat rewr Pat_Base _) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        let (t',rseq) = rewr;
        let t'' = last (t' # map (\<lambda> (_,_,t). t) rseq);
        check (t = t') (showsl_lit (STR ''terms t do not match''));
        check_rsteps R rseq t' t'';
        return ((s,\<sigma>s,\<mu>s),(t'',\<sigma>t,\<mu>t),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern rewriting (base) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Rewr pat rewr Pat_Pump x) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        let (t',rseq) = rewr;
        let t'' = last (t' # map (\<lambda> (_,_,t). t) rseq);
        check (mk_subst Var \<sigma>t x = t') (showsl_lit (STR ''sigma_t x does not match starting term''));
        check_rsteps R rseq t' t'';
        return ((s,\<sigma>s,\<mu>s),(t,subst_replace_impl \<sigma>t x t'',\<mu>t),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern rewriting (pumping) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Rewr pat rewr Pat_Close x) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      do {
        let (t',rseq) = rewr;
        let t'' = last (t' # map (\<lambda> (_,_,t). t) rseq);
        check (mk_subst Var \<mu>t x = t') (showsl_lit (STR ''sigma_t x does not match starting term''));
        check_rsteps R rseq t' t'';
        return ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,subst_replace_impl \<mu>t x t''),b)
      } <+? (\<lambda> e. showsl_lit (STR ''problem with pattern rewriting (closing) after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)
                  \<circ> e)
   }"
| "check_pat_rule_prf (Pat_Exp_Sigma pat k) = do {
      ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<leftarrow> check_pat_rule_prf pat;
      return ((s \<cdot> (mk_subst Var (subst_power_impl \<sigma>s k)),\<sigma>s,\<mu>s),(t \<cdot> (mk_subst Var (subst_power_impl \<sigma>t k)),\<sigma>t,\<mu>t),b)
   }"

(* and its correctness *)
lemma check_pat_rule_prf:
  assumes "check_pat_rule_prf prf = return p"
  shows "pat_rule_of p \<in> fixed_trs.pat_rule (set R) (set P)"
proof -
  note d = pat_rule_of.simps pat_term_of.simps
  interpret fixed_trs "set R" "set P" .
  show ?thesis using assms
  proof (induct "prf" arbitrary: p rule: check_pat_rule_prf.induct)
    case (1 l r isPair p)
    show ?case 
    proof (cases isPair)
      case True
      with 1 have p: "p = ((l,[],[]),(r,[],[]),True)" and lr: "(l,r) \<in> set P"
        by auto
      show ?thesis unfolding p d mk_subst_Nil
        by (rule pat_rule_I_P[OF lr])
    next
      case False
      with 1 have p: "p = ((l,[],[]),(r,[],[]),False)" and lr: "(l,r) \<in> (set R)"
        by auto
      show ?thesis unfolding p d mk_subst_Nil
        by (rule pat_rule_I_R[OF lr])
    qed
  next
    case (2 pat \<sigma> \<theta> p)
    let ?p = "check_pat_rule_prf pat"
    note simp = 2(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s sig tau t sig' tau' b where pp: "pp = ((s,sig,tau),(t,sig',tau'),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified]
    from simp have pp: "pp = ((s,[],[]),(t,[],[]),b)" "p = ((s,\<sigma>,[]),(t,\<theta>,[]),b)" unfolding pp by auto
    note IH =  2(1)[OF p, unfolded pp]
    show ?case unfolding pp d mk_subst_Nil
      by (rule pat_rule_II, insert simp IH, auto)
  next
    case (3 pat \<sigma> po z)
    let ?p = "check_pat_rule_prf pat"
    note simp = 3(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s sig tau t sig' tau' b where pp: "pp = ((s,sig,tau),(t,sig',tau'),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    let ?tz = "replace_at t po (Var z)"
    from simp have pp: "pp = ((s,[],[]),(t,[],[]),False)" "p = ((s,\<sigma>,[]),(?tz,(z,?tz) # \<sigma>,[(z,t |_ po)]),False)" unfolding pp by auto
    note IH =  3(1)[OF p, unfolded pp d mk_subst_Nil]
    from simp have po: "po \<in> poss t" by auto
    from simp have subt: "s = t |_ po \<cdot> mk_subst Var \<sigma>" by simp
    from simp have z: "z \<notin> vars_term s \<union> vars_term t \<union> vars_subst (mk_subst Var \<sigma>)" by auto
    let ?\<tau> = "\<lambda> u. mk_subst Var ((z, u) # \<sigma>)"
    let ?\<tau>' = "\<lambda> u. (mk_subst Var \<sigma>) (z := u)"
    have \<tau>: "\<And> u. ?\<tau> u = ?\<tau>' u" unfolding mk_subst_def by auto
    note main = pat_rule_III[OF IH po subt z]
    show ?case unfolding pp d mk_subst_Nil using main unfolding \<tau> 
      by simp
  next
    case (4 pat left eqv p)
    let ?p = "check_pat_rule_prf pat"
    note simp = 4(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain pleft pright b where pp: "pp = (pleft,pright,b)"
      by (cases pp, force+)
    let ?p = "if left then pleft else pright"
    obtain pold where pold: "pold = ?p" by auto
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    from simp pold obtain pnew where ppp: "check_pat_eqv_prf eqv pold = Inr pnew" 
      by (cases "check_pat_eqv_prf eqv pold") auto
    from check_pat_eqv_prf[OF this] have id: "pat_termI pold = pat_termI pnew" by auto
    let ?res = "(if left then pnew else pleft, if left then pright else pnew, b)"
    from simp[unfolded ppp[unfolded pold]] have res: "p = ?res"
      by (cases left) (auto)
    note IH = 4(1)[OF p, unfolded pp d]
    note main = pat_rule_IV[OF IH]
    {
      fix n
      have id: "pat_term (pat_term_of pold) n = pat_term (pat_term_of pnew) n"
        using arg_cong[OF id, of "\<lambda> x. x n"] 
        by (cases pold, cases pnew, auto simp: pat_term_def)
    } note id = this
    show ?case unfolding res d
    proof (rule main)
      fix n 
      show "pat_term (pat_term_of pleft) n = 
        pat_term (pat_term_of (if left then pnew else pleft)) n" (is "?l = ?r")
      proof (cases left)
        case False
        then show ?thesis by simp
      next
        case True
        then have "?l = pat_term (pat_term_of pold) n" using pold by simp
        also have "... = pat_term (pat_term_of pnew) n" using id by simp
        also have "... = ?r" using True by simp
        finally show ?thesis by auto
      qed
    next
      fix n 
      show "pat_term (pat_term_of pright) n = 
        pat_term (pat_term_of (if left then pright else pnew)) n" (is "?l = ?r")
      proof (cases "\<not> left")
        case False
        then show ?thesis by simp
      next
        case True
        then have "?l = pat_term (pat_term_of pold) n" using pold by simp
        also have "... = pat_term (pat_term_of pnew) n" using id by simp
        also have "... = ?r" using True by simp
        finally show ?thesis by auto
      qed
    qed
  next
    case (5 pat1 pat2 po)
    let ?p1 = "check_pat_rule_prf pat1"
    let ?p2 = "check_pat_rule_prf pat2"
    note simp = 5(3)[simplified]
    from simp obtain pp1 where p1: "?p1 = Inr pp1" by (cases ?p1, auto)
    obtain s \<sigma> \<mu> t sig mu b1 where pp1: "pp1 = ((s,\<sigma>,\<mu>),(t,sig,mu),b1)"
      by (cases pp1, force+)
    note simp = simp[unfolded p1 pp1, simplified]
    from simp obtain pp2 where p2: "?p2 = Inr pp2" by (cases ?p2, auto)
    obtain u sig2 mu2 v sig3 mu3 b2 where pp2: "pp2 = ((u,sig2,mu2),(v,sig3,mu3),b2)"
      by (cases pp2, force+)
    note simp = simp[unfolded p2 pp2, simplified]
    from simp have id_sig: "mk_subst Var sig = mk_subst Var \<sigma>" "mk_subst Var sig2 = mk_subst Var \<sigma>" "mk_subst Var sig3 = mk_subst Var \<sigma>" by auto
    from simp have id_mu: "mk_subst Var mu = mk_subst Var \<mu>" "mk_subst Var mu2 = mk_subst Var \<mu>" "mk_subst Var mu3 = mk_subst Var \<mu>" by auto
    from simp have po: "po \<in> poss t" by auto
    from simp have subt: "t |_ po = u" by simp
    from simp have b2: "b2 \<Longrightarrow> po = []" by auto
    note IH1 =  5(1)[OF p1, unfolded pp1 d id_sig id_mu]
    note IH2 =  5(2)[OF p1, unfolded pp1, OF refl refl refl p2, unfolded pp2 d id_sig id_mu]
    note main = pat_rule_VI[OF IH1 IH2 po subt b2]
    show ?case using simp main by auto
  next
    case (6 pat \<rho>)
    let ?p = "check_pat_rule_prf pat"
    note simp = 6(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    note IH =  6(1)[OF p, unfolded pp d]
    note main = pat_rule_V[OF IH, of "mk_subst Var \<rho>"]
    let ?\<rho> = "\<lambda> \<sigma>. subst_compose' (mk_subst Var \<sigma>) (mk_subst Var \<rho>)"
    from simp have p: "pat_rule_of p = ((s \<cdot> mk_subst Var \<rho>, ?\<rho> \<sigma>s, ?\<rho> \<mu>s),(t \<cdot> mk_subst Var \<rho>, ?\<rho> \<sigma>t, ?\<rho> \<mu>t),b)" by auto
    show ?case unfolding p 
      by (rule main, insert simp, auto simp: mk_subst_domain)
  next
    case (7 pat \<rho>)
    let ?p = "check_pat_rule_prf pat"
    note simp = 7(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    note IH =  7(1)[OF p, unfolded pp d]
    note main = pat_rule_VII[OF IH, of "mk_subst Var \<rho>"]
    from simp have p: "pat_rule_of p = ((s, subst_compose (mk_subst Var \<sigma>s) (mk_subst Var \<rho>), mk_subst Var \<mu>s),(t, subst_compose (mk_subst Var \<sigma>t) (mk_subst Var \<rho>), mk_subst Var \<mu>t),b)" by auto
    show ?case unfolding p 
      by (rule main, insert simp, auto simp: mk_subst_domain)
  next
    case (8 pat \<rho>)
    let ?p = "check_pat_rule_prf pat"
    note simp = 8(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    note IH =  8(1)[OF p, unfolded pp d]
    note main = pat_rule_VIII[OF IH, of "mk_subst Var \<rho>"]
    from simp have p: "pat_rule_of p = ((s, mk_subst Var \<sigma>s, subst_compose (mk_subst Var \<mu>s) (mk_subst Var \<rho>)),(t, mk_subst Var \<sigma>t, subst_compose (mk_subst Var \<mu>t) (mk_subst Var \<rho>)),b)" by auto
    show ?case unfolding p 
      by (rule main)
  next
    case (9 pat rewr x p)
    obtain t' rseq where rewr: "rewr = (t',rseq)" by force
    obtain t'' where t'': "t'' = last (t' # map (\<lambda>(_,_,t). t) rseq)" by auto
    let ?p = "check_pat_rule_prf pat"
    note simp = 9(2)[simplified] t''
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp rewr, simplified, unfolded Let_def, simplified]
    note IH =  9(1)[OF p, unfolded pp d]
    note main = pat_rule_IX[OF IH, of t'' "mk_subst Var \<sigma>t" "mk_subst Var \<mu>t"]
    from simp have p: "pat_rule_of p = ((s, mk_subst Var \<sigma>s, mk_subst Var \<mu>s),(t'', mk_subst Var \<sigma>t, mk_subst Var \<mu>t),b)" by auto
    show ?case unfolding p 
      by (rule main, rule check_rsteps_sound_star[of _ rseq], insert simp, auto)
  next
    case (10 pat rewr x p)
    obtain t' rseq where rewr: "rewr = (t',rseq)" by force
    obtain t'' where t'': "t'' = last (t' # map (\<lambda>(_,_,t). t) rseq)" by auto
    let ?p = "check_pat_rule_prf pat"
    note simp = 10(2)[simplified] 
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp rewr, simplified, unfolded Let_def, simplified]
    from simp have id: "p = ((s,\<sigma>s,\<mu>s),(t,subst_replace_impl \<sigma>t x t'',\<mu>t),b)" unfolding t'' by simp
    note IH = 10(1)[OF p, unfolded pp d]
    let ?\<tau> = "\<lambda> y. if x = y then t'' else mk_subst Var \<sigma>t y"
    note main = pat_rule_IX[OF IH, of t ?\<tau> "mk_subst Var \<mu>t"]
    have p: "pat_rule_of p = ((s, mk_subst Var \<sigma>s, mk_subst Var \<mu>s),(t, ?\<tau>, mk_subst Var \<mu>t),b)"
      unfolding id by simp
    show ?case unfolding p 
      by (rule main, insert simp t'', auto intro: check_rsteps_sound_star)
  next
    case (11 pat rewr x p)
    obtain t' rseq where rewr: "rewr = (t',rseq)" by force
    obtain t'' where t'': "t'' = last (t' # map (\<lambda>(_,_,t). t) rseq)" by auto
    let ?p = "check_pat_rule_prf pat"
    note simp = 11(2)[simplified] 
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp rewr, simplified, unfolded Let_def, simplified]
    note IH = 11(1)[OF p, unfolded pp d]
    let ?\<tau> = "\<lambda> y. if x = y then t'' else mk_subst Var \<mu>t y"
    note main = pat_rule_IX[OF IH, of t "mk_subst Var \<sigma>t" ?\<tau>]
    from simp have id: "p = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,subst_replace_impl \<mu>t x t''),b)" unfolding t'' by simp
    have p: "pat_rule_of p = ((s, mk_subst Var \<sigma>s, mk_subst Var \<mu>s),(t, mk_subst Var \<sigma>t, ?\<tau>),b)" unfolding id by simp
    show ?case unfolding p 
      by (rule main, insert simp t'', auto intro: check_rsteps_sound_star)
  next
    case (12 pat k p)
    let ?p = "check_pat_rule_prf pat"
    note simp = 12(2)[simplified]
    from simp obtain pp where p: "?p = Inr pp" by (cases ?p, auto)
    obtain s \<sigma>s \<mu>s t \<sigma>t \<mu>t b where pp: "pp = ((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b)"
      by (cases pp, force+)
    note simp = simp[unfolded p pp, simplified, unfolded Let_def, simplified]
    note IH = 12(1)[OF p, unfolded pp d]
    note main = pat_rule_X[OF IH, of k]
    from simp have p: "pat_rule_of p = ((s \<cdot> mk_subst Var \<sigma>s ^^ k, mk_subst Var \<sigma>s, mk_subst Var \<mu>s),(t \<cdot> mk_subst Var \<sigma>t ^^ k, mk_subst Var \<sigma>t, mk_subst Var \<mu>t),b)" by auto
    show ?case unfolding p 
      by (rule main)
  qed
qed
end

datatype ('f,'v) non_loop_prf =
  Non_loop_prf "('f, 'v) pat_rule_prf" "('f, 'v) substL" "('f, 'v) substL" nat nat pos

(* function which checks preconditions of Theorem 8 *)
fun check_non_loop_prf :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f :: showl, 'v :: showl)non_loop_prf \<Rightarrow> showsl check"
  where "check_non_loop_prf R P (Non_loop_prf pat \<sigma>' \<mu>' m b p) = (do {
      ((s,\<sigma>,\<mu>),(t,\<sigma>t,\<mu>t),is_pair) \<leftarrow> check_pat_rule_prf R P pat;
      do {
        check (is_pair \<longrightarrow> p = []) (showsl_lit (STR ''p must be empty, since pairs are contained''));
        check (commutes_impl \<sigma> \<sigma>') (showsl_lit (STR ''sigma and sigma' do not commute''));
        check (commutes_impl \<mu> \<sigma>') (showsl_lit (STR ''mu and sigma' do not commute''));
        check (subst_eq \<sigma>t (subst_compose_impl (subst_power_impl \<sigma> m)  \<sigma>')) (showsl_lit (STR ''sigma_t != sigma^m sigma' ''));
        check (subst_eq \<mu>t (subst_compose_impl \<mu> \<mu>')) (showsl_lit (STR ''mu_t != mu mu' ''));
        check (p \<in> poss t) (showsl_lit (STR ''p is not a position in t''));
        check (s \<cdot> mk_subst Var (subst_power_impl \<sigma> b) = t |_ p) (showsl_lit (STR ''s sigma^b != t |_ p''))
      } <+? (\<lambda> e. showsl_lit (STR ''problem with application condition of non-loop theorem after deriving correct pattern rule\<newline>'') 
                  \<circ> showsl_pat_rule ((s,\<sigma>,\<mu>),(t,\<sigma>t,\<mu>t),is_pair)
                  \<circ> e)
   } )" 

(* and its soundness proof *)
lemma check_non_loop_prf: assumes ok: "isOK(check_non_loop_prf R P prf)"
  shows "\<not> SN (rstep (set R) \<union> rrstep (set P))"
proof -
  interpret fixed_trs "set R" "set P" .
  obtain pat \<sigma>' \<mu>' m b p where Prf: "prf = Non_loop_prf pat \<sigma>' \<mu>' m b p"
    by (cases "prf", blast)
  note ok = ok[unfolded Prf, simplified]
  let ?ch = "check_pat_rule_prf R P pat"
  from ok have "isOK(?ch)" by simp
  then obtain pat1 pat2 is_pair where ch: "?ch = return (pat1,pat2,is_pair)"
    by (cases ?ch, force+)
  obtain s \<sigma> \<mu> where pat1: "pat1 = (s,\<sigma>,\<mu>)" by (cases pat1, auto)
  obtain t \<sigma>t \<mu>t where pat2: "pat2 = (t,\<sigma>t,\<mu>t)" by (cases pat2, auto)
  let ?m = "mk_subst Var"
  let ?\<sigma> = "?m \<sigma>"
  let ?\<mu> = "?m \<mu>"
  let ?\<sigma>t = "?m \<sigma>t"
  let ?\<mu>t = "?m \<mu>t"
  let ?\<sigma>p = "?m \<sigma>'"
  let ?\<mu>p = "?m \<mu>'"
  note ok = ok[unfolded ch pat1 pat2, simplified]
  note ch = ch[unfolded pat1 pat2]
  have pat: "((s,?\<sigma>,?\<mu>),(t,?\<sigma>t,?\<mu>t),is_pair) \<in> pat_rule" 
    using check_pat_rule_prf[OF ch] by simp
  show ?thesis
    by (rule pat_rule_imp_non_term_PR[OF pat, of m ?\<sigma>p ?\<mu>p p b],
      insert ok, auto) 
qed

(* it remains to wrap this function for methods on DP problems and on TRSs *)
definition "check_non_loop_dp_prf I dpp prf \<equiv> do {
  let P    = dpp_ops.pairs I dpp;
  let R    = dpp_ops.rules I dpp;
  check (dpp_ops.Q I dpp = []) (showsl_lit (STR ''strategy for non-loops unsupported''));
  check_non_loop_prf R P prf}"

lemma check_non_loop_dp_prf:
  assumes ok: "isOK (check_non_loop_dp_prf I dpp prf)"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  let ?P = "dpp_ops.pairs I dpp"
  let ?R = "dpp_ops.rules I dpp"
  let ?Q = "dpp_ops.Q I dpp"
  note ok = ok[unfolded check_non_loop_dp_prf_def Let_def]
  from ok have Q: "?Q = []" by auto
  from ok have "isOK(check_non_loop_prf ?R ?P prf)" by auto
  from check_non_loop_prf[OF this] Q show ?thesis
    unfolding infinite_dpp_not_SN_conv Un_commute[of "rstep (set ?R)"] by auto
qed

definition "check_non_loop_trs_prf I tp prf \<equiv> do {
  let R    = tp_ops.rules I tp;
  check (tp_ops.Q I tp = []) (showsl_lit (STR ''strategy for non-loops unsupported''));
  check_non_loop_prf R [] prf}"

lemma check_non_loop_trs_prf:
  assumes ok: "isOK (check_non_loop_trs_prf I tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  let ?R = "tp_ops.rules I tp"
  let ?Q = "tp_ops.Q I tp"
  note ok = ok[unfolded check_non_loop_trs_prf_def Let_def]
  from ok have Q: "?Q = []" by auto
  from ok have "isOK(check_non_loop_prf ?R [] prf)" by auto
  from check_non_loop_prf[OF this] Q show ?thesis by auto
qed

end
