(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generalized_Usable_Rules
  imports
    TRS.QDP_Framework
    Auxx.Name
    Ord.Non_Inf_Order
    TRS.Signature_Extension
    Dependency_Graph
    First_Order_Terms.Term_More
    Countable_Term
begin

section \<open>generalized usable rules\<close>

fun compat_root where 
  "compat_root _ (Var _) = False"
| "compat_root (Var _) l = False"
| "compat_root fls gts = (root fls = root gts)"


locale fixed_trs_dep =
  fixes \<pi> :: "'f dep"
  and R :: "('f,'v)trs"
  and Q :: "('f,'v)terms"
  and nfs :: bool
begin

abbreviation NFQ where "NFQ \<equiv> NF_terms Q"

text \<open>same definition as in CADE07 "Bounded Increase" paper, except that we define
  the usable rules of a term as a predicate instead of a set.\<close>

inductive gen_usable_rule :: "('f,'v)term \<Rightarrow> ('f,'v)rule \<Rightarrow> bool"
where in_R: "(l,r) \<in> R \<Longrightarrow> compat_root l t \<Longrightarrow> gen_usable_rule t (l,r)"
   |  in_U: "(l,r) \<in> R \<Longrightarrow> compat_root l t \<Longrightarrow> gen_usable_rule r lr \<Longrightarrow> gen_usable_rule t lr"
   |  in_arg: "i < length ts \<Longrightarrow> gen_usable_rule (ts ! i) lr \<Longrightarrow> lr' \<in> {lr} ^^^ \<pi> (f,length ts) i \<Longrightarrow> gen_usable_rule (Fun f ts) lr'"

definition gen_usable_rules :: "('f, 'v) term \<Rightarrow> ('f, 'v) trs" where
  "gen_usable_rules t = {lr. gen_usable_rule t lr}"
  
definition gen_usable_rules_pairs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "gen_usable_rules_pairs P = \<Union>(gen_usable_rules ` snd ` P)"

lemma gen_usable_rulesI[intro]: "gen_usable_rule t lr \<Longrightarrow> lr \<in> gen_usable_rules t"
  unfolding gen_usable_rules_def by auto

lemma gen_usable_rulesE[elim]: "lr \<in> gen_usable_rules t \<Longrightarrow> gen_usable_rule t lr"
  unfolding gen_usable_rules_def by auto

text \<open>a recursive version of usable rules
  (easier to use, but does not reflect that inductive sets correspond to \emph{least} fixpoint)\<close>
lemma gen_usable_rules_Fun: "gen_usable_rules (Fun f ts) = 
  {(Fun f ls,r) | ls r. (Fun f ls,r) \<in> R \<and> length ls = length ts} \<union>
  \<Union> { gen_usable_rules r | ls r. (Fun f ls,r) \<in> R \<and> length ls = length ts} \<union>
  \<Union> { gen_usable_rules (ts ! i) ^^^ \<pi> (f,length ts) i | i. i < length ts}" (is "?L = ?R1 \<union> ?R2 \<union> ?R3")
proof (rule equalityI) 
  let ?R = "?R1 \<union> ?R2 \<union> ?R3"
  {
    fix l r
    assume "(l,r) \<in> ?L"
    then have "gen_usable_rule (Fun f ts) (l,r)" by auto
    then have "(l,r) \<in> ?R" 
    proof(cases)
      case in_R
      from in_R(2) obtain ls where l: "l = Fun f ls" by (cases l, auto)
      with in_R show ?thesis by auto
    next
      case (in_U l2 r2)
      from in_U(2) obtain ls where l2: "l2 = Fun f ls" by (cases l2, auto)
      with in_U show ?thesis by auto
    next
      case (in_arg i lr)
      then have "(l, r) \<in> {lr. gen_usable_rule (ts ! i) lr} ^^^ \<pi> (f, length ts) i"
        by (cases "\<pi> (f,length ts) i", auto)
      then show ?thesis using in_arg(1) unfolding gen_usable_rules_def by auto
    qed
  } 
  then show "?L \<subseteq> ?R" ..
  moreover
  {
    fix l r
    assume "(l,r) \<in> ?R"
    then have "(l,r) \<in> ?R1 \<or> (l,r) \<in> ?R2 \<or> (l,r) \<in> ?R3" by blast
    then have "(l,r) \<in> ?L"
    proof
      assume "(l,r) \<in> ?R1"
      with in_R[of l r] show "(l,r) \<in> ?L" by auto
    next
      assume "(l,r) \<in> ?R2 \<or> (l,r) \<in> ?R3"
      then show ?thesis
      proof
        assume "(l,r) \<in> ?R2"
        then obtain ls r2 where U: "(l,r) \<in> gen_usable_rules r2" 
          and R: "(Fun f ls, r2) \<in> R" and l: "length ls = length ts" by auto
        from in_U[OF R _ gen_usable_rulesE[OF U]] l
        show ?thesis by auto
      next
        assume "(l,r) \<in> ?R3"
        then obtain i where i: "i < length ts"
          and lr: "(l,r) \<in> gen_usable_rules (ts ! i) ^^^ \<pi> (f,length ts) i" by auto
        then obtain lr' where u: "gen_usable_rule (ts ! i) lr'" and lr: "(l,r) \<in> {lr'} ^^^ \<pi> (f,length ts) i"
          unfolding gen_usable_rules_def by (cases "\<pi> (f,length ts) i", auto)
        show "(l,r) \<in> ?L"
          by (intro gen_usable_rulesI, rule in_arg[OF i u lr])
      qed
    qed
  } 
  then show "?R \<subseteq> ?L" ..
qed

lemma gen_usable_rules_Var: "gen_usable_rules (Var x) = {}"
proof -
  {
    fix l r
    assume "(l,r) \<in> gen_usable_rules (Var x)"
    then have "gen_usable_rule (Var x) (l,r)" ..
    then have False by (cases, auto)
  }
  then show ?thesis by auto
qed  
    
lemma gen_usable_rules_subst: "gen_usable_rules t \<subseteq> gen_usable_rules (t \<cdot> \<sigma>)"
proof (induct t)
  case (Var x)
  then show ?case by (simp add: gen_usable_rules_Var)
next
  case (Fun f ts)
  {
    fix i
    assume i: "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    from Fun[OF this] i
    have "gen_usable_rules (ts ! i) ^^^ \<pi> (f, length ts) i \<subseteq> 
      gen_usable_rules (map (\<lambda>t. t \<cdot> \<sigma>) ts ! i) ^^^ \<pi> (f, length ts) i" (is "?l \<subseteq> _")
      by (intro rel_dep_mono, auto)
    also have "... \<subseteq> \<Union>{gen_usable_rules (map (\<lambda>t. t \<cdot> \<sigma>) ts ! i) ^^^ \<pi> (f, length ts) i |i. i < length ts}"
      (is "_ \<subseteq> ?r")
      using i by auto
    finally have "?l \<subseteq> ?r" .
  } note main = this
  show ?case unfolding eval_term.simps gen_usable_rules_Fun
    by (insert main, auto) 
qed

text \<open>
  a helpful lemma to be used in an induction on the term structure, to show
  that the usable rules of the one term are a subset of those of another term.
\<close>
lemma gen_usable_rules_split: "\<exists> k. \<forall> s t. gen_usable_rules s ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<longrightarrow>
  gen_usable_rules (Fun f (b @ s # a)) \<subseteq> gen_usable_rules (Fun f (b @ t # a))" 
proof -
  let ?i = "length b"
  let ?n = "Suc (?i + length a)"
  let ?\<pi> = "\<pi> (f,?n) ?i"
  let ?all = "\<lambda> t. gen_usable_rules (Fun f (b @ t # a))"
  let ?coll = "\<lambda> t. \<Union>((\<lambda> i. gen_usable_rules ((b @ t # a) ! i) ^^^ \<pi> (f,?n) i) ` {i . i < ?n})"
  let ?single = "\<lambda> t. gen_usable_rules t ^^^ \<pi> (f,?n) ?i"
  have id: "{i. i < ?n} = {i. i < ?i} \<union> {?i} \<union> {Suc ?i + k | k. Suc ?i + k < ?n}" (is "_ = ?ib \<union> ?ii \<union> ?ia") by (auto, presburger)
  { 
    fix s t
    have "?all s - ?all t \<subseteq> ?coll s - ?coll t" 
      unfolding gen_usable_rules_Fun by auto
    also have "\<dots> \<subseteq> ?single s - ?single t" unfolding id by (auto simp: nth_append)
    finally have "?all s - ?all t \<subseteq> ?single s - ?single t" .
  } note sub = this
  have "\<exists> k. \<forall> s t. gen_usable_rules s ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<longrightarrow> ?single s - ?single t = {}"
  proof (cases ?\<pi>)
    case Ignore
    then show ?thesis by auto
  next
    case Increase
    show ?thesis
      by (rule exI[of _ Increase], insert Increase, auto)
  next
    case Decrease
    show ?thesis
      by (rule exI[of _ Decrease], insert Decrease, auto)
  next
    case Wild
    show ?thesis
      by (rule exI[of _ Wild], insert Wild, auto)
  qed
  then obtain k where "\<And> s t. gen_usable_rules s ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<Longrightarrow> ?single s - ?single t = {}" by auto
  with sub have "\<And> s t. gen_usable_rules s ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<Longrightarrow> ?all s \<subseteq> ?all t" by blast
  then show "\<exists> k. \<forall> s t. gen_usable_rules s ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<longrightarrow> ?all s \<subseteq> ?all t" by auto
qed
end

locale fixed_trs_dep_order = fixed_trs_dep \<pi> R Q nfs + non_inf_order_trs S NS F \<pi>
  for \<pi> :: "('f :: countable) dep"
  and R :: "('f,'v :: countable)trs"
  and Q :: "('f,'v)terms"
  and F :: "'f sig"
  and S :: "('f,'v)trs"
  and NS :: "('f,'v)trs"
  and nfs :: bool
  and m :: bool
  + fixes const :: 'f
  assumes wwf: "wwf_qtrs Q R"
  and NFQ: "NF_terms Q \<subseteq> NF_trs R"
  and infinite_V: "infinite (UNIV :: 'v set)"
  and RF: "funas_trs R \<subseteq> F"
  and QF: "\<Union>(funas_term ` Q) \<subseteq> F"
begin

lemma main_technical_lemma: 
  assumes step: "(t \<cdot> \<sigma>,v) \<in> qrstep nfs Q R"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and tsigF: "funas_term (t \<cdot> \<sigma>) \<subseteq> F \<or> funas_args_term (t \<cdot> \<sigma>) \<subseteq> F \<and> \<not> defined (applicable_rules Q R) (the (root (t \<cdot> \<sigma>)))"
  shows "(gen_usable_rules t ^^^ k \<subseteq> NS \<longrightarrow> {(t \<cdot> \<sigma>, v)} ^^^ k \<subseteq> NS) \<and> (\<exists> u \<sigma>'. v = u \<cdot> \<sigma>' 
    \<and> gen_usable_rules u ^^^ k \<subseteq> gen_usable_rules t ^^^ k \<and> \<sigma>' ` vars_term u \<subseteq> NFQ)"
  using step \<sigma> tsigF
proof (induction t arbitrary: v k)
  case (Var x v k)
  from Var.prems(2) NFQ have "Var x \<cdot> \<sigma> \<in> NF_trs R" by auto
  moreover from Var.prems(1) have "(Var x \<cdot> \<sigma>, v) \<in> rstep R" by auto
  ultimately have False by auto
  then show ?case by auto
next
  case (Fun f ts v k)
  note switch = wwf_qtrs_imp_nfs_switch[OF wwf]
  from qrstepE[OF Fun.prems(1)[unfolded switch[of nfs True]]]
    obtain C \<sigma>' l r where
    nf: "\<forall>u\<lhd>l \<cdot> \<sigma>'. u \<in> NFQ" and 
    lr: "(l, r) \<in> R" and 
    t: "Fun f ts \<cdot> \<sigma> = C\<langle>l \<cdot> \<sigma>'\<rangle>" and 
    v: "v = C\<langle>r \<cdot> \<sigma>'\<rangle>" and 
    nfs: "NF_subst True (l, r) \<sigma>' Q" .
  let ?\<sigma>' = "map (\<lambda> t. t \<cdot> \<sigma>')"
  let ?\<sigma> = "map (\<lambda> t. t \<cdot> \<sigma>)"
  from wwf_qtrs_imp_left_fun[OF wwf lr] obtain g ls where l: "l = Fun g ls" by auto
  from wwf only_applicable_rules[OF nf] lr
  have vars_lr: "vars_term r \<subseteq> vars_term l" unfolding wwf_qtrs_def by auto
  from RF lr have rF: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def] by force
  show ?case
  proof (cases C)
    case Hole
    from t Hole have t: "Fun f ts \<cdot> \<sigma> = l \<cdot> \<sigma>'" by simp
    from only_applicable_rules[OF nf, of r] lr l
    have defg: "defined (applicable_rules Q R) (g,length ls)" unfolding defined_def applicable_rules_def 
      by force
    from v Hole have v: "v = r \<cdot> \<sigma>'" by simp
    from l t have gf: "g = f" and id: "?\<sigma> ts = ?\<sigma>' ls" by auto
    from arg_cong[OF id, of length] have len: "length ts = length ls" by simp
    with l t gf have compat: "compat_root l (Fun f ts)" by simp
    from gf defg len have "defined (applicable_rules Q R) (f,length ts)" by simp
    with Fun(4) have "funas_term (Fun f ts \<cdot> \<sigma>) \<subseteq> F" by auto
    with t have "funas_term (l \<cdot> \<sigma>') \<subseteq> F" by simp
    then have \<sigma>'F: "\<Union>(funas_term ` \<sigma>' ` vars_term l) \<subseteq> F" unfolding funas_term_subst by blast
    let ?\<sigma>' = "\<lambda> x. if x \<in> vars_term l then \<sigma>' x else Var x"
    have l_id: "l \<cdot> \<sigma>' = l \<cdot> ?\<sigma>'" by (rule term_subst_eq, simp)
    have r_id: "r \<cdot> \<sigma>' = r \<cdot> ?\<sigma>'" by (rule term_subst_eq, insert vars_lr, auto)
    have \<sigma>'F: "\<Union>(funas_term ` range ?\<sigma>') \<subseteq> F" using \<sigma>'F by auto
    {
      assume ns: "gen_usable_rules (Fun f ts) ^^^ k \<subseteq> NS"
      have "(l,r) \<in> gen_usable_rules (Fun f ts)"
        by (rule gen_usable_rulesI[OF in_R[OF lr compat]])
      then have "{(l,r)} \<subseteq> gen_usable_rules (Fun f ts)" by auto
      from subset_trans[OF rel_dep_mono[OF this] ns]
      have "{(l,r)} ^^^ k \<subseteq> NS" .
      then have "{(l \<cdot> \<sigma>', r \<cdot> \<sigma>')} ^^^ k \<subseteq> (\<lambda> (s,t). (s \<cdot> ?\<sigma>', t \<cdot> ?\<sigma>')) ` NS" 
        unfolding l_id r_id by (cases k, auto)
      also have "(\<lambda> (s,t). (s \<cdot> ?\<sigma>', t \<cdot> ?\<sigma>')) ` NS \<subseteq> NS" using F_subst_closedD[OF stable_NS \<sigma>'F] by auto
      finally have "{(Fun f ts \<cdot> \<sigma>, v)} ^^^ k \<subseteq> NS" using t v by simp
    }
    then have NS: "gen_usable_rules (Fun f ts) ^^^ k \<subseteq> NS \<longrightarrow> {(Fun f ts \<cdot> \<sigma>, v)} ^^^ k \<subseteq> NS" ..
    show ?thesis
    proof (rule conjI[OF NS], intro exI conjI)
      show "v = r \<cdot> ?\<sigma>'" using v r_id by simp
      show "gen_usable_rules r ^^^ k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
        by (rule rel_dep_mono, insert in_U[OF lr compat], auto simp: gen_usable_rules_def)
      show "?\<sigma>' ` vars_term r \<subseteq> NFQ" using vars_lr nfs unfolding NF_subst_def vars_rule_def by auto
    qed
  next
    case (More g bef D aft)
    let ?i' = "length bef"
    let ?tsi' = "ts ! ?i'"
    let ?dl = "D \<langle> l \<cdot> \<sigma>' \<rangle>"
    let ?dr = "D \<langle> r \<cdot> \<sigma>' \<rangle>"
    let ?n' = "Suc (?i' + length aft)"
    from t More have t: "Fun f ts \<cdot> \<sigma> = Fun f (bef @ ?dl # aft)" and gf: "g = f" by auto
    with v More have v: "v = Fun f (bef @ ?dr # aft)" by auto
    from t have "map (\<lambda> t. t \<cdot> \<sigma>) ts = bef @ ?dl # aft" by simp
    from arg_cong[OF this, of length] have len: "length ts = ?n'" by simp
    then have i': "?i' < length ts" by auto
    from id_take_nth_drop[OF i'] obtain tbef taft where ts: "Fun f ts = Fun f (tbef @ ?tsi' # taft)" and tbef: "tbef = take ?i' ts" by auto
    let ?i = "length tbef" let ?n = "Suc (?i + length taft)"
    let ?tsi = "ts ! ?i"
    from tbef i' have llen: "?i' = ?i" by auto
    note ts = ts[unfolded llen]
    note tbef = tbef[unfolded llen]
    note i = i'[unfolded llen]
    from i have mem: "?tsi \<in> set ts" by auto
    from Fun.prems(2) mem have vars: "\<sigma> ` vars_term ?tsi \<subseteq> NFQ" by auto
    from t[unfolded ts] have "?\<sigma> tbef @ (?tsi \<cdot> \<sigma>) # ?\<sigma> taft = bef @ ?dl # aft" by auto
    from this[unfolded append_eq_append_conv_if] 
    have bef: "bef = ?\<sigma> tbef" and tsi: "?tsi \<cdot> \<sigma> =  ?dl"
     and aft: "aft = ?\<sigma> taft" using llen by auto
    from Fun(4) have tF: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term (t \<cdot> \<sigma>) \<subseteq> F"
      by (auto simp: funas_args_term_def)
    from tF[OF mem] have dlF: "funas_term ?dl \<subseteq> F" unfolding tsi .
    with vars_lr rF have drF: "funas_term ?dr \<subseteq> F" by (force simp: funas_term_subst)
    have "(?tsi \<cdot> \<sigma>,?dr) \<in> qrstep True Q R" unfolding tsi
      by (rule qrstepI[OF nf lr _ _ nfs], auto)
    note IH = Fun.IH[OF mem this[unfolded switch[of True nfs]] vars disjI1[OF tF[OF mem]]]
    from Fun(4)[unfolded t bef aft] dlF have fdlF: "funas_args_term (Fun f (?\<sigma> tbef @ ?dl # ?\<sigma> taft)) \<subseteq> F" by (auto simp: funas_args_term_def)
    from Fun(4)[unfolded t bef aft] drF have fdrF: "funas_args_term (Fun f (?\<sigma> tbef @ ?dr # ?\<sigma> taft)) \<subseteq> F" by (auto simp: funas_args_term_def)
    note compat' = dep_compatE[OF dep_compat_NS, of f "?\<sigma> tbef" _ "?\<sigma> taft"]
    note compat_lr = compat'[OF fdlF drF]
    note compat_rl = compat'[OF fdrF dlF]
    note v = v[unfolded bef aft]
    have t: "Fun f ts \<cdot> \<sigma> = Fun f (?\<sigma> tbef @ ?dl # ?\<sigma> taft)" unfolding ts tsi[symmetric]
      by simp
    {
      assume pi: "\<pi> (f,?n) ?i = Increase \<or> \<pi> (f,?n) ?i = Wild"
      have "gen_usable_rules ?tsi ^^^ k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
      proof (rule rel_dep_mono, rule, intro gen_usable_rulesI)
        fix l r
        assume "(l, r) \<in> gen_usable_rules ?tsi"
        note lr = gen_usable_rulesE[OF this]
        show "gen_usable_rule (Fun f ts) (l, r)" unfolding ts
          by (rule in_arg[of ?i _ "(l,r)"], insert lr pi, auto)
      qed
    } note inc = this
    {
      assume pi: "\<pi> (f,?n) ?i = Decrease \<or> \<pi> (f,?n) ?i = Wild"
      have "gen_usable_rules ?tsi ^^^ invert_dep k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
      proof (rule rel_dep_invert_mono, rule, intro gen_usable_rulesI)
        fix l r
        assume "(l, r) \<in> (gen_usable_rules ?tsi)^-1"
        then have "(r,l) \<in> gen_usable_rules ?tsi" by auto
        note lr = gen_usable_rulesE[OF this]
        show "gen_usable_rule (Fun f ts) (l, r)" unfolding ts
          by (rule in_arg[of ?i _ "(r,l)"], insert lr pi, auto)
      qed
    } note dec = this
    {
      assume prems: "gen_usable_rules (Fun f ts) ^^^ k \<subseteq> NS" 
      note us = this[unfolded ts]
      have orient: "{(Fun f ts \<cdot> \<sigma>, v)} ^^^ k \<subseteq> NS"
      proof (cases "\<pi> (f,?n) ?i")
        case Ignore
        with compat_lr compat_rl
        show ?thesis unfolding t v by (cases k, auto)
      next
        case Increase
        have "gen_usable_rules ?tsi ^^^ k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          by (rule inc, insert Increase, auto)
        from subset_trans[OF this prems] have "gen_usable_rules ?tsi ^^^ k \<subseteq> NS" .
        from IH this have "{(?dl,?dr)} ^^^ k \<subseteq> NS" unfolding tsi by simp
        with compat_lr compat_rl Increase show ?thesis unfolding t v 
          by (cases k, auto)
      next
        case Decrease
        have "gen_usable_rules ?tsi ^^^ invert_dep k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          by (rule dec, insert Decrease, auto)
        from subset_trans[OF this prems] have "gen_usable_rules ?tsi ^^^ invert_dep k \<subseteq> NS" .
        from IH this have "{(?dl,?dr)} ^^^ invert_dep k \<subseteq> NS" unfolding tsi by simp
        with compat_lr compat_rl Decrease show ?thesis unfolding t v 
          by (cases k, auto)
      next
        case Wild
        have one: "gen_usable_rules ?tsi ^^^ invert_dep k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          by (rule dec, insert Wild, auto)
        have two: "gen_usable_rules ?tsi ^^^ k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          by (rule inc, insert Wild, auto)
        from one two have "k = Ignore \<or> gen_usable_rules ?tsi ^^^ Wild \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          by (cases k, auto)
        then show ?thesis
        proof
          assume "k = Ignore"
          then show ?thesis by auto
        next
          assume "gen_usable_rules ?tsi ^^^ Wild \<subseteq> gen_usable_rules (Fun f ts) ^^^ k"
          from subset_trans[OF this prems] have "gen_usable_rules ?tsi ^^^ Wild \<subseteq> NS" .
          from IH[THEN conjunct1, rule_format, OF this] have "{(?dl,?dr)} ^^^ Wild \<subseteq> NS" unfolding tsi by auto
          with compat_lr compat_rl Wild show ?thesis unfolding t v 
            by (cases k, auto)
        qed
      qed
    }
    then have orient: "gen_usable_rules (Fun f ts) ^^^ k \<subseteq> NS \<longrightarrow> {(Fun f ts \<cdot> \<sigma>, v)} ^^^ k \<subseteq> NS" ..
    let ?ts = "\<lambda> t. tbef @ t # taft"
    let ?C = "\<lambda> t. Fun f (?ts t)"
    {
      fix j
      from IH[THEN conjunct2]
      obtain u \<mu> where dr: "?dr = u \<cdot> \<mu>"
        and us: "gen_usable_rules u ^^^ j \<subseteq> gen_usable_rules ?tsi ^^^ j"
        and nf: "\<mu> ` vars_term u \<subseteq> NFQ"
        by blast
      have "finite (vars_term (?C u))" by auto
      from finite_fresh_names_infinite_univ[OF this infinite_V]
        obtain ren ren' where
        ren: "\<And> x. x \<in> vars_term (?C u) \<Longrightarrow> ren x \<notin> vars_term (?C u)"
        and ren': "\<And> x. x \<in> vars_term (?C u) \<Longrightarrow> ren' (ren x) = x" by blast
      let ?ren = "(\<lambda> x. Var (ren x)) :: ('f,'v)subst"
      let ?ren' = "(\<lambda> x. Var (ren' x)) :: ('f,'v)subst"
      let ?u = "u \<cdot> ?ren"
      let ?\<mu> = "\<lambda> x. if (x \<in> vars_term (?C u)) then \<sigma> x else (?ren' \<circ>\<^sub>s \<mu>) x"
      have "\<exists>u \<mu>. v = ?C u \<cdot> \<mu> \<and> gen_usable_rules u ^^^ j \<subseteq> gen_usable_rules ?tsi ^^^ j \<and> \<mu> ` vars_term (?C u) \<subseteq> NFQ"
      proof (intro exI conjI)
        have "?dr = u \<cdot> (?ren \<circ>\<^sub>s ?\<mu>)" unfolding dr
          by (rule term_subst_eq, 
          unfold subst_compose_def,
          insert ren ren', auto)
        also have "... = ?u \<cdot> ?\<mu>" by simp
        finally have "?dr = ?u \<cdot> ?\<mu>" .
        moreover
        have "?\<sigma> (tbef @ taft) = map (\<lambda> t. t \<cdot> ?\<mu>) (tbef @ taft)"
        proof (rule map_cong[OF refl])
          fix t 
          assume t: "t \<in> set (tbef @ taft)"
          show "t \<cdot> \<sigma> = t \<cdot> ?\<mu>"
            by (rule term_subst_eq, insert t, auto)
        qed
        ultimately
        show "v = ?C ?u \<cdot> ?\<mu>" unfolding v by simp
      next
        have "gen_usable_rules ?u \<subseteq> gen_usable_rules (?u \<cdot> ?ren')"
          by (rule gen_usable_rules_subst)
        also have "?u \<cdot> ?ren' = u \<cdot> (?ren \<circ>\<^sub>s ?ren')" by simp
        also have "... = u \<cdot> Var"
          by (rule term_subst_eq, unfold subst_compose_def, insert ren ren', auto)
        finally have us': "gen_usable_rules ?u \<subseteq> gen_usable_rules u" by simp
        show "gen_usable_rules ?u ^^^ j \<subseteq> gen_usable_rules ?tsi ^^^ j"
          by (rule subset_trans[OF rel_dep_mono[OF us'] us])
      next
        {
          fix x
          assume "x \<in> vars_term (?C ?u)"
          then have "x \<in> vars_term (Fun f (tbef @ taft)) \<or> x \<in> vars_term ?u" by auto
          then have "?\<mu> x \<in> NFQ"
          proof
            assume "x \<in> vars_term (Fun f (tbef @ taft))"
            with Fun.prems(2) show ?thesis unfolding ts by auto
          next
            assume "x \<in> vars_term ?u"
            then obtain y where y: "y \<in> vars_term u" and x: "x = ren y" 
              unfolding vars_term_subst by auto
            with nf ren ren' show ?thesis unfolding subst_compose_def by auto
          qed
        }
        then show "?\<mu> ` vars_term (?C ?u) \<subseteq> NFQ" by blast
      qed          
    } 
    note IH = this
    show ?thesis
    proof (rule conjI[OF orient])
      from gen_usable_rules_split[of f tbef taft] obtain j where 
        usi: "\<And> s t. gen_usable_rules s ^^^ j \<subseteq> gen_usable_rules t ^^^ j \<Longrightarrow> gen_usable_rules (Fun f (tbef @ s # taft)) \<subseteq> gen_usable_rules (Fun f (tbef @ t # taft))"
        by auto
      from IH[of j] obtain u \<mu> where v: "v = ?C u \<cdot> \<mu>"
        and usi_prem: "gen_usable_rules u ^^^ j \<subseteq> gen_usable_rules ?tsi ^^^ j"
        and nf: "\<mu> ` vars_term (?C u) \<subseteq> NFQ" by auto
      note usi = usi[OF usi_prem]
      show "\<exists>u \<mu>. v = u \<cdot> \<mu> \<and> gen_usable_rules u ^^^ k \<subseteq> gen_usable_rules (Fun f ts) ^^^ k \<and> \<mu> ` vars_term u \<subseteq> NFQ"
        by (rule exI[of _ "?C u"], rule exI[of _ \<mu>], intro conjI[OF v conjI[OF _ nf]], unfold ts,
        rule rel_dep_mono[OF usi])
    qed
  qed
qed

lemma gen_usable_rules_lemma: 
  assumes step: "(t \<cdot> \<sigma>,v) \<in> (qrstep nfs Q R)^*"
  and usable: "gen_usable_rules t \<subseteq> NS"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and \<sigma>F: "\<And> x. funas_term (\<sigma> x) \<subseteq> F"
  and tsigF: "funas_args_term t \<subseteq> F"
  and ndef: "\<not> defined (applicable_rules Q R) (the (root (t \<cdot> \<sigma>)))"
  shows "(t \<cdot> \<sigma>, v) \<in> NS"
proof -
  let ?R = "qrstep nfs Q R"
  have tsigF: "funas_args_term (t \<cdot> \<sigma>) \<subseteq> F" 
  proof (cases t)
    case (Var x) then show ?thesis using \<sigma>F[of x] by (cases "\<sigma> x", auto simp: funas_args_term_def)
  next 
    case (Fun f ts) then show ?thesis using \<sigma>F tsigF
      by (auto simp: funas_args_term_def funas_term_subst)
  qed
  from rtrancl_imp_relpow[OF step] obtain n
    where "(t \<cdot> \<sigma>, v) \<in> ?R^^n" ..
  from this \<sigma> usable tsigF ndef 
  show ?thesis
  proof (induction n arbitrary: t \<sigma> v)
    case 0
    then show ?case using refl_NS unfolding refl_on_def by simp
  next
    case (Suc n)
    from Suc.prems(1)
    have "(t \<cdot> \<sigma>, v) \<in> ?R^^(1 + n)" by auto
    from this[unfolded relpow_add] obtain u where
      one: "(t \<cdot> \<sigma>, u) \<in> ?R" and n: "(u,v) \<in> ?R ^^ n" by auto
    from Suc.prems(4-5) have "funas_args_term (t \<cdot> \<sigma>) \<subseteq> F \<and> \<not> defined (applicable_rules Q R) (the (root (t \<cdot> \<sigma>)))" by auto
    from main_technical_lemma[OF one Suc.prems(2) disjI2[OF this], of Increase] Suc.prems(3)
    obtain s \<mu> where ns: "(t \<cdot> \<sigma>, u) \<in> NS" and u: "u = s \<cdot> \<mu>"
      and us: "gen_usable_rules s \<subseteq> gen_usable_rules t"
      and nf: "\<mu> ` vars_term s \<subseteq> NFQ"
      by auto
    from qrstep_imp_nrqrstep[OF _ Suc.prems(5) one[unfolded u]]
    have one: "(t \<cdot> \<sigma>, s \<cdot> \<mu>) \<in> nrqrstep nfs Q R" using wwf_qtrs_imp_left_fun[OF wwf] by force
    from nrqrstep_preserves_root[OF one] Suc.prems(5) have ndef: "\<not> defined (applicable_rules Q R) (the (root (s \<cdot> \<mu>)))" by simp
    from nrqrstep_funas_args_term[OF wwf RF Suc.prems(4) one] have Fs: "funas_args_term (s \<cdot> \<mu>) \<subseteq> F" .
    from Suc.IH[OF n[unfolded u] nf _ Fs ndef] us Suc.prems(3) have "(s \<cdot> \<mu>, v) \<in> NS" by auto
    with ns trans_NS show ?case unfolding u trans_def by blast
  qed
qed
end

(* ************************************************ *)
section \<open>processors using generalized usable rules\<close>


text \<open>directly use conditional contraints to define conditional reduction
  pair processor. Since the conditional constraints allow us to express unconditional
  constraints as well, we also get the generalized reduction pair processor without
  conditions as consequence.\<close>

datatype ('f,'v)cond_constraint 
  = CC_cond bool "('f,'v)rule" 
  | CC_rewr "('f,'v)term" "('f,'v)term"
  | CC_impl "('f,'v)cond_constraint list" "('f,'v)cond_constraint"
  | CC_all 'v "('f,'v)cond_constraint"

lemma
  fixes P :: "('f, 'v) cond_constraint \<Rightarrow> bool"
  assumes "\<And> ct s t. P(CC_cond ct (s,t))" and
  "\<And> s t. P(CC_rewr s t)" and 
  "\<And>cs c. (\<And>c. c \<in> set cs \<Longrightarrow> P c) \<Longrightarrow> P c \<Longrightarrow> P(CC_impl cs c)" and
  "\<And> x c. P c \<Longrightarrow> P(CC_all x c)"
  shows cond_constraint_induct[case_names cond rewr impl all, induct type: cond_constraint]:
    "P c" 
   by (induct c, insert assms, auto) 


definition disjoint_variant :: "('f,'v)rule list \<Rightarrow> ('f,'v)rule list \<Rightarrow> bool"
  where "disjoint_variant sts uvs \<equiv> 
    length sts = length uvs \<and> 
    (\<forall> i < length sts. sts ! i =\<^sub>v uvs ! i) \<and> 
    is_partition (map vars_rule uvs)"

text \<open>define, which constraints must be present, where the two nats specify how many pairs
  we take as predecessors and successofs (BEFore and AFTer)\<close>
definition initial_conditions_gen :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "initial_conditions_gen p bef_len aft_len P st \<equiv> let
     pairs = (\<lambda> n. { sts. length sts = n \<and> set sts \<subseteq> P});
     all = { bef @ st # aft | bef aft. bef \<in> pairs bef_len \<and> aft \<in> pairs aft_len}
   in { bef_st_aft . bef_st_aft \<in> all \<and> (\<forall> i < bef_len + aft_len. p (bef_st_aft ! i) (bef_st_aft ! Suc i))}"

lemma initial_conditions_gen_mono: assumes "\<And> s t. p s t \<Longrightarrow> q s t"
  shows "initial_conditions_gen p bef_len aft_len P st \<subseteq> initial_conditions_gen q bef_len aft_len P st"
  using assms unfolding initial_conditions_gen_def Let_def by auto

text \<open>datatype to represent atomic constraints on the orders\<close>
datatype condition_type = Bound | Strict | Non_Strict

fun condition_of :: "'f \<Rightarrow> condition_type \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f,'v)cond_constraint" where
  "condition_of c Bound (s,_) = CC_cond False (s,Fun c [])"
| "condition_of c Strict st = CC_cond True st"
| "condition_of c Non_Strict st = CC_cond False st"

definition constraint_of :: "'f \<Rightarrow> condition_type \<Rightarrow> ('f,'v)rule list \<Rightarrow> nat \<Rightarrow> ('f,'v)cond_constraint" where
  "constraint_of c ctype uvs bef \<equiv> 
  CC_impl 
    (map (\<lambda> i. CC_rewr (snd (uvs ! i)) (fst (uvs ! Suc i))) [0 ..< length uvs - 1])
    (condition_of c ctype (uvs ! bef))"

context fixed_trs_dep_order
begin

definition rel_of :: "bool \<Rightarrow> ('f,'v)trs" where
  "rel_of ct \<equiv> if ct then S else NS"

definition normal_F_subst :: "('f, 'v) subst \<Rightarrow> bool" where
  "normal_F_subst \<sigma> \<longleftrightarrow> (\<Union>(funas_term ` range \<sigma>) \<subseteq> F) \<and> range \<sigma> \<subseteq> NF_trs R"

text \<open>if we have minimality (m is true), then demand strong normalization\<close>
definition m_SN :: "('f, 'v) term \<Rightarrow> bool" where
  "m_SN t \<longleftrightarrow> m \<longrightarrow> SN_on (qrstep nfs Q R) {t}"

fun cc_models :: "('f,'v)subst \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
  "\<sigma> \<Turnstile> CC_cond ct (s,t) = ((s \<cdot> \<sigma>,t \<cdot> \<sigma>) \<in> rel_of ct)"
| "\<sigma> \<Turnstile> CC_impl c1 c2 = (Ball (set c1) (cc_models \<sigma>) \<longrightarrow> \<sigma> \<Turnstile> c2)"
| "\<sigma> \<Turnstile> CC_rewr s t = (m_SN (s \<cdot> \<sigma>) \<and> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^* \<and> t \<cdot> \<sigma> \<in> NF_terms Q)"
| "\<sigma> \<Turnstile> CC_all x c = (\<forall> (t :: ('f,'v)term). funas_term t \<subseteq> F \<longrightarrow> t \<in> NF_trs R \<longrightarrow> (\<sigma> (x := t)) \<Turnstile> c)"

definition cc_valid :: "('f,'v)cond_constraint \<Rightarrow> bool" where
  "cc_valid c \<equiv> \<forall> \<sigma>. normal_F_subst \<sigma> \<longrightarrow> \<sigma> \<Turnstile> c"

lemma cc_validE[elim]: "cc_valid c \<Longrightarrow> normal_F_subst \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> c" unfolding cc_valid_def by blast
lemma cc_validI[intro!]: "\<lbrakk>\<And> \<sigma>. normal_F_subst \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> c\<rbrakk> \<Longrightarrow> cc_valid c" unfolding cc_valid_def by blast

definition cc_equiv :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> bool" (infix "=cc" 49) where
  "c =cc d \<equiv> \<forall> \<sigma>. \<sigma> \<Turnstile> c = \<sigma> \<Turnstile> d"

definition cc_implies :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> bool" (infix "\<longrightarrow>cc" 49) where
  "c \<longrightarrow>cc d \<equiv> \<forall> \<sigma>. \<sigma> \<Turnstile> c \<longrightarrow> \<sigma> \<Turnstile> d"

lemma cc_equiv_substE: "c =cc d \<Longrightarrow> \<sigma> \<Turnstile> c = \<sigma> \<Turnstile> d" unfolding cc_equiv_def by auto
lemma cc_equivI[intro]: "\<lbrakk>\<And> \<sigma>. \<sigma> \<Turnstile> c = \<sigma> \<Turnstile> d\<rbrakk> \<Longrightarrow> c =cc d" unfolding cc_equiv_def by auto
lemma cc_impliesI[intro]: "\<lbrakk>\<And> \<sigma>. \<sigma> \<Turnstile> c \<Longrightarrow> \<sigma> \<Turnstile> d\<rbrakk> \<Longrightarrow> c \<longrightarrow>cc d" unfolding cc_implies_def by auto
lemma cc_impliesE[elim]: "c \<longrightarrow>cc d \<Longrightarrow> cc_valid c \<Longrightarrow> cc_valid d" unfolding cc_implies_def cc_valid_def by auto
lemma cc_implies_substE[elim]: "c \<longrightarrow>cc d \<Longrightarrow> \<sigma> \<Turnstile> c \<Longrightarrow> \<sigma> \<Turnstile> d" unfolding cc_implies_def cc_valid_def by auto
lemma cc_equiv_validE: "c =cc d \<Longrightarrow> cc_valid c = cc_valid d" unfolding cc_valid_def cc_equiv_def by auto
lemma cc_equiv_refl[simp]: "c =cc c" by auto
lemma cc_implies_refl[simp]: "c \<longrightarrow>cc c" by auto

text \<open>we do not have to consider all preceeding / succeeding pairs, but only those which are
  connected in the dependency graph. This optimization is also integrated in AProVE\<close>
definition initial_conditions :: "nat \<Rightarrow> nat \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f,'v)rule list set" where
  "initial_conditions bef aft P \<equiv> initial_conditions_gen (\<lambda> st uv. (st,uv) \<in> DG nfs m P Q R) bef aft P"

text \<open>main test, whether all required constraints are present to ensure that some pair is bounded/decreasing\<close>
definition constraint_present :: "nat \<Rightarrow> nat \<Rightarrow> ('f,'v)trs \<Rightarrow>
   condition_type \<Rightarrow> ('f,'v)cond_constraint set \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "constraint_present bef aft P ctype ccs st \<equiv>
     (\<forall> sts. sts \<in> initial_conditions bef aft P st \<longrightarrow> 
     (\<exists> c uvs. disjoint_variant sts uvs \<and> c \<in> ccs \<and> c \<longrightarrow>cc constraint_of const ctype uvs bef))"

fun tcondition_of :: "condition_type \<Rightarrow> ('f,'v)rule \<Rightarrow> bool" where
  "tcondition_of Bound (s,t) = ((s,Fun const []) \<in> NS)"
| "tcondition_of Strict st = (st \<in> S)"
| "tcondition_of Non_Strict st = (st \<in> NS)"

lemma tcondition_of: 
  assumes model: "\<sigma> \<Turnstile> condition_of const ctype (s,t)"
  shows "tcondition_of ctype (s \<cdot> \<sigma>,t \<cdot> \<sigma>)"
  using assms by (cases ctype, auto simp: rel_of_def)

text \<open>the conditional reduction pair processor, as it is formulated on chains, 
  where here we already assume that the chains respect the signature F\<close>
lemma conditional_general_reduction_pair_chains: 
  assumes U_NS: "gen_usable_rules_pairs (P \<union> Pw) \<subseteq> NS"
  and chain: "min_ichain_sig (nfs,m,P,Pw,Q,Rs,Rw) F s t \<sigma>"
  and nvar: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t"
  and var_cond: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ndef: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> \<not> defined (applicable_rules Q (Rs \<union> Rw)) (the (root t))"
  and PF: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> funas_args_term t \<subseteq> F"
  and orient: "P \<union> Pw \<subseteq> Ps \<union> Pns"
  and cS: "Ball Ps (constraint_present bef aft (P \<union> Pw) Strict ccs)"
  and cNS: "Ball Pns (constraint_present bef aft (P \<union> Pw) Non_Strict ccs)"
  and cB: "Ball Pb (constraint_present bef aft (P \<union> Pw) Bound ccs)"
  and ccs: "Ball ccs cc_valid"
  and R: "Rs \<union> Rw = R"
  shows "\<exists> i. min_ichain_sig (nfs,m,P - Ps, Pw - Ps,Q,Rs,Rw) F (shift s i) (shift t i) (shift \<sigma> i) 
    \<or> min_ichain_sig (nfs,m,P - Pb, Pw - Pb,Q,Rs,Rw) F (shift s i) (shift t i) (shift \<sigma> i)"
proof -
  let ?DP = "(nfs,m,P,Pw,Q,Rs,Rw)"
  let ?DPm = "\<lambda> S. (nfs,m,P - S,Pw - S,Q,Rs,Rw)"
  let ?DP_Ps = "?DPm Ps"
  let ?DP_Pb = "?DPm Pb"
  show ?thesis
  proof (cases "(INFM i. (s i, t i) \<in> Ps) \<and> (INFM i. (s i, t i) \<in> Pb)")
    case False
    (* if we do not have infinitely many strict or bound pairs, then we are done, as we can drop
       the initial part of the chain to obtain an infinite chain for one of the resulting DP-problems *)
    then obtain i where disj: "(\<forall> j \<ge> i. (s j, t j) \<notin> Ps) \<or> (\<forall> j \<ge> i. (s j, t j) \<notin> Pb)"
      unfolding INFM_nat_le by blast
    let ?s = "shift s"
    let ?t = "shift t"
    let ?\<sigma> = "shift \<sigma>"
    from disj
    show ?thesis
    proof
      assume nS: "(\<forall> j \<ge> i. (s j, t j) \<notin> Ps)"
      let ?DP = "(nfs, m, P - Ps, Pw - Ps, Q, Rs - {}, Rw - {})"
      have "\<exists> i. min_ichain_sig ?DP F (?s i) (?t i) (?\<sigma> i)"
      proof (rule min_ichain_split_sig[OF chain], rule)
        assume "min_ichain_sig (nfs, m, Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, {} \<inter> (Rs \<union> Rw), Rs \<union> Rw - {}) F s t \<sigma>"
        then have "INFM i. (s i, t i) \<in> Ps \<inter> (P \<union> Pw)" by (auto simp: ichain.simps)
        with nS show False unfolding INFM_nat_le by blast
      qed
      then show ?thesis by auto
    next
      assume nB: "(\<forall> j \<ge> i. (s j, t j) \<notin> Pb)"
      let ?DP = "(nfs, m, P - Pb, Pw - Pb, Q, Rs - {}, Rw - {})"
      have "\<exists> i. min_ichain_sig ?DP F (?s i) (?t i) (?\<sigma> i)"
      proof (rule min_ichain_split_sig[OF chain], rule)
        assume "min_ichain_sig (nfs, m, Pb \<inter> (P \<union> Pw), P \<union> Pw - Pb, Q, {} \<inter> (Rs \<union> Rw), Rs \<union> Rw - {}) F s t \<sigma>"
        then have "INFM i. (s i, t i) \<in> Pb \<inter> (P \<union> Pw)" by (auto simp: ichain.simps)
        with nB show False unfolding INFM_nat_le by blast
      qed
      then show ?thesis by auto
    qed
  next
    (* otherwise, infinitely many strict and bound pairs are occuring, which we must transform into a contradiction *)
    case True
    let ?QR = "qrstep nfs Q R"
    let ?ndef = "\<lambda> t. \<not> defined (applicable_rules Q R) (the (root t))"
    from chain have ichain: "ichain ?DP s t \<sigma>" and \<sigma>F: "funas_ichain s t \<sigma> \<subseteq> F" by auto
    {
      fix i
      from \<sigma>F have "\<Union>(funas_term ` range (\<sigma> i)) \<subseteq> F" unfolding funas_ichain_def by auto
    } note \<sigma>F = this
    let ?st = "\<lambda> i. (s i, t i)"
    from ichain have P_Pw: "\<And> i. ?st i \<in> P \<union> Pw" unfolding ichain.simps by auto
    from ichain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NFQ" unfolding ichain.simps by auto
    (* we first show, that for each i, whenever (s_i, t_i) is strictly decreasing, then s_i \<sigma> > t_i \<sigma>,
       and similar if (s_i, t_i) is weakly decreasing or bounded (arbitrary condition type ctype).
       we demand i \<ge> bef, since otherwise, we cannot consider the bef preceding pairs *)
    {
      fix ctype PP i      
      assume i_bef: "i \<ge> bef" and mem: "(s i, t i) \<in> PP"
      assume cp: "Ball PP (constraint_present bef aft (P \<union> Pw) ctype ccs)"
      with mem have cp: "constraint_present bef aft (P \<union> Pw) ctype ccs (s i, t i)" by auto
      define j where "j = i - bef" 
      define n where "n = Suc (bef + aft)"
      let ?j = "\<lambda> i. i + j"
      from i_bef j_def have i_j_bef: "i = ?j bef" by auto
      let ?sts_gen = "\<lambda> j. map (\<lambda> i. ?st (i + j))"
      let ?sts = "?sts_gen j [0 ..< n]"
      let ?bef = "?sts_gen j [0 ..< bef]"
      let ?aft = "?sts_gen (j + Suc bef) [0 ..< aft]"
      have "?sts = ?sts_gen j [0 ..< bef + Suc 0 + aft]" unfolding n_def by auto
      also have "... = ?bef @ ?st i # ?aft"
        unfolding map_upt_add i_j_bef by (simp add: ac_simps)
      finally have sts: "?sts = ?bef @ ?st i # ?aft" .
      have sts_init: "?sts \<in> initial_conditions bef aft (P \<union> Pw) (s i, t i)"
        unfolding initial_conditions_def initial_conditions_gen_def Let_def
      proof (rule, rule, rule, intro exI conjI, rule sts, insert P_Pw, (auto)[2], intro allI impI)
        fix i
        assume "i < bef + aft"
        with n_def have i: "i < n" "Suc i < n" by auto
        then have sts: "(?sts ! i, ?sts ! Suc i) = (?st (?j i), ?st (Suc (?j i)))" by auto
        show "(?sts ! i, ?sts ! Suc i) \<in> DG nfs m (P \<union> Pw) Q R" unfolding sts
          by (rule DG_I[of _ _ _ _ _ "\<sigma> (?j i)" "\<sigma> (Suc (?j i))"], 
            insert chain R, auto simp: ichain.simps minimal_cond_def)
      qed
      from cp[unfolded constraint_present_def, rule_format, OF sts_init]
      obtain c uvs where var: "disjoint_variant ?sts uvs" and c_ccs: "c \<in> ccs" and c_uvs: "c \<longrightarrow>cc constraint_of const ctype uvs bef" by auto
      define us where "us = (\<lambda> i. fst (uvs ! i))"
      define vs where "vs = (\<lambda> i. snd (uvs ! i))"
      let ?uv = "\<lambda> i. (us i, vs i)"
      from cc_impliesE[OF c_uvs] ccs c_ccs
      have valid: "cc_valid (constraint_of const ctype uvs bef)" by auto
      note var = var[unfolded disjoint_variant_def]
      from var have part: "is_partition (map vars_rule uvs)" and ulen: "length uvs = n" by auto
      (* we need to deal with renamings of pairs *)
      {
        fix i
        assume "i < n"
        with var have "?st (?j i) =\<^sub>v ?uv i" unfolding us_def vs_def by auto
        from eq_rule_mod_varsE[OF this] this have
        "\<exists> \<tau>. s (?j i) = us i \<cdot> \<tau> \<and> t (?j i) = vs i \<cdot> \<tau> \<and> range \<tau> \<subseteq> range Var" "?st (?j i) =\<^sub>v ?uv i" by auto
      } 
      then have eq: "\<And> i. i < n \<Longrightarrow> ?st (?j i) =\<^sub>v ?uv i" and taus: "\<forall> i. (\<exists> \<tau>. i < n \<longrightarrow> s (?j i) = us i \<cdot> \<tau> \<and> t (?j i) = vs i \<cdot> \<tau> \<and> range \<tau> \<subseteq> range Var)" by blast+
      from choice[OF taus] obtain \<tau> where st_uv: "\<And> i. i < n \<Longrightarrow> s (?j i) = us i \<cdot> \<tau> i" "\<And> i. i < n \<Longrightarrow> t (?j i) = vs i \<cdot> \<tau> i" 
        and \<tau>: "\<And> i. i < n \<Longrightarrow> range (\<tau> i) \<subseteq> range Var" by auto
      let ?sigs = "map (\<lambda> i. \<tau> i \<circ>\<^sub>s \<sigma> (?j i)) [0 ..< n]"
      (* and combinations of substitutions *)
      define \<gamma> where "\<gamma> = (\<lambda> x. if x \<in> \<Union>(vars_rule ` ?uv ` {0 ..< n}) then fun_merge ?sigs (map vars_rule uvs) x else Var x)"
      {
        fix i x
        assume i: "i < n" and x: "x \<in> vars_rule (uvs ! i)"
        then have "x \<in> \<Union>(vars_rule ` ?uv ` {0 ..< n})" unfolding us_def vs_def by auto
        then have "\<gamma> x = fun_merge ?sigs (map vars_rule uvs) x" unfolding \<gamma>_def by auto
        also have "\<dots> = (?sigs ! i) x"
          using part [unfolded is_partition_alt is_partition_alt_def]
          by (intro fun_merge_part, insert i x ulen, auto simp: is_partition_def)
        also have "\<dots> = (\<tau> i \<circ>\<^sub>s \<sigma> (?j i)) x" using i by simp
        finally have "\<gamma> x = (\<tau> i \<circ>\<^sub>s \<sigma> (?j i)) x" .
      } note \<gamma> = this
      (* which in the end delivers the one desired substitution \<gamma> *)
      {
        fix i
        assume i: "i < n"
        have "us i \<cdot> \<gamma> = us i \<cdot> (\<tau> i \<circ>\<^sub>s \<sigma> (?j i))"
          by (rule term_subst_eq, rule \<gamma>[OF i], unfold us_def vars_rule_def, auto)
        also have "\<dots> = s (?j i) \<cdot> \<sigma> (?j i)" unfolding st_uv[OF i] by simp
        finally have "us i \<cdot> \<gamma> = s (?j i) \<cdot> \<sigma> (?j i)" .
      } note u_s = this
      {
        fix i
        assume i: "i < n"
        have "vs i \<cdot> \<gamma> = vs i \<cdot> (\<tau> i \<circ>\<^sub>s \<sigma> (?j i))"
          by (rule term_subst_eq, rule \<gamma>[OF i], unfold vs_def vars_rule_def, auto)
        also have "\<dots> = t (?j i) \<cdot> \<sigma> (?j i)" unfolding st_uv[OF i] by simp
        finally have "vs i \<cdot> \<gamma> = t (?j i) \<cdot> \<sigma> (?j i)" .
      } note v_t = this
      have gammaF: "normal_F_subst \<gamma>" unfolding normal_F_subst_def
      proof -
        {
          fix x
          have "funas_term (\<gamma> x) \<subseteq> F \<and> \<gamma> x \<in> NF_trs R"
          proof (cases "x \<in> \<Union>(vars_rule ` ?uv ` {0 ..< n})")
            case False
            then have x: "\<gamma> x = Var x" unfolding \<gamma>_def by auto
            from NF_Var_is_Fun[of "lhss R" x] wwf_var_cond[OF wwf] have "Var x \<in> NF_trs R" by force
            then show ?thesis using x by auto
          next
            case True
            then obtain i where i: "i < n" and xx: "x \<in> vars_rule (?uv i)" by auto
            from eq_rule_mod_vars_var_cond[OF eq[OF i] var_cond[OF P_Pw]] xx
            have x: "x \<in> vars_term (us i)" unfolding vars_rule_def by auto
            then have "us i \<unrhd> Var x" by auto
            then have supt: "us i \<cdot> \<gamma> \<unrhd> \<gamma> x" by auto
            from u_s[OF i] NF[of "i+j"] NFQ have "us i \<cdot> \<gamma> \<in> NF_trs R" by auto
            from NF_subterm[OF this supt] have NF: "\<gamma> x \<in> NF_trs R" .
            from \<tau>[OF i] obtain y where \<tau>: "\<tau> i x = Var y" by auto
            have "\<gamma> x = (\<tau> i \<circ>\<^sub>s \<sigma> (?j i)) x"
              by (rule \<gamma>[OF i], insert xx us_def vs_def, auto)
            also have "\<dots> = \<sigma> (?j i) y" unfolding subst_compose_def \<tau> by simp
            finally have "funas_term (\<gamma> x) \<subseteq> F" using \<sigma>F by auto
            with NF show ?thesis by auto
          qed
        }
        then show "\<Union>(funas_term ` range \<gamma>) \<subseteq> F \<and> range \<gamma> \<subseteq> NF_trs R" by auto
      qed      
      have bef: "bef < n" unfolding n_def by auto
      from cc_validE[OF valid gammaF] 
      have model: "\<gamma> \<Turnstile> constraint_of const ctype uvs bef" .
      (* show that \<gamma> satisfies all rewrite constraints which are premises of the conditional constraint for the pair *)
      have rewr: "Ball (set (map (\<lambda>i. CC_rewr (snd (uvs ! i)) (fst (uvs ! Suc i))) [0..<length uvs - 1])) (cc_models \<gamma>)"
      proof
        fix c
        assume "c \<in> set (map (\<lambda>i. CC_rewr (snd (uvs ! i)) (fst (uvs ! Suc i))) [0..<length uvs - 1])"
        then obtain i where i: "i < n - 1" and c: "c = CC_rewr (vs i) (us (Suc i))" unfolding us_def vs_def ulen by auto
        from i have i: "i < n" "Suc i < n" unfolding n_def by auto
        show "\<gamma> \<Turnstile> c" unfolding c cc_models.simps u_s[OF i(2)] v_t[OF i(1)] using chain 
          by (auto simp: minimal_cond_def R ichain.simps m_SN_def)
      qed
      from this model[unfolded constraint_of_def]
      have "\<gamma> \<Turnstile> condition_of const ctype (us bef, vs bef)" unfolding us_def vs_def by simp
      (* and conclude that s_i \<sigma>_i is in relation to t_i \<sigma>_i *)
      from tcondition_of[OF this, unfolded u_s[OF bef] v_t[OF bef]]
      have "tcondition_of ctype (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i)" unfolding i_j_bef .
    } note main_constraint = this
    define cc where "cc = (Fun const [] :: ('f,'v)term)"
    (* shift everything by bef, so there are always enough preceding pairs *)
    define u where "u = (\<lambda> i. s (i + bef) \<cdot> \<sigma> (i + bef))" 
    define v where "v = (\<lambda> i. t (i + bef) \<cdot> \<sigma> (i + bef))"
    let ?st = "\<lambda> i. (s (i + bef), t (i + bef))"
    note uv = u_def v_def
    (* and conclude that all pairs (u i, v i) are in relation *)
    {
      fix i
      assume i: "?st i \<in> Ps"
      from main_constraint[OF _ this cS] have "(u i, v i) \<in> S" unfolding uv by simp
    } note PS = this
    {
      fix i
      assume i: "?st i \<in> Pns"
      from main_constraint[OF _ this cNS] have "(u i, v i) \<in> NS" unfolding uv by simp
    } note PNS = this
    {
      fix i
      assume i: "?st i \<in> Pb"
      from main_constraint[OF _ this cB] have "(u i, cc) \<in> NS" unfolding uv cc_def by simp
    } note PB = this
    (* show that there always is a non-strict decrease between v_i and u_i+1 due to orientation of usable rules *)
    {
      fix i
      from ichain have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*" 
       and P: "(s i, t i) \<in> P \<union> Pw" 
       and NF: "s i \<cdot> \<sigma> i \<in> NFQ" unfolding ichain.simps R by auto
      from P U_NS have orient: "gen_usable_rules (t i) \<subseteq> NS" unfolding gen_usable_rules_pairs_def by force
      from nvar[OF P] obtain f ts where ti: "t i = Fun f ts" by (cases "t i", auto)
      from PF[OF P] have tF: "funas_args_term (t i) \<subseteq> F" .
      from ndef[OF P] have "?ndef (t i)" unfolding R .
      with ti have ndef: "?ndef (t i \<cdot> \<sigma> i)" by simp
      {
        fix x
        assume "x \<in> vars_term (t i)"
        with var_cond[OF P] have "x \<in> vars_term (s i)" by auto
        then have "s i \<unrhd> Var x" by auto
        from NF_subterm[OF NF supteq_subst[OF this, of "\<sigma> i"]] have "\<sigma> i x \<in> NFQ" by simp
      }
      then have NF: "\<sigma> i ` vars_term (t i) \<subseteq> NFQ" by auto
      have NS: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> NS" 
        by (rule gen_usable_rules_lemma[OF steps orient NF _ tF ndef], insert \<sigma>F, auto)
    } note NS = this
    {
      fix i
      have "(v i, u (Suc i)) \<in> NS" unfolding uv using NS[of "i+bef"] by simp
    } note NS = this
    (* eventually put everything together to derive contradiction to non-infinitesmality *)
    {
      fix i
      from P_Pw[of "i + bef"] have "?st i \<in> P \<union> Pw" .
      with orient have "?st i \<in> Ps \<union> Pns" by auto
      with PS PNS have "(u i, v i) \<in> NS \<union> S" by auto
      with NS[of i]
        trans_NS[unfolded trans_def] compat_S_NS have "(u i, u (Suc i)) \<in> NS \<union> S" by blast
    } note orient = this    
    {
      fix i
      assume "?st i \<in> Ps"
      from PS[OF this] NS[of i] compat_S_NS have "(u i, u (Suc i)) \<in> S" by auto
    } 
    then have Ps: "{i. ?st i \<in> Ps} \<subseteq> {i. (u i, u (Suc i)) \<in> S}" by auto
    from PB have "{i. ?st i \<in> Pb} \<subseteq> {i. (u i, cc) \<in> NS \<union> S}" by auto
    from chain_split[of _ "\<lambda> i. i" u, OF Ps this orient]
    have disj: "(\<forall>\<^sub>\<infinity>j. ?st j \<notin> Ps) \<or> (\<forall>\<^sub>\<infinity>j. ?st j \<notin> Pb)" by auto
    note shift = Infm_double_shift[of "\<lambda> s t. (s,t) \<in> P" s bef t for P]
    from True[folded shift[of Ps] shift[of Pb]]
    have "(\<exists>\<^sub>\<infinity>i. ?st i \<in> Ps) \<and> (\<exists>\<^sub>\<infinity>i. ?st i \<in> Pb)" by auto
    with disj have False unfolding INFM_nat_le MOST_nat_le by auto
    then show ?thesis ..
  qed
qed

text \<open>the same processor again, but here the result on signature extensions is integrated\<close>
lemma conditional_general_reduction_pair_proc: 
  assumes R: "Rs \<union> Rw = R"
  and nvar: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t"
  and var_cond: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ndef: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> \<not> defined (applicable_rules Q R) (the (root t))"
  and PF: "funas_args_trs (P \<union> Pw) \<subseteq> F"
  and U_NS: "gen_usable_rules_pairs (P \<union> Pw) \<subseteq> NS"
  and orient: "P \<union> Pw \<subseteq> Ps \<union> Pns"
  and cS: "Ball Ps (constraint_present bef aft (P \<union> Pw) Strict ccs)"
  and cNS: "Ball Pns (constraint_present bef aft (P \<union> Pw) Non_Strict ccs)"
  and cB: "Ball Pb (constraint_present bef aft (P \<union> Pw) Bound ccs)"
  and ccs: "Ball ccs cc_valid"
  and finiteS: "finite_dpp (nfs,m,P - Ps, Pw - Ps,Q,Rs,Rw)"
  and finiteB: "finite_dpp (nfs,m,P - Pb, Pw - Pb,Q,Rs,Rw)"
  shows "finite_dpp (nfs,m,P, Pw,Q,Rs,Rw)"
proof (rule ccontr)
  let ?D = "(nfs,m,P, Pw,Q,Rs,Rw)"
  let ?Ds = "(nfs,m,P - Ps, Pw - Ps,Q,Rs,Rw)"
  let ?Db = "(nfs,m,P - Pb, Pw - Pb,Q,Rs,Rw)"
  {
    from ex_inj obtain tn :: "('f,'v)term \<Rightarrow> nat" where tn: "inj tn" by auto
    from infinite_countable_subset[OF infinite_V] obtain nv :: "nat \<Rightarrow> 'v" where nv: "inj nv" by blast
    from inj_compose[OF nv tn] have "\<exists> c :: ('f,'v)term \<Rightarrow> 'v. inj c" by blast
  }
  then obtain c :: "('f,'v)term \<Rightarrow> 'v" where inj: "inj c" ..
  interpret cleaning_innermost F c by (unfold_locales, rule inj)
  assume "\<not> ?thesis"  
  then obtain s t \<sigma> where chain: "min_ichain ?D s t \<sigma>" unfolding finite_dpp_def by auto
  from R have RR: "R = Rs \<union> Rw" by simp
  from QF have QF': "QF_cond F Q" unfolding QF_cond_def by auto
  from PF have PF': "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> funas_args_term t \<subseteq> F" 
    unfolding funas_args_trs_def funas_args_rule_def [abs_def] by force
  from clean_min_ichain_below[of Q Rs Rw, unfolded R, OF NFQ QF' RF PF wwf _ var_cond chain]
    nvar ndef obtain \<sigma> where "min_ichain_sig ?D F s t \<sigma>" by blast
  from conditional_general_reduction_pair_chains[where Pb = Pb, OF U_NS this nvar var_cond ndef[unfolded RR] PF' orient cS cNS cB ccs R]
  have "\<exists> i. min_ichain_sig ?Ds F (shift s i) (shift t i) (shift \<sigma> i) \<or> min_ichain_sig ?Db F (shift s i) (shift t i) (shift \<sigma> i)" .
  then obtain s t \<sigma> where "min_ichain_sig ?Ds F s t \<sigma> \<or> min_ichain_sig ?Db F s t \<sigma>" by blast
  then have "min_ichain ?Ds s t \<sigma> \<or> min_ichain ?Db s t \<sigma>" unfolding min_ichain_sig.simps by blast
  with finiteS finiteB show False unfolding finite_dpp_def by blast
qed

text \<open>we can also derive the unconditional general reduction pair processor by taking bef = aft = 0\<close>
lemma general_reduction_pair_proc: 
  assumes R: "Rs \<union> Rw = R"
  and nvar: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t"
  and var_cond: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ndef: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> \<not> defined (applicable_rules Q R) (the (root t))"
  and PF: "funas_args_trs (P \<union> Pw) \<subseteq> F"
  and U_NS: "gen_usable_rules_pairs (P \<union> Pw) \<subseteq> NS"
  and orient: "P \<union> Pw \<subseteq> Ps \<union> Pns"
  and orientS: "Ps \<subseteq> S"
  and orientNS: "Pns \<subseteq> NS"
  and orientB: "\<And> s t. (s,t) \<in> Pb \<Longrightarrow> (s,Fun const []) \<in> NS"
  and finiteS: "finite_dpp (nfs,m,P - Ps, Pw - Ps,Q,Rs,Rw)"
  and finiteB: "finite_dpp (nfs,m,P - Pb, Pw - Pb,Q,Rs,Rw)"
  shows "finite_dpp (nfs,m,P, Pw,Q,Rs,Rw)"
proof (rule conditional_general_reduction_pair_proc[OF R nvar var_cond ndef PF U_NS orient _ _ _ _ finiteS finiteB])
  let ?c = "\<lambda> ctype st. constraint_of const ctype [st] 0"
  let ?cS = "(?c Strict) ` Ps"
  let ?cNS = "(?c Non_Strict) ` Pns"
  let ?cB = "(?c Bound) ` Pb"  
  let ?ccs = "?cS \<union> ?cNS \<union> ?cB"
  {
    fix ctype PP
    have "Ball PP (constraint_present 0 0 (P \<union> Pw) ctype (?c ctype ` PP))"
    proof (intro ballI, unfold constraint_present_def, intro allI impI)
      fix st sts
      assume mem: "st \<in> PP" and sts: "sts \<in> initial_conditions 0 0 (P \<union> Pw) st"
      obtain s t where st: "st = (s,t)" by force
      from sts[unfolded initial_conditions_def initial_conditions_gen_def Let_def] st have sts: "sts = [(s,t)]" by simp
      have disj: "disjoint_variant sts [(s,t)]" unfolding sts disjoint_variant_def
        by (auto simp: is_partition_def)
      show "\<exists>c uvs. disjoint_variant sts uvs \<and> c \<in> (?c ctype) ` PP \<and> c \<longrightarrow>cc constraint_of const ctype uvs 0"
        by (intro exI conjI, rule disj, insert st mem, auto)
    qed
  } note present = this
  from present[of Ps Strict]
  show "Ball Ps (constraint_present 0 0 (P \<union> Pw) Strict ?ccs)" by (force simp: constraint_present_def)
  from present[of Pns Non_Strict]
  show "Ball Pns (constraint_present 0 0 (P \<union> Pw) Non_Strict ?ccs)" by (force simp: constraint_present_def)
  from present[of Pb Bound]
  show "Ball Pb (constraint_present 0 0 (P \<union> Pw) Bound ?ccs)" by (force simp: constraint_present_def)
  show "Ball ?ccs cc_valid"
  proof
    fix cc
    assume cc: "cc \<in> ?ccs"
    show "cc_valid cc"
    proof
      fix \<sigma>
      assume "normal_F_subst \<sigma>"
      then have \<sigma>F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" unfolding normal_F_subst_def by auto
      note stable_S = F_subst_closedD[OF stable_S \<sigma>F]
      note stable_NS = F_subst_closedD[OF stable_NS \<sigma>F]
      {
        assume "cc \<in> ?cS"
        then obtain s t where st: "(s,t) \<in> Ps" and cc: "cc = ?c Strict (s,t)" by force
        from st orientS have "(s,t) \<in> S" by auto
        from stable_S[OF this]
        have "\<sigma> \<Turnstile> cc" unfolding cc constraint_of_def by (simp add: rel_of_def)
      }
      moreover
      {
        assume "cc \<in> ?cB"
        then obtain s t where st: "(s,t) \<in> Pb" and cc: "cc = ?c Bound (s,t)" by force
        from st orientB have "(s,Fun const []) \<in> NS" by auto
        from stable_NS[OF this]
        have "\<sigma> \<Turnstile> cc" unfolding cc constraint_of_def by (simp add: rel_of_def)
      }
      moreover
      {
        assume "cc \<in> ?cNS"
        then obtain s t where st: "(s,t) \<in> Pns" and cc: "cc = ?c Non_Strict (s,t)" by force
        from st orientNS have "(s,t) \<in> NS" by auto
        from stable_NS[OF this]
        have "\<sigma> \<Turnstile> cc" unfolding cc constraint_of_def by (simp add: rel_of_def)
      }
      ultimately show "\<sigma> \<Turnstile> cc" using cc by blast
    qed
  qed
qed auto
end  

end

