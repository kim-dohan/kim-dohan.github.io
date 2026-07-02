theory Tree_Automata_Wit
imports
  Tree_Automata
  Refine_Monadic.Refine_Monadic
  First_Order_Terms.Option_Monad
  "Decreasing-Diagrams-II.Decreasing_Diagrams_II"
begin

no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

section \<open>Various algorithms for tree automata\<close>

subsection \<open>Auxiliary definitions and theorems\<close>

definition "update_all m ks v \<equiv> \<lambda>k. if k \<in> ks then Some v else (m k)"

lemma update_all_dom[simp]:
  "dom (update_all m ks v) = dom m \<union> ks" by (auto simp add: update_all_def)

lemma update_all_ballI[intro]:
  assumes "\<And>k. k \<in> ks \<Longrightarrow> P k v"
      and "\<And>k v. (k,v) \<in> map_to_set m \<Longrightarrow> P k v"
    shows "\<forall>(k,v) \<in> map_to_set (update_all m ks v). P k v"
using assms unfolding update_all_def map_to_set_def by auto

definition "ta_finite TA \<equiv> finite (ta_rules TA) \<and> finite (ta_eps TA) \<and> finite (ta_final TA)"
lemma ta_finiteD:
  assumes "ta_finite TA"
    shows "finite (ta_rules TA)" "finite (ta_eps TA)" "finite (ta_final TA)"
using assms by (simp_all add: ta_finite_def)

lemma ta_subset_finite:
  assumes "ta_subset TA' TA"
      and "ta_finite TA"
    shows "ta_finite TA'"
using assms unfolding ta_finite_def ta_subset_def by (auto intro: finite_subset)

lemma finite_states:
  assumes "ta_finite TA"
    shows "finite (ta_states TA)"
using assms by (auto simp add: ta_states_def r_states_def dest: ta_finiteD)

lemma finite_rhs_states:
  assumes "ta_finite TA"
    shows "finite (ta_rhs_states TA)"
using finite_states[OF assms, THEN rev_finite_subset, OF ta_rhs_states_subset_states] . 

lemma ta_diff_reachable_simp[simp]:
  "ta_reachable (ta_diff TA (ta_rules TA)) = {}"
by (auto simp: ta_diff_def)

abbreviation (input) eps_cl :: "(_,_)ta \<Rightarrow> _" where "eps_cl TA q \<equiv> {p. (q,p) \<in> (ta_eps TA)\<^sup>*}"
abbreviation (input) eps_icl :: "(_,_)ta \<Rightarrow> _" where "eps_icl TA q \<equiv> {p. (p,q) \<in> (ta_eps TA)\<^sup>*}"
abbreviation (input) eps_icls :: "(_,_)ta \<Rightarrow> _" where "eps_icls TA qs \<equiv> {p | q p. (p,q) \<in> (ta_eps TA)\<^sup>* \<and> q \<in> qs}"

lemma term_rule: 
  "\<lbrakk>\<And>x. t = Var x \<Longrightarrow> f1 x \<le> SPEC \<Phi>; \<And>f ts. t = Fun f ts \<Longrightarrow> f2 f ts \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> case_term f1 f2 t \<le> SPEC \<Phi>"
by (auto split: term.split)

lemma ta_rule_rule: 
  "\<lbrakk>\<And>f qs q. r = TA_rule f qs q \<Longrightarrow> s f qs q \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> case_ta_rule s r \<le> SPEC \<Phi>"
by (auto split: ta_rule.split)

lemma sum_rule: 
  "\<lbrakk>\<And>x. s = Inl x \<Longrightarrow> f1 x \<le> SPEC \<Phi>;\<And>x. s = Inr x \<Longrightarrow> f2 x \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> case_sum f1 f2 s \<le> SPEC \<Phi>"
by (auto split: sum.split)

subsection \<open>Reachability of states\<close>

definition next_res_wit_inv where
  "next_res_wit_inv rs m w \<equiv>
    case w of None \<Rightarrow> \<forall>r \<in> rs. mapM m (r_lhs_states r) = None
            | Some (q, t) \<Rightarrow> \<exists>f ts qs. t = Fun f ts \<and> (f qs \<rightarrow> q) \<in> rs \<and> mapM m qs = Some ts"

definition res_wits ::"(_,_) ta \<Rightarrow> _" where
  "res_wits TA \<equiv> do {
    let s = (ta_rules TA, Map.empty);
    s \<leftarrow> WHILE\<^sub>T (\<lambda>(todo, _). todo \<noteq> {}) (\<lambda>(todo, m). do {
      wit \<leftarrow> SPEC(next_res_wit_inv todo m);
      case wit of
        None \<Rightarrow> RETURN ({}, m) 
      | Some (q,t) \<Rightarrow> 
          let eps_cl_q = eps_cl TA q;
              m = update_all m eps_cl_q t;
              todo = {r \<in> todo . r_rhs r \<notin> eps_cl_q} in
          RETURN (todo, m)
    }) s;
    let (_,m) = s in RETURN m
  }"

abbreviation (input) "is_res_wit TA q t \<equiv> ground t \<and> q \<in> ta_res TA t"
abbreviation (input) "is_ad_res_wit TA q t \<equiv> ground t \<and> q \<in> ta_res TA (adapt_vars t)"

lemma adapt_vars_ground:
  assumes "ground t"
    shows "t = adapt_vars t"
using assms by (induction t, auto simp: map_idI) 

lemma is_ad_res_wit:
  "is_res_wit TA q t \<longleftrightarrow> is_ad_res_wit TA q t"
using adapt_vars_ground by fastforce

lemma is_ad_res_wit':
  "is_res_wit TA q (adapt_vars t) \<longleftrightarrow> is_ad_res_wit TA q t"
using adapt_vars_ground by fastforce

definition "res_wits_inv TA \<equiv> \<lambda>(todo, m).
              if todo = {} then
                dom m = ta_reachable TA \<and> (\<forall>(q,t) \<in> map_to_set m. is_ad_res_wit TA q t)
              else
                let IT = ta_diff TA todo in
                  todo \<subseteq> ta_rules TA \<and>
                  ta_rhs_states IT = ta_reachable IT \<and> ta_reachable IT = dom m \<and>
                  (\<forall>(q,t) \<in> map_to_set m. is_ad_res_wit IT q t)"

lemma res_wits_inv_complete:
  assumes inv: "res_wits_inv TA (todo, m)" "todo \<noteq> {}"
      and wit: "\<forall>r \<in> todo. mapM m (r_lhs_states r) = None"
    shows "res_wits_inv TA ({}, m)"
proof -
  note Let_def[simp] and res_wits_inv_def[simp]
  let ?ta_diff = "ta_diff TA todo"
  have "ta_reachable ?ta_diff \<subseteq> ta_reachable TA" by (rule ta_reachable_mono, simp)
  with inv have "dom m \<subseteq> ta_reachable TA" by simp
  moreover have "ta_reachable TA \<subseteq> dom m"
  proof 
    fix q
    assume res: "q \<in> ta_reachable TA"
    from ta_reachableE[OF res] obtain t where "is_res_wit TA q t" by blast
    from this have "\<exists>t. is_res_wit ?ta_diff q t"
    proof (induction t arbitrary: q, simp)
      case (Fun f ts)
        from Fun.prems obtain q' qs where
          rule: "f qs \<rightarrow> q' \<in> ta_rules TA" and
          eps: "(q',q) \<in> (ta_eps TA)\<^sup>*"  and
          length: "length qs = length ts" and
          res: "(\<forall>i<length ts. qs ! i \<in> ta_res TA (ts ! i))" by auto
        {
          fix i
          assume i: "i < length ts"
          have "ground (ts!i)" using Fun.prems(1) i by auto
          moreover have "qs!i \<in> ta_res TA (ts!i)" by (simp add: i res)
          ultimately have res_wit: "\<exists>t. is_res_wit ?ta_diff (qs!i) t" using i[THEN nth_mem, THEN Fun.IH] by blast
          then have "qs!i \<in> ta_reachable ?ta_diff" by (auto simp: ta_reachable_def)
          then have lu: "\<exists>t. m (qs!i) = Some t" using inv by auto
          note res_wit lu
        }
        note res_wit = this(1) and lu = this(2)
        show ?case proof (cases "f qs \<rightarrow> q' \<in> todo")
          case False
            from res_wit length have "\<forall> i. \<exists> t. i < length qs \<longrightarrow> is_res_wit ?ta_diff (qs!i) t" by auto
            from choice[OF this] obtain tf where tf: "\<And> i. i < length qs \<Longrightarrow> is_res_wit ?ta_diff (qs!i) (tf i)" by blast
            let ?t = "Fun f (map tf [0 ..< length qs])"
            from tf have ground: "ground ?t" by auto
            from False rule have "f qs \<rightarrow> q' \<in> ta_rules TA - todo" by blast
            with tf eps have "q \<in> ta_res ?ta_diff ?t" by (auto simp add: ta_diff_def)
            with ground show ?thesis by (intro exI[of _ ?t], auto)
          next
          case True
            from lu have "\<forall> i. \<exists> t. i < length ts \<longrightarrow> m (qs ! i) = Some t" by auto
            from choice[OF this] obtain tf where tf: "\<And> i. i < length ts \<Longrightarrow> m (qs ! i) = Some (tf i)" by blast
            obtain ts' where ts': "ts' = map tf [0 ..< length ts]" by blast
            with length have length: "length ts' = length qs" by simp
            with ts' tf have "\<And> i. i < length qs \<Longrightarrow> m (qs ! i) = Some (ts' ! i)" by simp
            then have mapM: "mapM m qs = Some ts'" by (induction rule: list_induct2[OF length], simp, fastforce)
            with wit True have False by auto then show ?thesis ..
        qed
      qed
    then have "q \<in> ta_reachable ?ta_diff" by (auto simp: ta_reachable_def)
    then show "q \<in> dom m" using inv by simp
  qed
  ultimately have "ta_reachable TA = dom m" by blast
  then show ?thesis using inv ta_res_mono[of ?ta_diff TA] by (force simp: map_to_set_def)
qed

lemma res_wits_inv_preserve:
  assumes inv: "res_wits_inv TA (todo, m)" "todo \<noteq> {}"
      and rule: "TA_rule f qs q \<in> todo" and mapM: "mapM m qs = Some ts"
  defines "todo' \<equiv> {r \<in> todo. r_rhs r \<notin> eps_cl TA q}"
      and "m' \<equiv> update_all m (eps_cl TA q) (Fun f ts)"
    shows "res_wits_inv TA (todo', m')"
proof -
  note Let_def[simp] and res_wits_inv_def[simp]
  let ?epcl = "eps_cl TA q"
  let ?old_ta = "ta_diff TA todo"
  let ?new_ta = "ta_diff TA todo'"
  
  have ta_subset: "ta_subset ?old_ta ?new_ta" by (auto simp add: ta_subset_def ta_diff_def todo'_def)
  from ta_reachable_mono[OF this] have subset: "ta_reachable ?old_ta \<subseteq> ta_reachable ?new_ta" .
  from inv have todo: "todo \<subseteq> ta_rules TA" by simp
  note mapM = mapM_Some[OF mapM]
  
  from mapM have length: "length qs = length ts" by simp
  moreover from rule todo have "f qs \<rightarrow> q \<in> ta_rules ?new_ta" by (auto simp add: ta_diff_def todo'_def)
  moreover {
    fix i assume i: "i < length ts"
    with inv mapM have "is_ad_res_wit ?old_ta (qs!i) (ts!i)" by (auto simp: map_to_set_def)
    with ta_res_mono[OF ta_subset] have "is_ad_res_wit ?new_ta (qs!i) (ts!i)" by auto
  }
  ultimately have res: "is_ad_res_wit ?new_ta q (Fun f ts)" by (auto simp add: in_set_conv_nth rule)
  then have reach: "q \<in> ta_reachable ?new_ta" unfolding ta_reachable_def using ground_adapt_vars by blast 

  note rhs_simps = ta_rhs_states_def ta_diff_def todo'_def
  have eq_rhs: "ta_rhs_states ?new_ta = ta_rhs_states ?old_ta \<union> ?epcl" (is "?newrhs = ?oldrhs")
  proof
    show "?newrhs \<subseteq> ?oldrhs" by (auto simp: rhs_simps intro: rtrancl_trans)
    show "?oldrhs \<subseteq> ?newrhs" proof
      fix p assume "p \<in> ?oldrhs"
      then show "p \<in> ?newrhs" proof (rule UnE)
        assume "p \<in> ?epcl"
        with rule todo show "p \<in> ?newrhs" by (auto simp: rhs_simps intro!: bexI)
      qed (auto simp: rhs_simps)
    qed
  qed

  have eq_reach: "ta_reachable ?new_ta = ta_reachable ?old_ta \<union> ?epcl" (is "?newres = ?oldres")
  proof
    show "?newres \<subseteq> ?oldres" proof
      fix p assume "p \<in> ?newres"
      with ta_reachabe_rhs_states have "p \<in> ?newrhs" by (rule set_mp)
      with inv show "p \<in> ?oldres" unfolding eq_rhs by simp
    qed
    show "?oldres \<subseteq> ?newres" proof
      fix p assume "p \<in> ?oldres"
      then show "p \<in> ?newres" proof (rule UnE)
        assume "p \<in> eps_cl TA q"
        with ta_reachableI_eps'[OF reach] show "p \<in> ?newres" by simp
      qed (auto dest: set_mp[OF subset])
    qed
  qed
  
  have todo': "todo' \<subseteq> ta_rules TA" unfolding todo'_def using todo by auto
  have m': "(\<forall>(q, t)\<in>map_to_set m'. is_ad_res_wit ?new_ta q t)" unfolding m'_def
  proof (intro update_all_ballI, goal_cases)
    case (1 p)
      then have "p \<in> eps_cl ?new_ta q" by simp
      note rtrancl_trans[OF _ this[simplified]]
      with res show ?case by auto
    next
    case (2 p t)
      with inv have "is_ad_res_wit ?old_ta p t" by auto
      with ta_res_mono[OF ta_subset] show ?case by auto
  qed

  from eq_reach eq_rhs todo' m' inv
  show ?thesis by (cases "todo' = {}", simp_all add: m'_def)
qed

lemma res_wits_inv_finite:
  assumes fin: "ta_finite TA"
      and inv: "res_wits_inv TA (todo, m)" "todo \<noteq> {}"
    shows "finite todo"
proof -
  from inv have "todo \<subseteq> ta_rules TA" by (simp add: res_wits_inv_def Let_def)
  then show "finite todo" by (rule finite_subset[of _ "ta_rules TA"], blast intro: ta_finiteD[OF fin])
qed

lemma res_wits_correct:
assumes "ta_finite TA"
  shows "res_wits TA \<le> SPEC(\<lambda>m. res_wits_inv TA ({}, m))"
unfolding res_wits_def next_res_wit_inv_def[abs_def]
proof (refine_vcg WHILET_rule[where R = "measure (card o fst)" and I="res_wits_inv TA"], goal_cases)
  case 3
    then show ?case by (intro res_wits_inv_complete, auto)
  next
  case prems: (4 _ todo m wit)
    from prems(1-3) res_wits_inv_finite[OF assms] have "finite todo" "todo \<noteq> {}" by auto
    then show ?case unfolding prems(3) by auto
  next
  case prems: (5 _ todo m wit _ q t)
    from prems(4-6) obtain f ts qs
      where t: "t = Fun f ts" and wit: "f qs \<rightarrow> q \<in> todo" "mapM m qs = Some ts" by auto
    show ?case unfolding t by (intro res_wits_inv_preserve, insert prems(1-3) wit, auto)
  next
  case prems: (6 _ todo m wit _ q t)
    from this obtain r f qs where "r = f qs \<rightarrow> q" "f qs \<rightarrow> q \<in> todo" by auto
    then have "r_rhs r \<in> eps_cl TA q" "r \<in> todo" by simp_all
    then have subset: "{r \<in> todo. r_rhs r \<notin> eps_cl TA q} \<subset> todo" by auto
    moreover from prems(1-3) res_wits_inv_finite[OF assms] have "finite todo" by auto
    ultimately show ?case unfolding prems(3) by (auto intro: psubset_card_mono)
  next
qed (simp_all add: res_wits_inv_def)

definition ta_only_res_wits :: "(_,_)ta \<Rightarrow> _" where
  "ta_only_res_wits TA wits \<equiv> 
    let fin = {q \<in> ta_final TA. wits q \<noteq> None};
        rs = {r \<in> ta_rules TA. \<forall>q \<in> set (r_lhs_states r). wits q \<noteq> None};
        eps = {q \<in> ta_eps TA. wits (fst q) \<noteq> None} in
          ta.make fin rs eps"

lemma ta_only_reach_res_wit:
  "is_ad_res_wit (ta_only_reach TA) q t \<longleftrightarrow> is_ad_res_wit TA q t" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  have subset: "ta_subset (ta_only_reach TA) TA" by (auto simp add: ta_subset_def ta_restrict_def)
  assume "?lhs"
  with ta_res_mono[OF subset] show "?rhs" by auto
  next
  assume *: "?rhs"
  then have "vars_term (adapt_vars t) = {}" using ground_vars_term_empty ground_adapt_vars by force
  with * ta_res_only_reach[of _ TA "adapt_vars t" q] show "?lhs" by force 
qed

lemma ta_only_prod_reach_res_wit:
  assumes "is_ad_res_wit (ta_only_prod (ta_only_reach TA)) q t"
     shows "is_ad_res_wit TA q t"
proof -
  let ?TA = "ta_only_prod (ta_only_reach TA)"
  have subset: "ta_subset ?TA TA" by (auto simp add: ta_subset_def ta_restrict_def)
  with ta_res_mono[OF subset] assms show ?thesis by auto
qed

lemma ta_only_reach_reachable:
  "ta_reachable (ta_only_reach TA) = ta_reachable TA"
proof -
  note rdefs = ta_reachable_def[of "ta_only_reach TA"] is_ad_res_wit ta_only_reach_res_wit 
  show ?thesis unfolding rdefs by (simp add: ta_reachable_def is_ad_res_wit)
qed

lemma ta_only_res_wits:
assumes "dom wits = ta_reachable TA"
  shows "ta_only_res_wits TA wits = ta_only_reach TA"
proof -
  let ?fin = "{q \<in> ta_final TA. wits q \<noteq> None}"
  let ?eps = "{q \<in> ta_eps TA. wits (fst q) \<noteq> None}"
  let ?rs = "{r \<in> ta_rules TA. \<forall>q\<in>set (r_lhs_states r). wits q \<noteq> None}"
  let ?res = "ta_reachable TA"
  note [simp] = res_wits_inv_def Let_def
  from assms have fin: "?fin = ta_final TA \<inter> ?res" by auto
  have "?eps \<subseteq> ?res \<times> ?res" proof
    fix q p assume *: "(q,p) \<in> ?eps"
    with assms have "q \<in> ?res" by auto
    moreover from ta_reachableI_eps[OF this] * have "p \<in> ?res" by auto
    ultimately show "(q,p) \<in> ?res \<times> ?res" by blast
  qed
  with assms have eps: "?eps = ta_eps TA \<inter> (?res \<times> ?res)" by auto
  have "?rs = {r \<in> ta_rules TA. r_states r \<subseteq> ta_reachable TA}" (is "?lhs = ?rhs") proof
    show "?lhs \<subseteq> ?rhs" proof
      fix r assume *: "r \<in> ?lhs"
      from this obtain f qs q where r: "r = f qs \<rightarrow> q" by (cases r)
      from * assms have qs: "set qs \<subseteq> ta_reachable TA" by (auto simp: r)
      then have "\<forall>i. \<exists>t. i \<in> set qs \<longrightarrow> is_res_wit TA i t" by (auto simp: ta_reachable_def)
      from choice[OF this] obtain w where w: "\<And>i. i \<in> set qs \<Longrightarrow> is_res_wit TA i (w i)" by blast
      with * have "q \<in> ta_res TA (Fun f (map w qs))" by (simp add: r, intro exI[of _ q] exI[of _ qs], auto)
      moreover from w have "ground (Fun f (map w qs))" by simp
      ultimately have "q \<in> ta_reachable TA" unfolding ta_reachable_def by blast
      with * qs show "r \<in> ?rhs" by (auto simp add: r_states_def r)
    qed
    show "?rhs \<subseteq> ?lhs" proof
      fix r assume *: "r \<in> ?rhs"
      then have "set (r_lhs_states r) \<subseteq> ta_reachable TA" by (auto simp: r_states_def)
      with * assms show "r \<in> ?lhs" by auto
    qed
  qed
  from this eps fin show ?thesis by (simp add: ta_restrict_def ta.make_def ta_only_res_wits_def)
qed

lemma ta_only_reach_inv:
  "res_wits_inv TA ({}, m) \<Longrightarrow> res_wits_inv (ta_only_reach TA) ({}, m)"
by (auto simp: res_wits_inv_def ta_only_reach_res_wit[of _ _ TA, symmetric] map_to_set_def ta_only_reach_reachable)

definition "ta_only_res TA \<equiv>
  (res_wits TA::('a \<Rightarrow> ('b, unit) term option) nres) \<bind> RETURN o ta_only_res_wits TA"

lemma ta_only_res:
assumes "ta_finite TA"
  shows "ta_only_res TA \<le> RETURN(ta_only_reach TA)"
unfolding ta_only_res_def
by (refine_vcg res_wits_correct[OF assms, THEN order_trans])
   (auto intro: ta_only_res_wits simp: res_wits_inv_def)

subsection \<open>Productivity of states\<close>

abbreviation (input) "is_prs_wit TA q C \<equiv> ta_res TA C\<langle>Var q\<rangle> \<inter> ta_final TA \<noteq> {}"

lemma prs_wit_prod:
  assumes "is_prs_wit TA q C"
    shows "q \<in> ta_productive TA"
using assms by (auto simp add: ta_productive_def)

lemma is_prs_wit_mono:
  assumes sub: "ta_subset TA TA'"
      and wit: "is_prs_wit TA q C"
    shows "is_prs_wit TA' q C"
proof -
  from wit obtain qf where res: "qf \<in> ta_res TA C\<langle>Var q\<rangle>" and fin: "qf \<in> ta_final TA" by auto
  with ta_res_mono[OF sub] have "qf \<in> ta_res TA' C\<langle>Var q\<rangle>" by auto
  with fin sub show ?thesis by (auto simp add: ta_subset_def)
qed

lemma is_prs_wit_compose:
  assumes prs: "is_prs_wit TA q C"
      and res: "q \<in> ta_res TA C'\<langle>Var q'\<rangle>"
    shows "is_prs_wit TA q' (C \<circ>\<^sub>c C')"
proof -
  from prs obtain qf where qf_res: "qf \<in> ta_res TA C\<langle>Var q\<rangle>" and qf_fin: "qf \<in> ta_final TA" by auto
  from res qf_res have "qf \<in> ta_res TA C\<langle>C'\<langle>Var q'\<rangle>\<rangle>" by (rule ta_res_ctxt)
  with qf_fin show ?thesis by auto
qed

lemma ta_productive_mono:
  assumes "ta_subset TA TA'"
    shows "ta_productive TA \<subseteq> ta_productive TA'"
using is_prs_wit_mono[OF assms] unfolding ta_productive_def by blast

lemma ta_productive_empty:
assumes "ta_rules TA = {}"
  shows "ta_productive TA = eps_icls TA (ta_final TA)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix q assume "q \<in> ?lhs"
    from ta_productiveE[OF this]
    obtain qf C where "qf \<in> ta_res TA C\<langle>Var q\<rangle>" "qf \<in> ta_final TA" by auto
    then show "q \<in> ?rhs" by (cases C, auto simp: assms)
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix q assume "q \<in> ?rhs"
    from this obtain qf where res: "(q, qf) \<in> (ta_eps TA)\<^sup>*" and fin: "qf \<in> ta_final TA" by auto
    then show "q \<in> ?lhs" by (intro ta_productiveI[where C = \<box>], auto)
  qed
qed

lemma ta_diff_productive_final[simp]:
  "ta_productive (ta_diff TA (ta_rules TA)) = eps_icls TA (ta_final TA)"
using ta_productive_empty[of "ta_diff TA (ta_rules TA)"] by (simp add: ta_diff_rules)

definition ta_fin_r_states :: "(_,_)ta \<Rightarrow> _" where
  "ta_fin_r_states TA \<equiv> eps_icls TA {q | q r. q \<in> r_states r \<and> r \<in> ta_rules TA \<or> q \<in> ta_final TA}"

lemma ta_productive_eps_r_states:
  "ta_productive TA \<subseteq> ta_fin_r_states TA"
proof
  fix q assume "q \<in> ta_productive TA"
  from ta_productiveE[OF this] obtain qf C where
    res: "qf \<in> ta_res TA (C\<langle>Var q\<rangle>)" and
    fin: "qf \<in> ta_final TA" by blast
  from fin have "qf \<in> ta_fin_r_states TA" by (auto simp: ta_fin_r_states_def)
  with res show "q \<in> ta_fin_r_states TA"
  proof (induction C arbitrary: qf)
    case (More f ss1 ctxt ss2)
      let ?lqs = "Suc (length ss1 + length ss2)" and ?mres = "map (ta_res TA)"
      from More.prems(1) obtain qs qt where
        len: "length qs = ?lqs" and
        rule: "f qs \<rightarrow> qt \<in> ta_rules TA" and
        qs: "\<And>i. i < ?lqs \<Longrightarrow> qs ! i \<in> (?mres ss1 @ ta_res TA ctxt\<langle>Var q\<rangle> # ?mres ss2) ! i" by auto
      from qs obtain q' where q': "q' = qs ! length ss1" by blast
      then have res: "q' \<in> ta_res TA ctxt\<langle>Var q\<rangle>" using qs[of "length ss1"] by (simp add: nth_append)
      have "q' \<in> r_states (f qs \<rightarrow> qt)" by (simp add: q' r_states_def len)
      then have rhs: "q' \<in> ta_fin_r_states TA" using rule by (auto simp: ta_fin_r_states_def)
      from More.IH[OF res rhs] show ?case .
  qed (auto dest: rtrancl_trans simp: ta_fin_r_states_def)
qed

lemma ta_productive_states:
  shows "ta_productive TA \<subseteq> ta_states TA"
proof (rule subset_trans[OF ta_productive_eps_r_states], rule)
  let ?qs = "{q | q r. q \<in> r_states r \<and> r \<in> ta_rules TA \<or> q \<in> ta_final TA}"
  fix q assume "q \<in> ta_fin_r_states TA"
  from this obtain q' where "(q, q') \<in> (ta_eps TA)\<^sup>*" "q' \<in> ?qs" by (auto simp: ta_fin_r_states_def)
  then show "q \<in> ta_states TA" by (induction rule: converse_rtrancl_induct, auto simp: ta_states_def)
qed

primrec add_prs_wit_aux where
  "add_prs_wit_aux TA m C f qs1 [] = m"
| "add_prs_wit_aux TA m C f qs1 (q#qs2) = 
    (let m = update_all m (eps_icl TA (the_Var q)) (C \<circ>\<^sub>c More f qs1 \<box> qs2)
     in add_prs_wit_aux TA m C f (qs1@[q]) qs2)"

lemma add_prs_wit_aux_simps[simp]:
  "add_prs_wit_aux (ta_diff TA x) m C f qs1 qs2 = add_prs_wit_aux TA m C f qs1 qs2"
  "dom (add_prs_wit_aux TA m C f qs1 qs2) = dom m \<union> eps_icls TA (the_Var ` set qs2)"
by (induction qs2 arbitrary: qs1 m, auto)

lemma add_prs_wit_auxD:
  assumes "add_prs_wit_aux TA m C f qs1 qs2 q' = Some C'"
  obtains
    (keep) "q' \<notin> eps_icls TA (the_Var ` set qs2)" and "m q' = Some C'"
  | (new) it1 q it2 where
      "q' \<in> eps_icl TA (the_Var q)" and "qs1@qs2 = it1@q#it2" and "C' = (C \<circ>\<^sub>c More f it1 \<box> it2)"
using assms proof (induction qs2 arbitrary: qs1 m)
  case (Cons q qs2)
    let ?invcl = "eps_icl TA (the_Var q)" and ?C' = "C \<circ>\<^sub>c More f qs1 \<box> qs2"
    let ?m' = "update_all m ?invcl ?C'"
    {
      assume q': "q' \<notin> eps_icls TA (the_Var ` set qs2)" and lu: "?m' q' = Some C'"
      have thesis proof (cases "q' \<in> ?invcl")
        case True
          with lu have "C' = ?C'" by (simp add: update_all_def)
          from Cons.prems(2)[OF True _ this] show ?thesis by simp
        next
        case False
          with lu have "m q' = Some C'" by (simp add: update_all_def)
          from Cons.prems(1)[OF _ this] False q' show ?thesis by auto
      qed
    }
    moreover note IH = Cons.IH[OF _ _ Cons.prems(3)[simplified]] Cons.prems(2)
    ultimately show ?thesis by auto
qed simp

definition add_prs_wit where
  "add_prs_wit TA m C r \<equiv> case r of (f qs \<rightarrow> q) \<Rightarrow> add_prs_wit_aux TA m C f [] (map Var qs)"

lemma add_prs_wit_diff[simp]:
  "add_prs_wit (ta_diff TA x) m C r = add_prs_wit TA m C r"
by (cases r, simp add: add_prs_wit_def)

lemma add_prs_wit_keys[simp]:
   "dom (add_prs_wit TA m C (f qs \<rightarrow> q)) = dom m \<union> eps_icls TA (set qs)"
unfolding add_prs_wit_def by (simp add: image_image)

lemma add_prs_witD:
  assumes rule: "(f qs \<rightarrow> q) \<in> ta_rules TA" and prs: "is_prs_wit TA q C"
      and lu: "add_prs_wit TA m C (f qs \<rightarrow> q) q' = Some C'"
  obtains
    (keep) "q' \<notin> eps_icls TA (set qs)" and "m q' = Some C'"
  | (new) "q' \<in> eps_icls TA (set qs)" and "is_prs_wit TA q' C'"
proof (goal_cases)
  case prems : 1
  note lu = lu[unfolded add_prs_wit_def ta_rule.case]
  then show ?thesis proof (cases rule: add_prs_wit_auxD)
    case keep
      with prems(1) show ?thesis by (simp add: image_image)
    next
    case (new it1 iw it2)
      let ?CI = "More f it1 \<box> it2"
      from new(2) have id: "map Var qs = it1 @ [iw] @ it2" by simp
      from id obtain qs1 where qs1: "it1 = map Var qs1" by (metis map_eq_append_conv) 
      from id obtain qs2 where qs2: "it2 = map Var qs2" by (metis map_eq_append_splits(2))
      from id obtain qw' where "[iw] = map Var qw'" by (metis map_eq_append_splits(2))
      then obtain qw where qw: "iw = Var qw" by auto 
      have inj: "inj Var" by (metis injI term.inject(1))
      have qs: "qs = qs1 @ qw # qs2" by (rule iffD1[OF inj_eq, of "map Var"], insert new(2), simp_all add: inj qs1 qs2 qw)
      note qss[simp] = qs qs1 qs2
      have "q \<in> ta_res TA ?CI\<langle>Var q'\<rangle>"
      proof -
        {
          fix i
          assume "i < length qs"
          then have "i < length qs1 \<or> i = length qs1 \<or> (i > length qs1 \<and> i < length qs)" by auto
          then have "qs ! i \<in> (map (ta_res TA) it1 @ {q. (q', q) \<in> (ta_eps TA)\<^sup>*} # map (ta_res TA) it2) ! i"
          proof (elim disjE)
            assume *: "i < length qs1"
            then have map: "\<And>f. i < length (map f qs1)" by auto
            then show ?thesis by (simp add: append_Cons_nth_left[OF *] append_Cons_nth_left[OF map])
            next
            assume *: "i = length qs1"
            then have map: "\<And>f. i = length (map f qs1)" by auto
            from new(1) have "qw \<in> {q. (q', q) \<in> (ta_eps TA)\<^sup>*}" by (auto simp add: qw)
            then show ?thesis by (simp add: append_Cons_nth_middle[OF *] append_Cons_nth_middle[OF map])
            next
            assume *: "i > length qs1 \<and> i < length qs"
            from this obtain j where j: "i - Suc (length qs1) = j" "j < length qs2" by auto
            from * have map: "\<And>f. i > length (map f qs1)" by auto
            then show ?thesis by (simp add: nth_append j)
          qed
        }
        then show ?thesis by (auto intro!: exI[of _ q] exI[of _ qs] rule)
      qed
      note is_prs_wit_compose[OF prs this]
      then have "is_prs_wit TA q' C'" by (simp add: new(3))
      moreover have "q' \<in> eps_icls TA (set qs)" using new(1,2) by auto
      ultimately show ?thesis using prems(2) by blast
  qed
qed

definition prs_wits :: "('a, 'b) ta \<Rightarrow> ('a \<Rightarrow> ('b,'a) ctxt option) nres"
    where "prs_wits TA \<equiv> do {
  let m = update_all Map.empty (eps_icls TA (ta_final TA)) \<box>;
  let s = (False, ta_rules TA, m);
  s \<leftarrow> WHILE\<^sub>T (\<lambda>(done, _, _). \<not> done) (\<lambda>(_, todo, m).
        FOREACH todo (\<lambda>r (done, todo, m).
           case m (r_rhs r) of
             Some C \<Rightarrow> RETURN (False, todo, add_prs_wit TA m C r)
           | None \<Rightarrow> RETURN (done, insert r todo, m)
        ) (True, {}, m)
  ) s;
  let (_,_,r) = s in
  RETURN r
}"

definition "prs_wits_inner_inv TA todo it \<equiv> \<lambda>(done, todo', m).
    (if done then
      (todo - it) = todo' \<and> (\<forall>r \<in> todo'. r_rhs r \<notin> dom m)
    else
      todo' \<subset> (todo - it)) \<and>
    (let TA' = ta_diff (ta_diff TA it) todo' in
      ta_fin_r_states TA' = ta_productive TA' \<and> ta_productive TA' = dom m \<and>
      (\<forall>(q,C) \<in> map_to_set m. is_prs_wit TA' q C))"

definition "prs_wits_inv TA \<equiv> \<lambda>(done, todo, m).
    (done \<longrightarrow> ta_productive TA = dom m) \<and> todo \<subseteq> ta_rules TA \<and> 
    (let TA' = ta_diff TA todo in
      ta_fin_r_states TA' = ta_productive TA' \<and> ta_productive TA' = dom m \<and>
      (\<forall>(q,C) \<in> map_to_set m. is_prs_wit TA' q C))"

abbreviation "prs_wits_term_measure \<equiv> {(True, False)} <*lex*> measure (card o fst)"

lemma prs_wits_term_measure_wf:
  "wf prs_wits_term_measure"
by (rule wf_lex_prod, simp add: wf_def, simp)

lemma prs_wits_inv_initial:
  "prs_wits_inv TA (False, ta_rules TA, update_all Map.empty (eps_icls TA (ta_final TA)) \<box>)"
by (auto simp: prs_wits_inv_def ta_diff_rules map_to_set_def ta_fin_r_states_def update_all_def split: if_splits)

lemma prs_wits_inner_inv_preserve_none:
  assumes inv: "prs_wits_inner_inv TA todo it (done, todo', m)"
      and it: "r \<in> it" "it \<subseteq> todo" and lu: "m (r_rhs r) = None"
    shows "prs_wits_inner_inv TA todo (it - {r}) (done, insert r todo', m)"
proof -
  let ?old_ta = "ta_diff (ta_diff TA it) todo'"
  let ?new_ta = "ta_diff (ta_diff TA (it - {r})) (insert r todo')"
  from it have same: "?new_ta = ?old_ta" by (auto simp: ta_diff_def)
  from inv it lu show ?thesis unfolding prs_wits_inner_inv_def by (cases "done", auto simp: same)
qed

lemma prs_wits_inner_inv_preserve_some:
  assumes inv: "prs_wits_inner_inv TA todo it (done, todo', m)"
      and it: "r \<in> it" "it \<subseteq> todo" "todo \<subseteq> ta_rules TA" and lu: "m (r_rhs r) = Some C"
    shows "prs_wits_inner_inv TA todo (it - {r}) (False, todo', add_prs_wit TA m C r)"
proof -
  note prs_wits_inner_inv_def[simp] and Let_def[simp] and map_to_set_def[simp]
  obtain f qs q where r: "r = (f qs \<rightarrow> q)" by (cases r)
  let ?old_ta = "ta_diff (ta_diff TA it) todo'"
  let ?new_ta = "ta_diff (ta_diff TA (it - {r})) todo'"
  let ?new_m = "add_prs_wit ?new_ta m C (f qs \<rightarrow> q)"
  let ?new_prs = "eps_icls ?new_ta (set qs)"
  have ta_sub: "ta_subset ?old_ta ?new_ta" by (auto simp add: ta_diff_def ta_subset_def)
  from it inv have "r \<in> todo" "r \<notin> todo'" "r \<in> ta_rules TA" by (auto split: if_splits)
  then have rule: "(f qs \<rightarrow> q) \<in> ta_rules ?new_ta" by (auto simp add: ta_diff_def r)
  then have rules: "ta_rules ?new_ta = insert (f qs \<rightarrow> q) (ta_rules ?old_ta)" by (auto simp add: ta_diff_rules r)
  from lu inv have "is_prs_wit ?old_ta q C" by (auto simp: r)
  note is_wit_new = is_prs_wit_mono[OF ta_sub this]
  
  {
    fix q' C'
    assume *: "?new_m q' = Some C'"
    with rule is_wit_new have "is_prs_wit ?new_ta q' C'" proof (cases rule: add_prs_witD)
      case keep
        with inv is_prs_wit_mono[OF ta_sub] show ?thesis by simp
    qed simp
  }
  note is_prs_wits = this
  
  have "q \<in> dom m" using lu by (auto simp: r) 
  then have "q \<in> ta_fin_r_states ?old_ta" using inv by simp
  then have "eps_icl ?new_ta q \<subseteq> ta_fin_r_states ?old_ta" by (auto simp: ta_fin_r_states_def dest: rtrancl_trans)
  then have states: "ta_fin_r_states ?new_ta = ta_fin_r_states ?old_ta \<union> ?new_prs"
    by (auto simp add: ta_fin_r_states_def r_states_def rules, force)
  
  have prs: "ta_productive ?new_ta = ta_productive ?old_ta \<union> ?new_prs" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof
      fix q' assume "q' \<in> ?lhs"
      then have "q' \<in> ta_fin_r_states ?new_ta" using ta_productive_eps_r_states by fastforce
      then have "q' \<in> ta_fin_r_states ?old_ta \<union> ?new_prs" by (simp add: states)
      then show "q' \<in> ?rhs" using inv by simp
    qed
    show "?rhs \<subseteq> ?lhs"
    proof
      fix q' assume "q' \<in> ?rhs"
      then have "q' \<in> ta_productive ?old_ta \<or> q' \<in> ?new_prs" by blast
      then show "q' \<in> ?lhs" proof (elim disjE)
        assume "q' \<in> ta_productive ?old_ta"
        then show ?thesis using ta_productive_mono[OF ta_sub] by auto
        next
        assume *: "q' \<in> ?new_prs"
        from this obtain q'' where q'': "q'' \<in> set qs" "(q', q'') \<in> (ta_eps TA)\<^sup>*" by auto
        from this obtain qs1 qs2 where qs: "qs = qs1@q''#qs2" by (auto simp add: in_set_conv_decomp)
        let ?C = "More f (map Var qs1) \<box> (map Var qs2)"
        have "q \<in> ta_res ?new_ta (Fun f (map Var qs))" by (simp, intro exI conjI, rule rule, simp_all)
        then have "q \<in> ta_res ?new_ta ?C\<langle>Var q''\<rangle>" by (simp add: qs)
        note is_prs_wit_compose[OF is_wit_new this]
        moreover have "q'' \<in> ta_res ?new_ta \<box>\<langle>Var q'\<rangle>" using * q'' by simp
        ultimately show ?thesis by (rule is_prs_wit_compose[THEN prs_wit_prod])
      qed
    qed
  qed
  
  have cur: "dom ?new_m = dom m \<union> ?new_prs" by simp
  from inv it have "todo' \<subset> todo - (it - {r})" by (auto split: if_splits)
  note new_add_inv = this states prs cur[folded r] is_prs_wits[folded r]
  with inv show ?thesis by simp
qed

lemma prs_wits_inner_inv_to_outer:
  assumes inv: "prs_wits_inner_inv TA todo {} (done, todo', m)"
      and todo: "todo \<subseteq> ta_rules TA"
    shows "prs_wits_inv TA (done, todo', m)"
proof -
  note prs_wits_inner_inv_def[simp] and prs_wits_inv_def[simp]
  note Let_def[simp] and map_to_set_def[simp]
  let ?ta_diff = "ta_diff TA todo'"
  have ta_sub: "ta_subset ?ta_diff TA" by (auto simp add: ta_subset_def ta_diff_def)
  {
    assume "done"
    with inv have complete: "\<forall>r \<in> todo'. r_rhs r \<notin> ta_fin_r_states ?ta_diff" by auto
    have "ta_productive TA \<subseteq> ta_productive ?ta_diff" proof
      fix q
      assume full: "q \<in> ta_productive TA"
      from ta_productiveE[OF this] obtain qf C
        where res: "qf \<in> ta_res TA C\<langle>Var q\<rangle>" and fin: "qf \<in> ta_final TA" by blast
      from fin have "qf \<in> ta_fin_r_states ?ta_diff" by (auto simp: ta_fin_r_states_def)
      with res have "\<exists>C qf. qf \<in> ta_res ?ta_diff C\<langle>Var q\<rangle> \<and> qf \<in> ta_fin_r_states ?ta_diff"
      proof (induction C arbitrary: qf)
        case Hole
          then show ?case by (simp, intro exI[of _ \<box>] exI[of _ qf], simp)
        next
        case (More f ss1 ctxt ss2)
          let ?lqs = "Suc (length ss1 + length ss2)" and ?mres = "map (ta_res TA)"
          from More.prems(1) obtain qs qt
            where eps: "(qt, qf) \<in> (ta_eps TA)\<^sup>*"
            and len: "length qs = ?lqs"
            and rule: "f qs \<rightarrow> qt \<in> ta_rules TA"
            and qs: "\<And>i. i < ?lqs \<Longrightarrow> qs ! i \<in> (?mres ss1 @ ta_res TA ctxt\<langle>Var q\<rangle> # ?mres ss2) ! i" by auto
          from qs obtain q' where q': "q' = qs ! length ss1" by blast
          then have res: "q' \<in> ta_res TA ctxt\<langle>Var q\<rangle>" using qs[of "length ss1"] by (simp add: nth_append)
          have "qt \<in> ta_fin_r_states ?ta_diff" using eps More.prems(2) by (auto simp: ta_fin_r_states_def dest: rtrancl_trans)
          with complete have "f qs \<rightarrow> qt \<notin> todo'" by auto
          then have "f qs \<rightarrow> qt \<in> ta_rules (ta_diff TA todo')" using rule by (simp add: ta_diff_rules)
          then have "set qs \<subseteq> ta_fin_r_states ?ta_diff" by (force simp: ta_fin_r_states_def r_states_def)
          then have "q' \<in> ta_fin_r_states ?ta_diff" by (auto simp add: q' len)
          from More.IH[OF res this] show ?case .
      qed
      from this obtain qp C
        where res: "qp \<in> ta_res ?ta_diff C\<langle>Var q\<rangle>" and fin: "qp \<in> ta_fin_r_states ?ta_diff" by blast
      from fin inv have "qp \<in> dom m" by simp
      from this obtain C' where "is_prs_wit ?ta_diff qp C'" using inv by force
      note is_prs_wit_compose[OF this res]
      from prs_wit_prod[OF this] show "q \<in> ta_productive ?ta_diff" .
    qed
    then have "ta_productive TA = ta_productive (ta_diff TA todo')" using ta_productive_mono[OF ta_sub] by blast
    with inv have "ta_productive TA = dom m" by simp
  }
  with todo show ?thesis using inv by (auto split: if_splits)
qed

abbreviation "prs_wits_spec TA m \<equiv> dom m = ta_productive TA \<and> (\<forall>(q,C) \<in> map_to_set m. is_prs_wit TA q C)"

lemma prs_wits_correct:
assumes "ta_finite TA"
  shows "prs_wits TA \<le> SPEC(prs_wits_spec TA)"
unfolding prs_wits_def
proof (refine_vcg WHILET_rule[where R = "prs_wits_term_measure" and I="prs_wits_inv TA"], goal_cases)
  case 2
    show ?case using prs_wits_inv_initial .

  case outer_prems: (3 _ "done" _ todo)
    then have "\<not> done" by auto
    from outer_prems have "todo \<subseteq> ta_rules TA" by (simp add: prs_wits_inv_def)
    then show ?case 
    proof (refine_vcg FOREACH_rule[where I = "prs_wits_inner_inv TA todo"], goal_cases)
      case 2
        with outer_prems show ?case by (simp add: prs_wits_inner_inv_def prs_wits_inv_def)
      next
      case 3
        then show ?case by (intro prs_wits_inner_inv_preserve_none, simp_all)
      next
      case 4
        then show ?case by (intro prs_wits_inner_inv_preserve_some, simp_all)
      next
      case prems: (5 s)
        obtain done' todo' m where s: "s = (done', todo', m)" by (cases s)
        from prems show ?case unfolding s by (intro prs_wits_inner_inv_to_outer, simp_all)
      next
      case prems: (6 s)
        obtain done' todo' m where s: "s = (done', todo', m)" by (cases s)
        show ?case proof (cases done')
          case True
            with \<open>\<not> done\<close> show ?thesis  by (simp add: s outer_prems)
          next
          case False
            from prems assms have fin: "finite todo" by (auto dest: finite_subset ta_finiteD)
            from \<open>\<not> done'\<close> prems have sub: "todo' \<subset> todo" by (simp add: s prs_wits_inner_inv_def)
            note psubset_card_mono[OF fin sub]
            then show ?thesis using \<open>\<not> done'\<close> \<open>\<not> done\<close> by (simp add: s outer_prems)
        qed
    qed (insert assms, auto dest: finite_subset ta_finiteD)
  next

  case prems: (5 s don _ todo cur)
    have "ta_subset (ta_diff TA todo) TA" by (auto simp add: ta_subset_def ta_diff_def)
    from is_prs_wit_mono[OF this] prems show ?case by (simp add: prs_wits_inv_def Let_def map_to_set_def)

qed (simp_all add: prs_wits_inv_def prs_wits_term_measure_wf)

definition ta_only_prs_wits :: "(_,_)ta \<Rightarrow> _" where
  "ta_only_prs_wits TA wits \<equiv>
    let fin = {q \<in> ta_final TA. wits q \<noteq> None};
        rs = {r \<in> ta_rules TA. wits (r_rhs r) \<noteq> None};
        eps = {q \<in> ta_eps TA. wits (snd q) \<noteq> None} in
          ta.make fin rs eps"

lemma ta_only_prod_prs_wit:
  "is_prs_wit (ta_only_prod TA) q C \<longleftrightarrow> is_prs_wit TA q C" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  have subset: "ta_subset (ta_only_prod TA) TA" by (auto simp add: ta_subset_def ta_restrict_def)
  assume "?lhs"
  with is_prs_wit_mono[OF subset] show "?rhs" by blast
  next
  assume "?rhs"
  from this obtain qf where res: "qf \<in> ta_res TA C\<langle>Var q\<rangle>" and fin: "qf \<in> ta_final TA" by blast
  note ta_productive_final[OF fin] ta_res_only_prod[OF res] fin
  then show "?lhs" by (auto simp: ta_restrict_def)
qed

lemma ta_only_prod_productive:
  "ta_productive (ta_only_prod TA) = ta_productive TA"
proof -
  have alt_def: "\<And>q TA. (\<exists>q' C. q' \<in> ta_res TA C\<langle>Var q\<rangle> \<and> q' \<in> ta_final TA) \<longleftrightarrow> (\<exists>C. is_prs_wit TA q C)" by blast
  note prs_def = ta_productive_def[of "ta_only_prod TA"]
  show ?thesis unfolding prs_def alt_def ta_only_prod_prs_wit by (auto simp: ta_productive_def)
qed

lemma ta_only_prs_wits:
assumes "dom wits = ta_productive TA"
  shows "ta_only_prs_wits TA wits = ta_only_prod TA"
proof -
  let ?fin = "{q \<in> ta_final TA. wits q \<noteq> None}"
  let ?eps = "{q \<in> ta_eps TA. wits (snd q) \<noteq> None}"
  let ?rs = "{r \<in> ta_rules TA. wits (r_rhs r) \<noteq> None}"
  let ?prs = "ta_productive TA"
  from assms have fin: "?fin = ta_final TA \<inter> ?prs" by auto
  have "?eps \<subseteq> ta_eps TA \<inter> (?prs \<times> ?prs)" proof
    fix q p assume *: "(q,p) \<in> ?eps"
    with assms have p: "p \<in> ?prs" by auto
    from * have "p \<in> ta_res TA (Var q)" by auto                     
    from ta_res_ctxt[OF this] p have "q \<in> ?prs" by (auto simp add: ta_productive_def)
    with p * show "(q,p) \<in> ta_eps TA \<inter> (?prs \<times> ?prs)" by auto
  qed
  with assms have eps: "?eps = ta_eps TA \<inter> (?prs \<times> ?prs)" by auto
  have "?rs = {r \<in> ta_rules TA. r_states r \<subseteq> ?prs}" (is "?lhs = ?rhs") proof
    show "?lhs \<subseteq> ?rhs" proof
      fix r assume *: "r \<in> ?lhs"
      obtain f qs q where r[simp]: "r = f qs \<rightarrow> q" by (cases r)
      from assms * have prs: "q \<in> ?prs" by auto
      let ?qsv = "map Var qs"
      from * have q: "q \<in> ta_res TA (Fun f ?qsv)" by auto
      have "set qs \<subseteq> ?prs" proof
        fix p assume "p \<in> set qs"
        from this obtain i where ith: "p = qs!i" and len: "i < length qs" by (auto simp: in_set_conv_nth)
        let ?C = "More f (take i ?qsv) \<box> (drop (Suc i) ?qsv)"
        from len have "i < length (map Var qs)" by simp
        note id_take_nth_drop[OF this, symmetric]
        then have "?C\<langle>Var p\<rangle> = Fun f ?qsv" unfolding ith using len by auto
        from q[folded this] have q: "q \<in> ta_res TA ?C\<langle>Var p\<rangle>" .
        note ta_productiveE[OF prs]
        from this obtain q' C where res: "q' \<in> ta_res TA C\<langle>Var q\<rangle>" and fin: "q' \<in> ta_final TA" by blast
        from ta_res_ctxt[OF q res] fin show "p \<in> ?prs" by (intro ta_productiveI[of q' _ "C \<circ>\<^sub>c ?C"], auto)
      qed
      with prs * show "r \<in> ?rhs" by (auto simp add: r_states_def)
    qed
    show "?rhs \<subseteq> ?lhs" using assms unfolding r_states_def by auto
  qed
  from this fin eps show ?thesis by (simp add: ta_restrict_def ta.make_def ta_only_prs_wits_def)
qed

lemma ta_only_prod_inv:
  "prs_wits_spec TA m \<Longrightarrow> prs_wits_spec (ta_only_prod TA) m"
by (simp add: ta_only_prod_productive map_to_set_def ta_only_prod_prs_wit[of TA, symmetric])

definition "ta_only_prs TA \<equiv>
  prs_wits TA \<bind> RETURN o ta_only_prs_wits TA"

lemma ta_only_prs:
assumes "ta_finite TA"
  shows "ta_only_prs TA \<le> RETURN(ta_only_prod TA)"
unfolding ta_only_prs_def
by (refine_vcg prs_wits_correct[OF assms, THEN order_trans])
   (auto intro: ta_only_prs_wits simp: res_wits_inv_def)

subsection \<open>"Trimming" and computing witnesses for reachability and productivity\<close>

definition trim_ta_wits where
  "trim_ta_wits TA \<equiv>
    do {
      res \<leftarrow> res_wits TA;
      let TA = ta_only_res_wits TA res in do {
      prs \<leftarrow> prs_wits TA;
      let TA = ta_only_prs_wits TA prs in 
      RETURN (TA, res, prs)
    }}"

lemma ta_only_reach_finite:
  "ta_finite TA \<Longrightarrow> ta_finite (ta_only_reach TA)"
unfolding ta_restrict_def ta_finite_def by auto

lemma trim_ta_reachable:
  "ta_states (ta_only_prod (ta_only_reach TA)) \<subseteq> ta_reachable TA"
unfolding ta_states_def ta_restrict_def r_states_def by auto

lemma map_to_set_ball_conv:
  "(\<forall>x\<in>map_to_set m. P x) \<longleftrightarrow> (\<forall>k\<in>dom m. P (k, the (m k)))"
unfolding map_to_set_def dom_def by auto

lemma trim_ta_wits_correct:
  assumes "ta_finite TA"
    shows "trim_ta_wits TA \<le> SPEC(\<lambda>(TA', res, prs).
            ta_trim TA' \<and> ((ta_lang TA::('f,'x) terms) = ta_lang TA') \<and> ta_subset TA' TA \<and>
            (\<forall>q \<in> ta_states TA'. is_ad_res_wit TA' q (the (res q))) \<and>
            (\<forall>q \<in> ta_states TA'. is_prs_wit TA' q (the (prs q))))"
proof -
  note prs = order_trans[OF res_wits_correct[OF assms]]
  note res = order_trans[OF prs_wits_correct]
  note [simp] = ta_only_res_wits ta_only_prs_wits res_wits_inv_def
  show ?thesis unfolding trim_ta_wits_def
  proof (refine_vcg res prs, goal_cases)
    case 3
      then show ?case by (auto simp: ta_only_prod_lang ta_only_reach_lang) next
    case 4
      then show ?case by (auto simp: ta_subset_def ta_restrict_def) next
    case prems: (5 res prs TA' x res' prs')
      note inv = prems(4)[unfolded prems(3), symmetric, simplified] prems(1,2)
      have prod: "\<And>TA. ta_states (ta_only_prod TA) \<subseteq> ta_productive TA"
        by (auto simp: ta_states_def r_states_def ta_restrict_def)
      from inv have states: "ta_states TA' \<subseteq> ta_reachable TA" by (auto simp: trim_ta_reachable)
      with inv prod[of "ta_only_reach TA"] show ?case
        by (simp add: domD rev_subsetD map_to_set_def ta_only_reach_res_wit[of _ _ TA, symmetric])
           (intro ballI ta_res_only_prod, auto simp: domD)
      next
    case prems: (6 res prs TA' x res' prs')
      note inv = prems(4)[unfolded prems(3), symmetric, simplified] prems(1,2)
      have prod: "ta_states (ta_only_prod (ta_only_reach TA)) \<subseteq> ta_productive (ta_only_reach TA)"
        by (auto simp: ta_states_def r_states_def ta_restrict_def)
      with inv show ?case by (simp add: ta_only_prod_prs_wit) (auto simp: map_to_set_def domD) next
  qed (auto intro: ta_only_reach_finite assms trim_ta[unfolded trim_ta_def])
qed

lemma res_wit_subst:
  assumes wits: "\<And>q. q \<in> vars_term w \<Longrightarrow> is_ad_res_wit TA q (the (m q))"
      and res: "q \<in> ta_res TA w"
    shows "is_ad_res_wit TA q (w \<cdot> (the \<circ> m))"
using assms proof (induction w arbitrary: q)
  case (Var x)
    then show ?case by (auto intro: ta_res_eps) next
  case (Fun f ts)
    from Fun.prems(2) obtain qs p where
      rule: "f qs \<rightarrow> p \<in> ta_rules TA" "length qs = length ts" "q \<in> eps_cl TA p" and
      qs: "\<And>i. i < length ts \<Longrightarrow> qs!i \<in> ta_res TA (ts!i)" by auto
    {
      fix i assume i: "i < length ts"
      with Fun.prems(1) have "\<And>q. q \<in> vars_term (ts!i) \<Longrightarrow> is_ad_res_wit TA q (the (m q))" by force
      note Fun.IH[OF nth_mem[OF i] this qs[OF i]]
    }
    moreover from Fun.prems have "\<forall>t \<in> set ts. \<forall>x \<in> vars_term t. ground (the (m x))" by auto
    ultimately show ?case using rule by (auto intro!: exI[of _ p] exI[of _ qs])
qed

lemma res_wit_subst_lang:
  assumes wits: "\<And>q. q \<in> vars_term w \<Longrightarrow> is_ad_res_wit TA q (the (m q))"
      and res: "ta_res TA w \<inter> ta_final TA \<noteq> {}"
    shows "w \<cdot> (the \<circ> m) \<in> ta_lang TA"
proof -
  from res obtain qf where "qf \<in> ta_res TA w" "qf \<in> ta_final TA" by blast
  with res_wit_subst[OF wits this(1)] show ?thesis by (intro ta_langI2) auto
qed

lemma subst_res_wit:
  assumes det: "ta_det TA"
      and res: "\<And>q. q \<in> vars_term w \<Longrightarrow> is_ad_res_wit TA q (the (rw q))"
      and p: "p \<in> ta_res TA (adapt_vars (w \<cdot> (the \<circ> rw)))"
    shows "p \<in> ta_res TA w"
using res p  proof (induction w arbitrary: p)
  case (Var x)
    with ta_detE[OF det] have "ta_res TA (adapt_vars (the (rw x))) = {x}" by auto
    with Var show ?case by auto next
  case (Fun f ts)
    from Fun.prems(2) obtain qs p' where
      rule: "f qs \<rightarrow> p' \<in> ta_rules TA" "length qs = length ts" "p \<in> eps_cl TA p'" and
      qs: "\<And>i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res TA (adapt_vars (ts ! i \<cdot> (the \<circ> rw)))" unfolding comp_def by auto
    {
      fix i assume i: "i < length ts"
      with Fun.prems(1) have "\<And>q. q \<in> vars_term (ts ! i) \<Longrightarrow> is_ad_res_wit TA q (the (rw q))" by fastforce
      note Fun.IH[OF nth_mem[OF i] this qs[OF i]]
    }
    with rule show ?case by (auto intro!: exI[of _ p'] exI[of _ qs])
qed

lemma res_nowit_subst_lang:
  assumes det: "ta_det TA"
  assumes wits: "\<And>q. q \<in> vars_term w \<Longrightarrow> is_ad_res_wit TA q (the (m q))"
      and res: "ta_res TA w \<inter> ta_final TA = {}"
    shows "w \<cdot> (the \<circ> m) \<notin> ta_lang TA"
proof (rule ccontr, simp)
  assume "w \<cdot> (the \<circ> m) \<in> ta_lang TA"
  from ta_langE2[OF this] obtain q where
    q: "q \<in> ta_res TA (adapt_vars (w \<cdot> (the \<circ> m)))" and
    fin: "q \<in> ta_final TA" by blast
  from subst_res_wit[OF det wits q] res fin show False by auto
qed

lemma prs_wit_apply:
  assumes wits: "\<And>q. q \<in> ta_states TA \<Longrightarrow> is_prs_wit TA q (the (m q))"
      and vars: "vars_term w \<subseteq> ta_states TA"
      and res: "q \<in> ta_res TA w"
    shows "ta_res TA (the (m q))\<langle>w\<rangle> \<inter> ta_final TA \<noteq> {}"
proof -
  from vars res have "q \<in> ta_states TA" by (cases w) (auto intro: ta_eps_ta_states dest: r_rhs_states)
  from wits[OF this] obtain q' where fin: "q' \<in> ta_res TA (the (m q))\<langle>Var q\<rangle>" "q' \<in> ta_final TA" by auto
  from fin(2) ta_res_ctxt[OF res fin(1)] show ?thesis by blast
qed

definition "ta_lang_wit res prs q w \<equiv> ((the (prs q))\<langle>w\<rangle>) \<cdot> (the \<circ> res)"

lemma ta_lang_wit:
  assumes res: "\<And>q. q \<in> ta_states TA \<Longrightarrow> is_ad_res_wit TA q (the (rw q))"
      and prs: "\<And>q. q \<in> ta_states TA \<Longrightarrow> is_prs_wit TA q (the (pw q))"
      and vars: "vars_term w \<subseteq> ta_states TA"
      and q: "q \<in> ta_res TA w"
    shows "ta_lang_wit rw pw q w \<in> ta_lang TA"
proof -
  from prs_wit_apply[OF prs vars q] obtain q' where
    fin: "q' \<in> ta_res TA (the (pw q))\<langle>w\<rangle>" "q' \<in> ta_final TA" by blast
  then have "q' \<in> ta_states TA" by (auto simp: ta_states_def)
  from ta_res_vars_states[OF fin(1) this] res have 
    "is_ad_res_wit TA q' ((the (pw q))\<langle>w\<rangle> \<cdot> (the \<circ> rw))" by (intro res_wit_subst[OF _ fin(1)]) auto
  with fin(2) show ?thesis by (intro ta_langI2) (auto simp: ta_lang_wit_def)
qed

lemma ta_lang_nowit:
  assumes det: "ta_det TA"
      and res: "\<And>q. q \<in> vars_term w \<Longrightarrow> is_ad_res_wit TA q (the (rw q))"
      and w: "ta_res TA w = {}"
    shows "ta_lang_wit rw pw q w \<notin> ta_lang TA"
proof (rule ccontr, simp)
  assume "ta_lang_wit rw pw q w \<in> ta_lang TA"
  from ta_langE2[OF this] obtain qf where
    "qf \<in> ta_res TA (adapt_vars ((the (pw q))\<langle>w\<rangle> \<cdot> (the \<circ> rw)))" by (auto simp: ta_lang_wit_def)
  from this obtain p where "p \<in> ta_res TA (adapt_vars (w \<cdot> (the o rw)))" by (auto dest: ta_res_ctxt_decompose)
  with subst_res_wit[OF det res this] w show False by blast
qed

lemma ta_lang_wit_rstep:
  assumes "(s \<cdot> (the o res),t \<cdot> (the o res)) \<in> rstep R"
    shows "(ta_lang_wit res prs q s, ta_lang_wit res prs q t) \<in> rstep R"
unfolding ta_lang_wit_def subst_apply_term_ctxt_apply_distrib by (intro rstep_ctxt assms)

subsection \<open>Deciding closure under rewriting\<close>

subsubsection \<open>Auxiliary definitions and theorems\<close>

abbreviation (input) lookup2 :: "('a \<Rightarrow> ('b \<Rightarrow> 'c option) option) \<Rightarrow> _" where 
  "lookup2 m k1 k2 \<equiv> m k1 \<bind> (\<lambda>m. m k2)"

definition update_all2 where
  "update_all2 m ks1 ks2 v \<equiv>
    \<lambda>k1. if k1 \<in> ks1 then Some (\<lambda>k2. if k2 \<in> ks2 then Some v else lookup2 m k1 k2) else m k1"

definition "dom2 m \<equiv> {(k1,k2). lookup2 m k1 k2 \<noteq> None}"

lemma dom2_empty[simp]: "dom2 Map.empty = {}" by (auto simp: dom2_def)

lemma update_all2_dom[simp]:
  "dom (update_all2 m ks1 ks2 v) = dom m \<union> ks1"
unfolding update_all2_def by auto

lemma update_all2_dom2[simp]:
  "dom2 (update_all2 m ks1 ks2 v) = dom2 m \<union> (ks1 \<times> ks2)"
unfolding update_all2_def dom2_def by (force split: if_splits)

definition map2_to_set where
  "map2_to_set m = {(k1, k2, v). lookup2 m k1 k2 = Some v}"

lemma map2_to_set_empty[simp]:
  "map2_to_set Map.empty = {}"
unfolding map2_to_set_def by auto

lemma update_all2_ballI[intro]:
  assumes "\<And>k1 k2 v. (k1,k2,v) \<in> map2_to_set m \<Longrightarrow> P k1 k2 v"
      and "\<And>k1 k2. \<lbrakk>k1 \<in> ks1; k2 \<in> ks2\<rbrakk> \<Longrightarrow> P k1 k2 v"
    shows "\<forall>(k1,k2,v) \<in> map2_to_set (update_all2 m ks1 ks2 v). P k1 k2 v"
using assms unfolding update_all2_def map2_to_set_def by auto

definition map_add2 where "map_add2 m1 m2 \<equiv>
  \<lambda>k. case m2 k of None \<Rightarrow> m1 k | Some m2' \<Rightarrow>
       (case m1 k of None \<Rightarrow> Some m2' | Some m1' \<Rightarrow> Some (m1' ++ m2'))"

lemma map_add2_dom2[simp]:
  shows "dom2 (map_add2 m1 m2) = dom2 m1 \<union> dom2 m2"
by (auto simp: dom2_def map_add2_def Map.map_add_def split: option.splits)

lemma map_add2_ballI[intro]:
  assumes "\<forall>(k1,k2,v) \<in> map2_to_set m1. P k1 k2 v"
      and "\<forall>(k1,k2,v) \<in> map2_to_set m2. P k1 k2 v"
    shows "\<forall>(k1,k2,v) \<in> map2_to_set (map_add2 m1 m2) . P k1 k2 v"
using assms by (auto simp: map2_to_set_def map_add2_def Map.map_add_def split: option.splits)

lemma ta_match_length:
  assumes "\<sigma> \<in> ta_match TA (ta_rhs_states TA) t Q"
    shows "length \<sigma> = length (vars_term_list t)"
using assms proof (induction t arbitrary: Q \<sigma>)
  case (Var x)
    then show ?case by (auto simp add: vars_term_list.simps)
  next
  case (Fun f ts)
    from Fun.prems[simplified] obtain \<sigma>s qs where
      cat: "\<sigma> = concat \<sigma>s" and len: "length \<sigma>s = length ts" and
      res: "\<forall>i<length ts. \<sigma>s ! i \<in> ta_match TA (ta_rhs_states TA) (ts ! i) {qs ! i}" by auto
    with Fun.IH res have "\<And>i. i < length ts \<Longrightarrow> length (\<sigma>s!i) = length (vars_term_list (ts!i))" by auto
    with len show ?case unfolding cat
    proof (induction rule: list_induct2)
      case (Cons \<sigma> \<sigma>s t ts)
      from Cons.prems[of 0] have "length \<sigma> = length (vars_term_list t)" by simp
      moreover {
        fix i assume "i < length ts"
        with Cons.prems[of "Suc i"] have "length (\<sigma>s!i) = length (vars_term_list (ts! i))" by auto
      }
      ultimately show ?case using Cons.IH by (simp add: vars_term_list.simps)
    qed (simp add: vars_term_list.simps)
qed

lemma ta_match_finite:
  assumes "ta_finite TA"
    shows "finite (ta_match TA (ta_rhs_states TA) t Q)"
proof -
  let ?n = "length (vars_term_list t)"
  let ?A = "vars_term t \<times> ta_rhs_states TA"
  let ?ls = "{xs. set xs \<subseteq> ?A \<and> length xs = ?n}"
  have "finite ?A" using finite_rhs_states[OF assms] by (intro finite_cartesian_product, simp)
  then have "finite ?ls" by (rule finite_lists_length_eq)
  moreover have "ta_match TA (ta_rhs_states TA) t Q \<subseteq> ?ls" (is "?lhs \<subseteq> ?ls")
  proof
    fix x assume x: "x \<in> ?lhs"
    from ta_match_vars_term[OF x] have "set x \<subseteq> vars_term t \<times> ta_rhs_states TA" by auto
    moreover from ta_match_length[OF x] have "length x = length (vars_term_list t)" by auto
    ultimately show "x \<in> ?ls" by auto
  qed
  ultimately show ?thesis by (rule rev_finite_subset)
qed

lemmas ta_match'_finite = ta_match_finite[of TA _ "ta_rhs_states TA", folded ta_match'_def] for TA

subsubsection \<open>Checking state compatibility\<close>

definition is_compatible where
  "is_compatible TA R \<equiv>
    FOREACH\<^sub>C R isOK (\<lambda>(l,r) rel.
      let \<sigma>s = ta_match' TA (ta_rhs_states TA) l in
      FOREACH\<^sub>C \<sigma>s isOK (\<lambda>\<sigma> rel.
        let l\<sigma> = map_vars_term (fun_of \<sigma>) l;
            ql = ta_res TA l\<sigma> in
        if ql = {} then
          RETURN rel
        else
          let r\<sigma> = map_vars_term (fun_of \<sigma>) r;
              qr = ta_res TA r\<sigma> in
          if qr = {} then do {
            q \<leftarrow> SPEC(\<lambda>q. q \<in> ql);
            RETURN (error (q, l\<sigma>, r\<sigma>))
          }
          else do {
            ASSERT (isOK rel);
            let rel = update_all2 (run rel) ql qr (l\<sigma>, r\<sigma>) in
            RETURN (return rel)
          }
      ) rel
    ) (return Map.empty)"

definition state_compatible_it\<tau> where
  "state_compatible_it\<tau> TA l r it\<tau> rel \<equiv>
    \<forall>\<tau> \<in> it\<tau>. \<forall>q \<in> ta_res TA (map_vars_term (fun_of \<tau>) l).
      \<exists>p. p \<in> ta_res TA (map_vars_term (fun_of \<tau>) r) \<and> (q,p) \<in> rel"

lemma [simp]: "state_compatible_it\<tau> TA l r {} rel = True" by (auto simp: state_compatible_it\<tau>_def)

definition state_compatible_itR where
  "state_compatible_itR TA itR rel \<equiv>
    \<forall>(l,r) \<in> itR. state_compatible_it\<tau> TA l r (ta_match' TA (ta_rhs_states TA) l) rel"

lemma state_compatible_itR_mono:
  assumes "R \<subseteq> S"
      and "state_compatible_itR TA itR R"
    shows "state_compatible_itR TA itR S"
using assms by (fastforce simp: state_compatible_itR_def state_compatible_it\<tau>_def)

lemma state_compatible_itR:
  assumes wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
      and itR: "state_compatible_itR TA R rel"
    shows "state_compatible TA rel R"
proof -
  from itR show ?thesis unfolding state_compatible_def rule_state_compatible_def prod.case
  proof (intro impI allI subsetI, goal_cases)
    case p: (1 l r \<sigma> q)
      note comp = p(1) and rule = p(2) and funas = p(3) and vars = p(4) and res = p(5)
      from ta_match'[OF res vars] obtain \<tau> where
        \<tau>: "\<tau>\<in>ta_match' TA (ta_rhs_states TA) l" "\<forall>x\<in>vars_term l. \<sigma> x = fun_of \<tau> x" by auto
      from \<tau>(2) have l: "map_vars_term \<sigma> l = map_vars_term (fun_of \<tau>) l"  by (induction l, auto)
      from wf[OF rule] \<tau>(2) have r: "map_vars_term \<sigma> r = map_vars_term (fun_of \<tau>) r" by (induction r, auto)
      from comp rule \<tau>(1) res show ?case by (fastforce simp: state_compatible_itR_def state_compatible_it\<tau>_def l r)
  qed
qed

abbreviation "dom2r \<equiv> dom2 o run"

definition is_compatible_inner_ok_inv where
  "is_compatible_inner_ok_inv TA itR l r it\<tau> rel \<equiv>
    isOK rel \<longrightarrow>
      state_compatible_itR TA itR (dom2r rel) \<and> state_compatible_it\<tau> TA l r it\<tau> (dom2r rel)"

definition is_compatible_ok_inv where
  "is_compatible_ok_inv TA itR rel \<equiv>
    isOK rel \<longrightarrow> state_compatible_itR TA itR (dom2r rel)"

lemma is_compatible_ok_correct:
assumes fin_R: "finite R"
    and fin_TA: "ta_finite TA"
  shows "is_compatible TA R \<le> SPEC(is_compatible_ok_inv TA R)"
proof -
  note is_compatible_ok_inv_def[simp] and is_compatible_inner_ok_inv_def[simp]
  note ref_rule = FOREACHc_rule'[where I="\<lambda>it. is_compatible_ok_inv TA (R - it)"]
  show ?thesis unfolding is_compatible_def
  proof (refine_vcg ref_rule, simp_all only: it_step_insert_iff, goal_cases)
    case (3 _ itR rel l r)
      note outer_inv = this and state_compatible_it\<tau>_def[simp] and state_compatible_itR_def[simp]
      let ?\<sigma>s = "ta_match' TA (ta_rhs_states TA) l"
      note ref_rule = FOREACHc_rule'[where I="\<lambda>it. is_compatible_inner_ok_inv TA (R - itR) l r (?\<sigma>s - it)"]
      show ?case
      proof (refine_vcg ref_rule, simp_all only: it_step_insert_iff, goal_cases)
        case 2
          from outer_inv show ?case by simp next
        case 5
          then show ?case by simp blast next
      qed (auto simp: ta_match'_finite[OF fin_TA])
  qed (simp_all add: fin_R state_compatible_itR_def)
qed

abbreviation (input) ta_states_rstep where
  "ta_states_rstep TA R s s' \<sigma> \<equiv> (s\<cdot>\<sigma>, s'\<cdot>\<sigma>) \<in> rstep R \<and> vars_term s \<subseteq> ta_states TA \<and> vars_term s' \<subseteq> ta_states TA"

definition rel_wit_inv where
  "rel_wit_inv \<sigma> TA R m \<equiv> case m of
      error (q,s,s') \<Rightarrow>
        q \<in> ta_res TA s \<and> ta_res TA s' = {} \<and> ta_states_rstep TA R s s' \<sigma>
    | return m \<Rightarrow> \<forall>(q,q',(s,s')) \<in> map2_to_set m.
        q \<in> ta_res TA s \<and> q' \<in> ta_res TA s' \<and> ta_states_rstep TA R s s' \<sigma>"

lemma rel_wit_inv_empty[simp]:
  "rel_wit_inv \<sigma> TA R (return Map.empty)"
by (simp add: rel_wit_inv_def)

lemma map_vars_term_rstep:
  assumes "(l,r) \<in> R"
    shows "(map_vars_term \<tau> l \<cdot> \<sigma>, map_vars_term \<tau> r \<cdot> \<sigma>) \<in> rstep R"
unfolding map_vars_term_as_subst subst_subst
by (intro rstep_subst rstep_rule assms)

lemma match_apply_states:
  assumes vars: "vars_term r \<subseteq> vars_term l"
      and match: "\<tau> \<in> ta_match' TA (ta_rhs_states TA) l"
    shows "vars_term (map_vars_term (fun_of \<tau>) r) \<subseteq> ta_states TA"
proof -
  note states_trans = order_trans[OF _ ta_rhs_states_subset_states]
  note match_states = ta_match'_vars_term[THEN states_trans]
  from match_states[OF match] vars have "fun_of \<tau> ` vars_term r \<subseteq> ta_states TA" by auto
  then show ?thesis by (induction r, auto)
qed

lemma is_compatible_wit:
assumes fin_R: "finite R"
    and fin_TA: "ta_finite TA"
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "is_compatible TA R \<le> SPEC(rel_wit_inv \<sigma> TA R)"
proof -
  note rel_wit_inv_def[simp]
  show ?thesis unfolding is_compatible_def
  proof (refine_vcg FOREACHc_rule'[where I = "\<lambda>_. rel_wit_inv \<sigma> TA R"], goal_cases)
    case prems: (4 _ _ _ l r \<tau>)
      note res = prems(10-12)
      from prems have lr: "(l,r) \<in> R" and \<tau>: "\<tau> \<in> ta_match' TA (ta_rhs_states TA) l" by auto
      note match_apply_states[OF subset_refl \<tau>] match_apply_states[OF wf[OF lr] \<tau>] 
      with res show ?case by (auto intro: map_vars_term_rstep[OF lr])
    next
    case prems: (5 _ _ _ l r \<tau> _ rel)
      note res = prems(10,11) and inv = prems(8)
      from prems obtain m where rel: "rel = return m" by (cases rel, auto)
      from prems have lr: "(l,r) \<in> R" and \<tau>: "\<tau> \<in> ta_match' TA (ta_rhs_states TA) l" by auto
      note match_apply_states[OF subset_refl \<tau>] match_apply_states[OF wf[OF lr] \<tau>]
      with inv res show ?case unfolding rel
        by (simp, intro update_all2_ballI, auto split: prod.splits intro: map_vars_term_rstep[OF lr])
  qed (simp_all add: ta_match'_finite[OF fin_TA] fin_R)
qed

definition "rel_empty_inv m \<equiv> isOK m \<longrightarrow> (Map.empty \<notin> ran (run m))"

lemma rel_empty_inv:
  assumes "rel_empty_inv m" "isOK m"
    shows "dom2r m = {} \<longleftrightarrow> (run m) = Map.empty" (is "?dom = ?empty")
proof
  show "?empty \<Longrightarrow> ?dom" by simp
  show "?dom \<Longrightarrow> ?empty" proof (rule ccontr)
    assume dom: "?dom" and empty: "run m \<noteq> Map.empty"
    then have "\<forall>v \<in> ran (run m). v = Map.empty" by (simp add: dom2_def ran_def split: bind_splits) (meson not_Some_eq)
    moreover from empty obtain k v where "run m k = Some v" by force
    ultimately show False using assms by (auto simp: rel_empty_inv_def ran_def)
  qed
qed

lemma update_all2_not_empty1:
  assumes "ks1 \<noteq> {}"
    shows "update_all2 m ks1 ks2 v \<noteq> Map.empty"
using assms unfolding update_all2_def fun_eq_iff by auto

lemma update_all2_not_empty2:
  assumes "ks2 \<noteq> {}"
      and "Map.empty \<notin> ran m"
    shows "Map.empty \<notin> ran (update_all2 m ks1 ks2 v)"
using assms by (auto simp: update_all2_def fun_eq_iff ran_def)

lemma is_compatible_empty:
assumes fin_R: "finite R"
    and fin_TA: "ta_finite TA"
  shows "is_compatible TA R \<le> SPEC(rel_empty_inv)"
proof -
  note simps = fin_R ta_match'_finite[OF fin_TA] rel_empty_inv_def
  note rule = FOREACHc_rule'[where I = "\<lambda>_. rel_empty_inv"]
  show ?thesis unfolding is_compatible_def by (refine_vcg rule, simp_all add: simps, intro update_all2_not_empty2)
qed

definition "rel_finite_inv m \<equiv> isOK m \<longrightarrow> finite (dom (run m)) \<and> finite (dom2r m)"

lemma ta_res_finite:
  assumes "ta_finite TA"
    shows "finite (ta_res TA t)"
proof -
  note [dest] = ta_finiteD
  show ?thesis proof (induction t)
  case (Var x)
    have "ta_res TA (Var x) = (ta_eps TA)\<^sup>* `` {x}" by auto
    with assms show ?case by (auto intro: finite_rtrancl_Image)
  next
  case (Fun f ts)
    have "ta_res TA (Fun f ts) \<subseteq> ta_rhs_states TA" by (intro ta_rhs_states_res) simp
    with finite_rhs_states[OF assms] show ?case by (blast intro: finite_subset)
  qed
qed

lemma is_compatible_finite:
  assumes fin_R: "finite R"
    and fin_TA: "ta_finite TA"
  shows "is_compatible TA R \<le> SPEC(rel_finite_inv)"
proof -
  note simps = fin_R ta_match'_finite[OF fin_TA] rel_finite_inv_def ta_res_finite[OF fin_TA]
  note rule = FOREACHc_rule'[where I = "\<lambda>_. rel_finite_inv"]
  show ?thesis unfolding is_compatible_def by (refine_vcg rule, simp_all add: simps)
qed

subsubsection \<open>Computing states that are required for state coherence\<close>

definition new_rel :: "('q,'f) ta_rule set \<Rightarrow> _" where
  "new_rel rs accu todo \<equiv>
    FOREACH\<^sub>C rs isOK (\<lambda>r new. case r of f qs \<rightarrow> q \<Rightarrow>
      nfoldli [0 ..< length qs] isOK (\<lambda>i new. do {
        ASSERT (i < length qs);
        let qi = qs ! i in
        case todo qi of 
          None \<Rightarrow> RETURN new
        | Some rtodo \<Rightarrow>
            FOREACH\<^sub>C (map_to_set rtodo) isOK (\<lambda>(qsi,wl,wr) new.
              let qsa = map Var (take i qs);
              qsb = map Var (drop (Suc i) qs);
              wl = Fun f (qsa@wl#qsb);
              wr = Fun f (qsa@wr#qsb);
              qs = qs[i := qsi];
              rhss = r_rhs ` {r \<in> rs. case r of (f' qs' \<rightarrow> q') \<Rightarrow> f' = f \<and> qs' = qs} in
              if rhss = {} then
                RETURN (error (q, wl, wr))
              else
                let rhss = {q' \<in> rhss. lookup2 accu q q' = None} in
                if rhss = {} then
                  RETURN new
                else do {
                  ASSERT (isOK new);
                  RETURN (return (update_all2 (run new) {q} rhss (wl, wr)))
                }
            ) new
      }) new
    ) (return Map.empty)"

definition "req_rel_it_rule_arg accu rs f qs q i qsis  = {(q, q') | q' qsi. TA_rule f (qs[i := qsi]) q' \<in> rs \<and> qsi \<in> qsis} - accu"
definition "req_rel_it_rule rel accu rs f qs q is = \<Union>{req_rel_it_rule_arg accu rs f qs q i {qsi. (qs!i, qsi) \<in> rel} | i. i \<in> is}"
definition "req_rel_it rel accu rs it = \<Union>{req_rel_it_rule rel accu rs f qs q {0 ..< length qs} | f qs q. TA_rule f qs q \<in> it}"
abbreviation "req_rel rel accu rs \<equiv> req_rel_it rel accu rs rs"

definition "is_rule_arg_coh_it rs f qs q i qsiIt \<equiv> \<forall>qsi \<in> qsiIt. \<exists>q'. TA_rule f (qs[i := qsi]) q' \<in> rs"
definition "is_rule_coh_it rel rs f qs q iIt \<equiv> \<forall>i \<in> iIt. is_rule_arg_coh_it rs f qs q i {qsi. (qs!i, qsi) \<in> rel}"
definition "is_coh_it rel rs rsIt \<equiv> \<forall>r \<in> rsIt. case r of TA_rule f qs q \<Rightarrow> is_rule_coh_it rel rs f qs q {0 ..< length qs}"
abbreviation "is_coh rel rs \<equiv> is_coh_it rel rs rs"

definition "new_rel_ok_inv3 rel accu rs rsIt f qs q iIt i qsiIt m \<equiv> isOK m \<longrightarrow>
  dom2r m = req_rel_it rel accu rs rsIt \<union> req_rel_it_rule rel accu rs f qs q iIt \<union> req_rel_it_rule_arg accu rs f qs q i qsiIt \<and>
  is_coh_it rel rs rsIt \<and> is_rule_coh_it rel rs f qs q iIt \<and> is_rule_arg_coh_it rs f qs q i qsiIt"

definition "new_rel_ok_inv2 rel accu rs rsIt f qs q iIt m \<equiv> isOK m \<longrightarrow>
  dom2r m = req_rel_it rel accu rs rsIt \<union> req_rel_it_rule rel accu rs f qs q iIt \<and>
  is_coh_it rel rs rsIt \<and> is_rule_coh_it rel rs f qs q iIt"

definition "new_rel_ok_inv1 rel accu rs rsIt m \<equiv> isOK m \<longrightarrow>
  dom2r m = req_rel_it rel accu rs rsIt \<and> is_coh_it rel rs rsIt"

abbreviation "new_rel_ok_inv rel accu rs \<equiv> new_rel_ok_inv1 rel accu rs rs"

lemma new_rel_empty_simps[simp]:
  "req_rel_it x y z {} = {}"
  "req_rel_it_rule x y z f qs q {} = {}"
  "req_rel_it_rule_arg y z f qs q i {} = {}"
by (simp_all add: req_rel_it_def req_rel_it_rule_def req_rel_it_rule_arg_def)

lemma is_coh_it_true_simps[simp]:
  "is_rule_arg_coh_it rs f qs q i {}"
  "is_rule_coh_it rel rs f qs q {}"
  "is_coh_it rel rs {}"
by (simp_all add: is_coh_it_def is_rule_coh_it_def is_rule_arg_coh_it_def)

lemma coh_rel_insert_simps[simp]:
  "req_rel_it x y z (insert (f qs \<rightarrow> q) b) = req_rel_it x y z b \<union> req_rel_it_rule x y z f qs q {0..<length qs}"
  "req_rel_it_rule x y z f qs q (insert i is) = req_rel_it_rule x y z f qs q is \<union> req_rel_it_rule_arg y z f qs q i {qsi. (qs!i, qsi) \<in> x}"
  "req_rel_it_rule_arg y z f qs q i (insert qsi qsis) = req_rel_it_rule_arg y z f qs q i qsis \<union> ({(q, q') | q'. TA_rule f (qs[i := qsi]) q' \<in> z} - y)"
unfolding req_rel_it_rule_def req_rel_it_def by (auto, unfold req_rel_it_rule_arg_def, auto)

lemma is_coh_it_insert_simps[simp]:
  "is_coh_it x z (insert (f qs \<rightarrow> q) b) \<longleftrightarrow> is_coh_it x z b \<and> is_rule_coh_it x z f qs q {0..<length qs}"
  "is_rule_coh_it x z f qs q (insert i is) \<longleftrightarrow> is_rule_coh_it x z f qs q is \<and> is_rule_arg_coh_it z f qs q i {qsi. (qs!i, qsi) \<in> x}"
  "is_rule_arg_coh_it z f qs q i (insert qsi qsis) \<longleftrightarrow> is_rule_arg_coh_it z f qs q i qsis \<and> (\<exists>q'. TA_rule f (qs[i := qsi]) q' \<in> z)"
unfolding is_coh_it_def is_rule_coh_it_def is_rule_arg_coh_it_def by auto

lemmas is_coh_defs = is_coh_it_def is_rule_coh_it_def is_rule_arg_coh_it_def
lemmas req_rel_defs = req_rel_it_def req_rel_it_rule_def req_rel_it_rule_arg_def

lemma dom2_lu_finite:
  assumes finite: "finite (dom2 m)"
      and lu: "m k = Some mr"
    shows "finite (map_to_set mr)"
proof -
  have "dom mr \<subseteq> Range (dom2 m)" proof
    fix l assume "l \<in> dom mr"
    from this obtain x where "mr l = Some x" by auto
    with lu have "lookup2 m k l = Some x" by simp
    then show "l \<in> Range (dom2 m)" by (auto simp: dom2_def)
  qed
  note finite_Range[OF finite] finite_subset[OF this]
  then show ?thesis unfolding finite_map_to_set by blast
qed

lemma upt_len_lt:
  assumes "[0..<length qs] = l1 @ x # l2"
    shows "x < length qs"
proof -
  from assms have "x \<in> set [0..<length qs]" by auto
  then show ?thesis by auto
qed

lemma new_relation_ok_correct:
  assumes fin_rs: "finite rs"
      and fin_todo: "finite (dom2 todo)"
    shows "new_rel rs accu todo \<le> SPEC(new_rel_ok_inv (dom2 todo) (dom2 accu) rs)"
proof -
  let ?rel = "dom2 todo" and ?accu = "dom2 accu"
  note new_rel_ok_inv1_def[simp] and new_rel_ok_inv2_def[simp] and new_rel_ok_inv3_def[simp]
  note rule = FOREACHc_rule'[where I = "\<lambda>it. new_rel_ok_inv1 ?rel ?accu rs (rs - it)"]
  show ?thesis unfolding new_rel_def
  proof (refine_vcg rule, simp_all only: it_step_insert_iff, goal_cases)
    case prems1: (3 r rsit m)
      obtain f qs q where r: "r = (f qs \<rightarrow> q)" by (cases r)
      note rule = nfoldli_rule[where I = "\<lambda>idone _. new_rel_ok_inv2 ?rel ?accu rs (rs - rsit) f qs q (set idone)"]
      show ?case unfolding r ta_rule.case
      proof (refine_vcg rule, goal_cases)
        case prems2: (3 i idone itodo m)
          then have "\<And>x. (qs!i,x) \<notin> dom2 todo" by (auto simp: dom2_def)
          with prems2 show ?case by simp
        next
        case prems2: (4 i idone itodo m rtodo)
          let ?iIt = "set idone" and ?qsiIt = "\<lambda>it. fst ` (map_to_set rtodo - it)"
          note rule = FOREACHc_rule'[where I = "\<lambda>it. new_rel_ok_inv3 ?rel ?accu rs (rs - rsit) f qs q ?iIt i (?qsiIt it)"]
          show ?case 
          proof (refine_vcg rule, simp_all only: it_step_insert_iff, goal_cases)
            case prems3: (4 _ qsiIt rel qsi)
              have "{(q, q') |q'. f qs[i := qsi] \<rightarrow> q' \<in> rs} \<subseteq> dom2 accu"
                using prems3(8) by (force simp: dom2_def split: ta_rule.splits)
              moreover from prems3(7) have "\<exists>q'. f qs[i := qsi] \<rightarrow> q' \<in> rs"
                by (force split: ta_rule.splits)
              ultimately show ?case using prems3(3) by simp blast
            next
            case prems3: (5 _ qsiIt rel qsi)
              let ?rhss = "{r \<in> rs. case r of f' qs' \<rightarrow> q' \<Rightarrow> f' = f \<and> qs' = qs[i := qsi]}"
              let ?dom = "{q} \<times> {q' \<in> r_rhs ` ?rhss. lookup2 accu q q' = None}"
              let ?rel = "{(q, q') |q'. f qs[i := qsi] \<rightarrow> q' \<in> rs} - dom2 accu"
              have "?dom = ?rel" proof
                show "?dom \<subseteq> ?rel" by (force simp: dom2_def split: ta_rule.splits)
                show "?rel \<subseteq> ?dom" proof
                  fix p p' assume "(p,p') \<in> ?rel"
                  then have "f qs[i := qsi] \<rightarrow> p' \<in> rs" "lookup2 accu p p' = None" "p = q"
                    by (auto simp: dom2_def)
                  then show "(p,p') \<in> ?dom" by (force split: ta_rule.split)
                qed
              qed
              moreover from prems3(7) have "\<exists>q'. f qs[i := qsi] \<rightarrow> q' \<in> rs" by (force split: ta_rule.splits)
              ultimately show ?case using prems3 by auto
            next
            case prems3: 6
              from prems2 have "fst ` map_to_set rtodo = {qsi. (qs ! i, qsi) \<in> dom2 todo}"
                by (auto simp: map_to_set_def dom2_def)
              with prems3 prems2 show ?case by auto
          qed (insert prems2, simp_all add: dom2_lu_finite[OF fin_todo])
      qed (insert prems1 upt_len_lt, simp_all)
  qed (simp_all add: fin_rs)
qed

lemma in_map_sng_eq:
  assumes "length xs = length ys"
      and "\<And>i. i < length xs \<Longrightarrow> xs!i \<in> (map (\<lambda>q. {q}) ys) ! i"
    shows "xs = ys"
using assms proof (induction rule: list_induct2)
  case (Cons x xs y ys)
    {
      fix i assume i: "i < length xs"
      with Cons.prems[of "Suc i"] have "xs!i \<in> (map (\<lambda>q. {q}) ys) ! i" by simp
    }
    with Cons.IH have "xs = ys" by auto
    moreover from Cons.prems[of 0] have "x = y" by simp
    ultimately show ?case by simp
qed simp

lemma in_map_sng_cons_app_eq:
  assumes i: "i < length qs" and len: "length qs' = length qs"
      and in_sng: "\<forall>j < length qs. qs'!j \<in> (map (\<lambda>q.{q}) (take i qs)@{qsi}#map (\<lambda>q.{q}) (drop (Suc i) qs))!j"
    shows "qs' = qs[i := qsi]"
proof -
  let ?qs' = "(take i qs)@qsi#(drop (Suc i) qs)"
  from i have len': "length qs = length ?qs'" by simp
  with in_sng have "qs' = ?qs'" by (metis in_map_sng_eq len list.simps(9) map_append)
  with i show "qs' = qs[i := qsi]" by (simp add: upd_conv_take_nth_drop)
qed

lemma new_rel_wit_rstep:
  assumes wit: "rel_wit_inv \<sigma> TA R (return rel)" "lookup2 rel (qs!i) qsi = Some (wl,wr)"
      and i: "i < length qs"
      and rule: "f qs \<rightarrow> q \<in> ta_rules TA" 
  defines [simp]: "qsa \<equiv> map Var (take i qs)" and [simp]: "qsb \<equiv> map Var (drop (Suc i) qs)"
    shows "ta_states_rstep TA R (Fun f (qsa@wl#qsb)) (Fun f (qsa@wr#qsb)) \<sigma>"
proof -
  note rel_wit_inv_def[simp] map2_to_set_def[simp]

  from wit have rstep: "(wl\<cdot>\<sigma>, wr\<cdot>\<sigma>) \<in> rstep R" by auto
  note ctxt_simps = intp_actxt.simps(2)[symmetric] subst_apply_term_ctxt_apply_distrib
  have rstep: "(Fun f (qsa@\<box>\<langle>wl\<rangle>#qsb) \<cdot> \<sigma>, Fun f (qsa@\<box>\<langle>wr\<rangle>#qsb) \<cdot> \<sigma>) \<in> rstep R"
    unfolding ctxt_simps using rstep by blast

  have "set qs \<subseteq> ta_states TA" using rule by (auto simp: ta_states_def r_states_def)
  then have "set (take i qs) \<subseteq> ta_states TA" "set (drop (Suc i) qs) \<subseteq> ta_states TA"
    using set_take_subset set_drop_subset by force+
  moreover from wit have "vars_term wl \<subseteq> ta_states TA" "vars_term wr \<subseteq> ta_states TA" by auto
  ultimately show ?thesis using rstep by auto
qed

lemma new_rel_wit_error:
  assumes det_TA: "ta_det TA"
      and wit: "rel_wit_inv \<sigma> TA R (return rel)" "lookup2 rel (qs!i) qsi = Some (wl,wr)"
      and rule: "f qs \<rightarrow> q \<in> ta_rules TA"
      and i: "i < length qs"
      and not_coh: "\<not>(\<exists> q'. (f (qs[i := qsi]) \<rightarrow> q') \<in> ta_rules TA)"
  defines [simp]: "qsa \<equiv> map Var (take i qs)" and [simp]: "qsb \<equiv> map Var (drop (Suc i) qs)"
    shows "rel_wit_inv \<sigma> TA R (error (q, Fun f (qsa@wl#qsb), Fun f (qsa@wr#qsb)))"
proof -
  note rel_wit_inv_def[simp] map2_to_set_def[simp]

  let ?C = "More f qsa \<box> qsb"
  from i have "i < length (map Var qs)" by simp
  note id_take_nth_drop[OF this, symmetric]
  then have ctxt: "?C\<langle>Var (qs!i)\<rangle> = Fun f (map Var qs)" using i by (auto simp: take_map drop_map) 
  have res: "q \<in> ta_res TA ?C\<langle>Var (qs!i)\<rangle>" unfolding ctxt using rule by auto
  from wit have "qs!i \<in> ta_res TA wl" by auto
  from ta_res_ctxt[OF this res] have wl: "q \<in> ta_res TA (Fun f (qsa@wl#qsb))" by simp

  from wit have "qsi \<in> ta_res TA wr" by auto
  with ta_detE[OF det_TA this] have [simp]: "ta_res TA wr = {qsi}" by blast
  have wr: "ta_res TA (Fun f (qsa@wr#qsb)) = {}" unfolding ctxt
  proof (rule equals0I)
    from det_TA have [simp]: "ta_res TA o Var = (\<lambda>q. {q})" by (auto simp: ta_det_def fun_eq_iff)
    from det_TA have [simp]: "ta_eps TA = {}" by (simp add: ta_det_def)
    fix p assume "p \<in> ta_res TA (Fun f (qsa@wr#qsb))"
    then have "f qs[i := qsi] \<rightarrow> p \<in> ta_rules TA" using i by (auto dest: in_map_sng_cons_app_eq[OF i])
    with not_coh show False by auto
  qed

  note wl wr new_rel_wit_rstep[OF wit i rule, folded qsa_def qsb_def]
  then show ?thesis by (auto simp del: qsa_def qsb_def)
qed

lemma new_rel_wit_ok:
  assumes wit: "rel_wit_inv \<sigma> TA R (return rel)" "lookup2 rel (qs!i) qsi = Some (wl,wr)"
      and i: "i < length qs"
      and rule: "f qs \<rightarrow> q \<in> ta_rules TA" "f qs[i := qsi] \<rightarrow> q' \<in> ta_rules TA"
  defines [simp]: "qsa \<equiv> map Var (take i qs)" and [simp]: "qsb \<equiv> map Var (drop (Suc i) qs)"
    shows "q \<in> ta_res TA (Fun f (qsa@wl#qsb))" "q' \<in> ta_res TA (Fun f (qsa@wr#qsb))"
          "ta_states_rstep TA R (Fun f (qsa@wl#qsb)) (Fun f (qsa@wr#qsb)) \<sigma>"
proof -
  note rel_wit_inv_def[simp] map2_to_set_def[simp]

  let ?C = "More f qsa \<box> qsb"
  from wit have wl: "qs!i \<in> ta_res TA wl" and wr: "qsi \<in> ta_res TA wr" by auto
  from id_take_nth_drop[symmetric, of i "map Var qs"] i
  have ctxt: "?C\<langle>Var (qs!i)\<rangle> = Fun f (map Var qs)" by (auto simp: take_map drop_map)
  have res: "q \<in> ta_res TA ?C\<langle>Var (qs!i)\<rangle>" unfolding ctxt using rule by auto
  from ta_res_ctxt[OF wl this] show "q \<in> ta_res TA (Fun f (qsa@wl#qsb))" by simp
  from id_take_nth_drop[symmetric, of i "map Var (qs[i := qsi])"] i
  have ctxt: "?C\<langle>Var (qsi)\<rangle> = Fun f (map Var (qs[i := qsi]))" by (auto simp: take_map drop_map) 
  have res: "q' \<in> ta_res TA ?C\<langle>Var (qsi)\<rangle>" unfolding ctxt using rule i by (simp, intro exI[of _ q'], auto)
  from ta_res_ctxt[OF wr this] show "q' \<in> ta_res TA (Fun f (qsa@wr#qsb))" by simp

  note new_rel_wit_rstep[OF wit i rule(1), folded qsa_def qsb_def]
  then show "ta_states_rstep TA R (Fun f (qsa@wl#qsb)) (Fun f (qsa@wr#qsb)) \<sigma>" .
qed
  
lemma new_relation_wit:
  assumes fin_TA: "ta_finite TA"
      and det_TA: "ta_det TA"
      and inv: "rel_wit_inv \<sigma> TA R (return todo)"
      and fin_todo: "finite (dom2 todo)"
  shows "new_rel (ta_rules TA) accu todo \<le> SPEC(rel_wit_inv \<sigma> TA R)"
proof -
  note rule_foreach = FOREACHc_rule'[where I = "\<lambda>_. rel_wit_inv \<sigma> TA R"]
  note rule_nfoldli = nfoldli_rule[where I = "\<lambda>_ _. rel_wit_inv \<sigma> TA R"]
  have [simp]: "\<And>q. eps_cl TA q = {q}" using assms by (auto simp: ta_det_def)
  show ?thesis unfolding new_rel_def
  proof (refine_vcg rule_foreach ta_rule_rule rule_nfoldli rule_foreach, goal_cases)
    case prems: (5 _ _ _ f qs q i _ _ _ _ _ _ _ qsi _ wl wr)
      then have "i < length qs" by (auto intro!: upt_len_lt)
      moreover from prems have "lookup2 todo (qs!i) qsi = Some (wl, wr)" by (auto simp: map_to_set_def)
      moreover from prems have "\<not>(\<exists> q'. (f (qs[i := qsi]) \<rightarrow> q') \<in> ta_rules TA)" by auto
      moreover from prems have "f qs \<rightarrow> q \<in> ta_rules TA" by auto
      ultimately show ?case by (intro new_rel_wit_error, insert assms, auto)
    next
    case prems: (6 _ _ x f qs q i _ _ rel' _ _ _ rel qsi _ wl wr)
      then have i: "i < length qs" by (auto intro!: upt_len_lt)
      let ?rhss = "r_rhs ` {r \<in> ta_rules TA. case r of f' qs' \<rightarrow> q' \<Rightarrow> f' = f \<and> qs' = qs[i := qsi]}"
      have rule': "\<And>p. p \<in> {q' \<in> ?rhss. lookup2 accu q q' = None} \<Longrightarrow> f qs[i := qsi] \<rightarrow> p \<in> ta_rules TA"
        by (force split: ta_rule.splits)
      from prems have lu: "lookup2 todo (qs!i) qsi = Some (wl, wr)" by (auto simp: map_to_set_def)
      from prems have rule: "f qs \<rightarrow> q \<in> ta_rules TA" by auto
      from prems obtain m where inner_inv: "rel = return m" "rel_wit_inv \<sigma> TA R (return m)" by auto
      show ?case unfolding rel_wit_inv_def sum.case using inner_inv new_rel_wit_ok[OF inv lu i rule rule']
        by (intro update_all2_ballI, auto simp: rel_wit_inv_def)
  qed (auto intro: ta_finiteD[OF fin_TA] dom2_lu_finite[OF fin_todo] upt_len_lt)
qed

lemma new_relation_empty:
  assumes fin_rs: "finite rs"
      and fin_todo: "finite (dom2 todo)"
    shows "new_rel rs accu todo \<le> SPEC(rel_empty_inv)"
proof -
  note simps = dom2_lu_finite[OF fin_todo] fin_rs rel_empty_inv_def
  note foreach_rule = FOREACHc_rule'[where I = "\<lambda>_. rel_empty_inv"]
  note rule_nfoldli = nfoldli_rule[where I = "\<lambda>_ _. rel_empty_inv"]
  show ?thesis unfolding new_rel_def
    by (refine_vcg foreach_rule ta_rule_rule rule_nfoldli foreach_rule,
        simp_all add: simps upt_len_lt, intro update_all2_not_empty2, auto)
qed

lemma new_relation_finite:
  assumes fin_rs: "finite rs"
      and fin_todo: "finite (dom2 todo)"
    shows "new_rel rs accu todo \<le> SPEC(rel_finite_inv)"
proof -
  note simps = dom2_lu_finite[OF fin_todo] fin_rs rel_finite_inv_def
  note foreach_rule = FOREACHc_rule'[where I = "\<lambda>_. rel_finite_inv"]
  note rule_nfoldli = nfoldli_rule[where I = "\<lambda>_ _. rel_finite_inv"]
  show ?thesis unfolding new_rel_def
    by (refine_vcg foreach_rule ta_rule_rule rule_nfoldli foreach_rule,
        simp_all add: simps upt_len_lt)
qed

subsubsection \<open>Checking state coherence iteratively\<close>

inductive is_coh_iterate for rs rel where
  start: "\<lbrakk>is_coh rel rs; new = req_rel rel rel rs\<rbrakk> 
    \<Longrightarrow> is_coh_iterate rs rel new (new \<union> rel)"
| iterate: "\<lbrakk>is_coh_iterate rs rel todo accu; is_coh todo rs; new = req_rel todo accu rs\<rbrakk> 
    \<Longrightarrow> is_coh_iterate rs rel new (new \<union> accu)"

definition "rule_coherent rel rs \<equiv> \<forall> f qs q i qi.
  TA_rule f qs q \<in> rs \<longrightarrow> i < length qs \<longrightarrow> (qs!i,qi) \<in> rel \<longrightarrow> 
  (\<exists> q'. (f (qs[ i := qi]) \<rightarrow> q') \<in> rs \<and> (q,q') \<in> rel)"

lemma det_rule_coherent:
  assumes "ta_det TA"
      and final: "rel `` ta_final TA \<subseteq> ta_final TA "
    shows "state_coherent TA rel = rule_coherent rel (ta_rules TA)"
proof -
  from assms have "ta_eps TA = {}" by (auto simp: ta_det_def)
  with final show ?thesis by (auto simp: state_coherent_def rule_coherent_def)
qed

lemma req_rel_new:
    shows "req_rel todo accu rs \<inter> accu = {}"
unfolding req_rel_defs by auto

lemma coherence_empty_simps[simp]:
  "req_rel {} accu rs = {}"
  "state_coherent TA {}"
  "is_coh {} rs"
unfolding req_rel_defs state_coherent_def is_coh_defs by (auto split: ta_rule.split)

lemma is_coh_iterate_empty[simp]:
  "is_coh_iterate rs {} {} {}"
by (intro start[of "{}" rs "{}", simplified])

lemma req_rel_sound:
  assumes rule: "TA_rule f qs q \<in> rs"
      and i: "i < length qs"
      and qi: "(qs!i, qi) \<in> todo"
      and rule': "f qs[i := qi] \<rightarrow> q' \<in> rs"
    shows "(q,q') \<in> req_rel todo accu rs \<union> accu"
proof -
  from rule' have "(q,q') \<in> req_rel_it_rule_arg accu rs f qs q i {qi} \<union> accu" by (auto simp: req_rel_defs)
  with qi have "(q,q') \<in> req_rel_it_rule todo accu rs f qs q {i} \<union> accu" by (auto simp: req_rel_defs)
  with i have "(q,q') \<in> req_rel_it todo accu rs {f qs \<rightarrow> q} \<union> accu" by (auto simp: req_rel_defs)
  with rule show ?thesis by (auto simp: req_rel_defs)
qed

lemma coherent_union:
  assumes A: "is_coh A rs" and B: "is_coh B rs"
    shows "is_coh (A \<union> B) rs"
unfolding is_coh_defs proof (split ta_rule.split, intro allI impI ballI)
  fix r f qs q i qsi
  assume rs: "r \<in> rs" and r: "r = TA_rule f qs q" and i: "i \<in> {0..<length qs}"
     and qsi: "qsi \<in> {qsi. (qs!i, qsi) \<in> A \<union> B}"
  from qsi have "(qs!i, qsi) \<in> A \<or> (qs!i, qsi) \<in> B" by blast
  then show "\<exists>q'. f qs[i := qsi] \<rightarrow> q' \<in> rs"
  proof (elim disjE)
    assume "(qs ! i, qsi) \<in> A"
    moreover note A[unfolded is_coh_defs, rule_format, OF rs, unfolded r] i
    ultimately show ?thesis by auto
    next
    assume "(qs ! i, qsi) \<in> B"
    moreover note B[unfolded is_coh_defs, rule_format, OF rs, unfolded r] i
    ultimately show ?thesis by auto
  qed
qed

lemma is_coh_iterate_increase:
  assumes "is_coh_iterate rs rel todo accu"
    shows "rel \<subseteq> accu"
using assms by (induction) auto

lemma req_rel_states:
  shows "req_rel todo accu rs \<subseteq> r_rhs ` rs \<times> r_rhs ` rs"
proof
  fix q q' assume "(q,q') \<in> req_rel todo accu rs"
  from this obtain f qs qs' where "f qs \<rightarrow> q \<in> rs" "f qs' \<rightarrow> q' \<in> rs"
    unfolding req_rel_defs by auto
  then show "(q,q') \<in> r_rhs ` rs \<times> r_rhs ` rs" by force
qed

lemma is_coh_iterate_states:
  assumes coh: "is_coh_iterate rs rel todo accu"
  defines [simp]: "rhs \<equiv> r_rhs ` rs"
    shows "todo \<subseteq> rhs \<times> rhs \<and> accu \<subseteq> rhs \<times> rhs \<union> rel"
using coh proof (induction rule: is_coh_iterate.induct)
  case (start new)
    with req_rel_states have "new \<subseteq> rhs \<times> rhs" by simp
    then show ?case by blast
  next
  case (iterate todo accu new)
    with req_rel_states have "new \<subseteq> rhs \<times> rhs" by simp
    with iterate show ?case by blast
qed

lemma is_coh_iterate_inv:
  assumes "is_coh_iterate rs rel new accu"
    shows "is_coh (accu - new) rs \<and> new \<subseteq> accu"
using assms proof (induction)
  case (start new)
    with req_rel_new have "new \<union> rel - new = rel" by blast
    with start show ?case by simp
  next
  case (iterate todo accu new)
    with req_rel_new have "new \<union> accu - new = accu" by blast
    moreover from iterate have "is_coh ((accu - todo) \<union> todo) rs" by (intro coherent_union, blast)
    moreover from iterate have "(accu - todo) \<union> todo = accu" by blast
    ultimately show ?case by simp
qed

lemma is_coh_iterate_sound:
  assumes rule: "TA_rule f qs q \<in> rs"
      and i: "i < length qs"
      and qi: "(qs!i, qi) \<in> (accu - new)"
      and rule': "f qs[i := qi] \<rightarrow> q' \<in> rs"
      and coh: "is_coh_iterate rs rel new accu"
    shows "(q,q') \<in> new \<union> accu"
using coh qi proof (induction)
  case (start new)
    with req_rel_new have new: "new \<union> rel - new = rel" by blast
    from start req_rel_sound[OF rule i start(3) rule'] show ?case unfolding new by auto
  next
  case (iterate todo accu new)
    with req_rel_new have new: "new \<union> accu - new = accu" by blast
    note iterate = iterate[unfolded new]
    show ?case proof (cases "(qs!i, qi) \<in> todo")
      case False
        with iterate(4,5) is_coh_iterate_inv[OF iterate(1)] have "(q, q') \<in> accu" by blast
        then show ?thesis by blast
      next
      case True
        from iterate(3) req_rel_sound[OF rule i True rule', of accu] show ?thesis by simp
    qed
qed
  
lemma is_coh_iterate_coherent:
  assumes coh: "is_coh_iterate rs init {} accu"
    shows "rule_coherent accu rs"
unfolding rule_coherent_def proof (intro impI allI)
  fix f qs q i qi
  assume prems: "f qs \<rightarrow> q \<in> rs" "i < length qs" "(qs ! i, qi) \<in> accu"
  from is_coh_iterate_inv[OF coh] have "is_coh accu rs" by simp
  note this[unfolded is_coh_defs, rule_format, OF prems(1)] prems
  from this obtain q' where "f qs[i := qi] \<rightarrow> q' \<in> rs" by force
  moreover note is_coh_iterate_sound[where new = "{}", simplified, OF prems this coh]
  ultimately show "\<exists>q'. f qs[i := qi] \<rightarrow> q' \<in> rs \<and> (q, q') \<in> accu" by blast
qed

definition is_coh_iterate_ref where
  "is_coh_iterate_ref rs rel \<equiv> do {
    (wit,rel) \<leftarrow> WHILE\<^sub>T 
      (\<lambda>(todo,accu). case todo of error w \<Rightarrow> False | return todo \<Rightarrow> todo \<noteq> Map.empty)
      (\<lambda>(todo,accu). do {
        ASSERT (isOK todo);
        new \<leftarrow> new_rel rs accu (run todo);
        if isOK new then
          RETURN (new, map_add2 accu (run new))
        else
          RETURN (new, accu)
      }) (return rel, rel);
    if isOK wit then
      RETURN (return rel)
    else
      RETURN wit
  }"

definition "is_coh_final fin rel \<equiv>
  FOREACH\<^sub>C (map_to_set rel) is_None (\<lambda>(q,qs') err. 
    if q \<in> fin then
      FOREACH\<^sub>C (map_to_set qs') is_None (\<lambda>(q',wl,wr) err.
        if q' \<in> fin then
          RETURN None
        else
          RETURN (Some (wl,wr))
      ) None
    else
      RETURN None
  ) None"

definition ta_check_comcoh_trim where
  "ta_check_comcoh_trim TA R res prs \<equiv>
    do {
      err \<leftarrow> is_compatible TA R;
      let wit = ta_lang_wit res prs in
      case err of
        error (q,wl,wr) \<Rightarrow> RETURN (Some (wit q wl, wit q wr))
      | return rel \<Rightarrow> do {
          err \<leftarrow> is_coh_iterate_ref (ta_rules TA) rel;
          case err of
            error (q,wl,wr) \<Rightarrow> RETURN (Some (wit q wl, wit q wr))
          | return rel \<Rightarrow> do {
              err \<leftarrow> is_coh_final (ta_final TA) rel;
              case err of
                Some (wl,wr) \<Rightarrow> RETURN (Some (wl \<cdot> (the o res), wr \<cdot> (the o res)))
              | None \<Rightarrow> RETURN None
            }
        }
    }"

locale ta_fin_trim_det =
  fixes TA :: "('q, 'f) ta"
    and R :: "(('f,'v)term \<times> ('f,'v) term) set"
  assumes det_TA: "ta_det TA"
      and fin_TA: "ta_finite TA"
      and fin_R: "finite R"
      and wf_R: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin

context begin

private abbreviation "rs \<equiv> ta_rules TA"
private abbreviation "rhss2 \<equiv> r_rhs ` rs \<times> r_rhs ` rs"

lemma fin_rs[iff]: "finite rs" using fin_TA by (elim ta_finiteD)
lemma fin_rhss2[iff]: "finite rhss2" using fin_TA by (auto dest: ta_finiteD) 

lemma new_relation_spec:
  assumes inv: "rel_wit_inv \<sigma> TA R (return todo)"
      and todo: "finite (dom2 todo)"
    shows "new_rel rs accu todo \<le>
            SPEC (\<lambda>v. new_rel_ok_inv (dom2 todo) (dom2 accu) rs v \<and>
                      rel_wit_inv \<sigma> TA R v \<and>
                      rel_empty_inv v)"
proof -
  note intros = SPEC_rule_conjI new_relation_ok_correct new_relation_wit new_relation_empty
  from fin_TA det_TA assms show ?thesis by (auto intro!: intros)
qed

definition is_coh_term_measure where
  "is_coh_term_measure all \<equiv>
     inv_image ({(False,True)} <*lex*> less_than)
      (\<lambda>(t,a). (isOK t, card all - (card (dom2 a) - card(dom2r t))))"

lemma is_coh_term_measure_wf[iff]:
  "wf (is_coh_term_measure x)"
unfolding is_coh_term_measure_def by auto

lemma is_coh_term_measure_error[intro]:
  "\<not> isOK a \<Longrightarrow> ((a,b),(return c,d)) \<in> is_coh_term_measure x"
unfolding is_coh_term_measure_def by simp

abbreviation retw :: "_ \<Rightarrow> 'q \<times> ('f, 'q)term \<times> ('f, 'q)term + _" where "retw \<equiv> return"

definition is_coh_iterate_ref_inv where
  "is_coh_iterate_ref_inv rel \<sigma> \<equiv> \<lambda>(todo,accu). 
    rel_wit_inv \<sigma> TA R todo \<and> rel_wit_inv \<sigma> TA R (return accu) \<and>
    rel_empty_inv todo \<and> rel_empty_inv (retw accu) \<and>
    (isOK todo \<longrightarrow>
      (let rel = dom2 rel; todo' = dom2r todo; accu = dom2 accu in
        (is_coh_iterate rs rel todo' accu) \<or> (accu = todo' \<and> todo' = rel)))"

lemma is_coh_iterate_ref_inv_preserve:
  assumes it_inv: "is_coh_iterate_ref_inv rel \<sigma> (return todo, accu)"
      and new_inv: "new_rel_ok_inv (dom2 todo) (dom2 accu) rs (return new)"
      and empty_inv: "rel_empty_inv (retw new)"
      and wit_inv: "rel_wit_inv \<sigma> TA R (return new)"
    shows "is_coh_iterate_ref_inv rel \<sigma> (return new, map_add2 accu new)"
proof -
  let ?rel = "dom2 rel" and ?accu = "dom2 accu" and ?todo = "dom2 todo" and ?new = "dom2 new"
  note simps[simp] = new_rel_ok_inv1_def is_coh_iterate_ref_inv_def Let_def
  from it_inv have "rel_wit_inv \<sigma> TA R (return accu)" by simp
  with wit_inv have accu_wit_inv: "rel_wit_inv \<sigma> TA R (return (map_add2 accu new))"
    by (simp add: rel_wit_inv_def, intro map_add2_ballI, auto)
  from it_inv empty_inv have empty_inv': "rel_empty_inv (retw (map_add2 accu new))"
    by (auto split: option.split simp: map_add2_def ran_def rel_empty_inv_def)
  show ?thesis 
  proof (cases "?accu = ?todo \<and> ?todo = ?rel")
  case True
    with new_inv have "is_coh_iterate rs ?rel ?new (?new \<union> ?accu)" by (auto intro: start)
    with empty_inv empty_inv' wit_inv accu_wit_inv show ?thesis by (simp add: Un_commute rel_empty_inv_def)
  next
  case False
    with it_inv have "is_coh_iterate rs ?rel ?todo ?accu" by simp
    with new_inv have "is_coh_iterate rs ?rel ?new (?new \<union> ?accu)" by (auto intro: iterate)
    with empty_inv empty_inv' wit_inv accu_wit_inv show ?thesis by (simp add: Un_commute rel_empty_inv_def)
  qed
qed

lemma is_coh_iterate_ref_term:
  assumes fin_rel: "finite (dom2 rel)"
      and it_inv: "is_coh_iterate_ref_inv rel \<sigma> (return todo, accu)"
      and new_inv: "new_rel_ok_inv (dom2 todo) (dom2 accu) rs (return new)"
      and empty_inv: "rel_empty_inv (return new)"
      and not_empty: "todo \<noteq> Map.empty"
  defines "bound \<equiv> dom2 rel \<union> r_rhs ` rs \<times> r_rhs ` rs"
    shows "((return new, map_add2 accu new), (return todo, accu)) \<in> is_coh_term_measure bound"
proof -
  let ?rel = "dom2 rel" and ?accu = "dom2 accu" and ?todo = "dom2 todo" and ?new = "dom2 new"
  note simps[simp] = new_rel_ok_inv1_def is_coh_iterate_ref_inv_def Let_def is_coh_term_measure_def
  from new_inv have new: "?new = req_rel ?todo ?accu rs" by simp
  with req_rel_states have "?new \<subseteq> rhss2" by blast
  then have fin_new: "finite ?new" using finite_subset by auto
  show ?thesis 
  proof (cases "?accu = ?todo \<and> ?todo = ?rel")
    case True
      with it_inv not_empty have not_empty: "?rel \<noteq> {}" by (auto dest: rel_empty_inv)
      with fin_rel have card_rel: "card ?rel > 0" by auto
      from not_empty fin_rel have card_bound: "card bound > 0" by (auto simp: bound_def)
      note req_rel_new card_Un_disjoint[OF fin_new fin_rel]
      then have "card (?new \<union> ?rel) = card ?new + card ?rel" by (auto simp: True new)
      with empty_inv True card_rel card_bound show ?thesis by (simp add: equal Un_commute)
    next
    case False
      with it_inv not_empty have
        is_coh: "is_coh_iterate rs ?rel ?todo ?accu" and
        todo: "?todo \<noteq> {}" by (auto dest: rel_empty_inv)
      with is_coh have rel: "?rel \<noteq> {}" by (induction, auto simp: req_rel_defs)
      with is_coh_iterate_increase[OF is_coh] have "?accu \<noteq> {}" by blast
      note not_empty = todo rel this
      note is_coh_iterate_states[OF is_coh] fin_rel finite_subset
      then have fin: "finite ?todo" "finite ?accu" "finite bound" "card ?accu \<le> card bound" by (auto simp: bound_def intro: card_mono)
      from fin not_empty have card: "card bound > 0" "card ?todo > 0" "card ?accu > 0" by (auto simp: bound_def)
      note req_rel_new card_Un_disjoint[OF fin_new fin(2)]
      then have "card (?new \<union> ?accu) = card ?new + card ?accu" by (auto simp: new)
      with empty_inv fin card show ?thesis by (simp add: bound_def Un_commute)
  qed
qed

lemma is_coh_iterate_finite_todo:
assumes fin_rel: "finite (dom2 rel)"
    and inv: "is_coh_iterate_ref_inv rel \<sigma> (return todo, accu)"
  shows "finite (dom2 todo)"
proof (cases "dom2 todo = dom2 rel")
case False
  with inv have "is_coh_iterate rs (dom2 rel) (dom2 todo) (dom2 accu)" by (auto simp: is_coh_iterate_ref_inv_def)
  from is_coh_iterate_states[OF this] have "dom2 todo \<subseteq> rhss2" by blast
  then show ?thesis using finite_subset by auto
qed (simp add: fin_rel)

lemma is_coh_iterate_refine:
  assumes wit_inv: "rel_wit_inv \<sigma> TA R (return rel)"
      and empty_inv: "rel_empty_inv (retw rel)"
      and fin_rel: "finite (dom2 rel)"
    shows "is_coh_iterate_ref rs rel \<le>
            SPEC(\<lambda>m. rel_wit_inv \<sigma> TA R m \<and> rel_empty_inv m \<and>
              (isOK m \<longrightarrow> is_coh_iterate rs (dom2 rel) {} (dom2r m)))"
proof -
  let ?all = "dom2 rel \<union> rhss2"
  note rule = WHILET_rule[where R="is_coh_term_measure ?all" and I="is_coh_iterate_ref_inv rel \<sigma>"]
  show ?thesis unfolding is_coh_iterate_ref_def
  proof (refine_vcg rule order_trans[OF new_relation_spec, of \<sigma>], goal_cases)
    case (5 _ todo accu)
      then have "is_coh_iterate_ref_inv rel \<sigma> (return (run todo), accu)" by (cases todo, auto)
      then show ?case by (rule is_coh_iterate_finite_todo[OF fin_rel])
    next
    case prems: (6 s todo accu enew)
      from this obtain new where err: "enew = return new" by auto
      from prems show ?case by (cases todo, simp_all add: err, intro is_coh_iterate_ref_inv_preserve, auto)
    next
    case prems: (7 s todo accu enew)
      from this obtain new where err: "enew = return new" by auto
      from prems show ?case by (cases todo, simp_all add: err, intro is_coh_iterate_ref_term[OF fin_rel], auto)
    next
  qed (insert assms, auto split: sum.splits simp: is_coh_iterate_ref_inv_def Let_def)
qed

lemma map_it_fst_diff_distrib:
  assumes "i \<in> it"
      and "it \<subseteq> map_to_set m"
    shows "fst ` (it - {i}) = fst ` it - {fst i}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" proof
    fix x assume *: "x \<in> ?lhs"
    from this obtain y where y: "x = fst y" "y \<in> it - {i}" by fastforce
    with assms have "y \<in> map_to_set m" "it - {i} \<subseteq> map_to_set m" by auto
    note inj_on_image_mem_iff[OF inj_on_fst_map_to_set this] inj_on_fst_map_to_set[of m]
    with * assms show "x \<in> ?rhs" unfolding y by (auto simp: inj_on_def)
  qed
qed auto 
    
lemma is_coh_final_ok_correct:
  assumes "finite (dom rel)" and "finite (dom2 rel)"
  shows "is_coh_final fin rel \<le>
          SPEC(\<lambda>err. err = None \<longrightarrow> (\<forall>(q,q') \<in> dom2 rel. q \<in> fin \<longrightarrow> q' \<in> fin))"
proof -
  let ?I = "\<lambda>rel err. err = None \<longrightarrow> (\<forall>(q,q') \<in> rel. q \<in> fin \<longrightarrow> q' \<in> fin)"
  from assms have "finite (map_to_set rel)" by (simp add: finite_map_to_set) 
  note outer_foreach = FOREACHc_rule[OF this, where I = "\<lambda>it err. ?I {(q,q') \<in> dom2 rel. q \<notin> fst ` it} err"]
  show ?thesis unfolding is_coh_final_def
  proof (refine_vcg outer_foreach, goal_cases)
    case 1
    then show ?case by (auto simp: dom2_def map_to_set_def split: bind_splits)
  next
    case outer_prems: (2 i oit err q qs')
      with assms have fin: "finite (map_to_set qs')" by (intro dom2_lu_finite[of rel], auto simp: map_to_set_def) 
      let ?I = "\<lambda>it err. ?I ({(q,q') \<in> dom2 rel. q \<notin> fst ` oit} \<union> {q} \<times> (dom qs' - fst ` it)) err"
      note inner_foreach = FOREACHc_rule[OF fin, where I = ?I]
      show ?case
      proof (refine_vcg inner_foreach, goal_cases)
        case 1
          with outer_prems show ?case by (auto simp: map_to_set_dom) next
        case inner_prems: (2 i iti err q' _ wl wr)
          then have "q' \<in> fst ` iti" "fst ` iti \<subseteq> dom qs'" by (auto simp: map_to_set_dom)
          with inner_prems have "dom qs' - fst ` (iti - {i}) = insert (fst i) (dom qs' - fst ` iti)"
            by (simp add: map_it_fst_diff_distrib it_step_insert_iff)
          with inner_prems show ?case by auto next
        case inner_prems: 4
          from outer_prems have qs: "\<And>b. (q, b) \<in> dom2 rel \<Longrightarrow> b \<in> dom qs'" by (auto simp: map_to_set_def dom2_def)
          from inner_prems outer_prems show ?case by (auto dest!: qs simp: map_it_fst_diff_distrib)
      qed simp_all next
  qed (auto simp: map_it_fst_diff_distrib)
qed

definition rel_wit_final_inv where
  "rel_wit_final_inv \<sigma> err \<equiv> case_option True (\<lambda>(wl,wr). 
    ta_states_rstep TA R wl wr \<sigma> \<and>
    ta_res TA wl \<inter> ta_final TA \<noteq> {} \<and> ta_res TA wr \<inter> ta_final TA = {}) err"

lemma is_coh_final_wit:
 assumes wit_inv: "rel_wit_inv \<sigma> TA R (return rel)"
     and "finite (dom rel)" and "finite (dom2 rel)"
   shows "is_coh_final (ta_final TA) rel \<le> SPEC(rel_wit_final_inv \<sigma>)"
proof -
  note foreach_rule = FOREACHc_rule[where ?I = "\<lambda>_. rel_wit_final_inv \<sigma>"]
  show ?thesis unfolding is_coh_final_def
  proof (refine_vcg foreach_rule, goal_cases)
    case 3
      with assms show ?case by (intro dom2_lu_finite[of rel], auto simp: map_to_set_def) next
    case prems: (6 _ _ err' q _ _ _ err q' _ wl wr)
      then have lu2: "lookup2 rel q q' = Some (wl,wr)" by (auto simp: map_to_set_def bind_eq_Some_conv)
      with ta_detE[OF det_TA] wit_inv have "ta_res TA wl = {q}" "ta_res TA wr = {q'}"
        by (simp_all add: rel_wit_inv_def map2_to_set_def, blast+)
      with prems have "ta_res TA wl \<inter> ta_final TA \<noteq> {}" "ta_res TA wr \<inter> ta_final TA = {}" by auto
      moreover from lu2 wit_inv have "ta_states_rstep TA R wl wr \<sigma>" by (auto simp: map2_to_set_def rel_wit_inv_def)
      ultimately show ?case by (auto simp: rel_wit_final_inv_def)
  qed (simp_all add: rel_wit_final_inv_def finite_map_to_set assms)
qed

lemma is_coh_iterate_finite:
  assumes fin: "finite (dom2 rel)"
      and coh: "is_coh_iterate rs (dom2 rel) {} (dom2 accu)"
    shows "finite (dom2 accu)"
using fin is_coh_iterate_states[OF coh] by (auto intro: finite_subset)

lemma rel_empty_inv_dom:
  assumes "rel_empty_inv (return m)"
    shows "dom m = fst ` dom2 m"
proof
  show "fst ` dom2 m \<subseteq> dom m" unfolding dom2_def dom_def by (auto split: bind_splits)
  show "dom m \<subseteq> fst ` dom2 m" proof
    fix x assume "x \<in> dom m"
    from this obtain v where v: "m x = Some v" by auto
    with assms have "v \<noteq> Map.empty" by (auto simp: rel_empty_inv_def ran_def)
    from this obtain k v' where "v k = Some v'" by force
    with v show "x \<in> fst ` dom2 m" by (auto simp: dom2_def bind_eq_Some_conv)
  qed
qed

lemma rel_empty_inv_finite:
  assumes "rel_empty_inv (return m)"
      and "finite (dom2 m)"
    shows "finite (dom m)"
using assms by (auto simp: rel_empty_inv_dom)

lemma comcoh_closed:
  assumes com_inv: "is_compatible_ok_inv TA R (return rel)"
  assumes coh_inv: "is_coh_iterate rs (dom2 rel) {} (dom2 accu)"
  assumes fin: "\<forall>(q,q') \<in> dom2 accu. q \<in> ta_final TA \<longrightarrow> q' \<in> ta_final TA"
    shows "rstep R `` ta_lang TA \<subseteq> ta_lang TA"
proof -
  from is_coh_iterate_increase[OF coh_inv] have "dom2 rel \<subseteq> dom2 accu" .
  from com_inv state_compatible_itR_mono[OF this] have
    "state_compatible_itR TA R (dom2 accu)" by (auto simp: is_compatible_ok_inv_def)
  with state_compatible_itR[OF wf_R] have com: "state_compatible TA (dom2 accu) R" by blast
  from assms is_coh_iterate_coherent have "rule_coherent (dom2 accu) rs" by blast
  with assms det_rule_coherent[OF det_TA, of "dom2 accu"] have
    coh: "state_coherent TA (dom2 accu)" by auto
  from  det_TA wf_R show ?thesis by (intro state_compatible_lang[OF com coh]) auto
qed

lemmas comcoh_aux = 
  SPEC_rule_conjI[OF is_compatible_empty[OF fin_R fin_TA]
  SPEC_rule_conjI[OF is_compatible_finite[OF fin_R fin_TA]
  SPEC_rule_conjI[OF is_compatible_wit[OF fin_R fin_TA wf_R, where \<sigma> = "the o res"]
                     is_compatible_ok_correct[OF fin_R fin_TA]]]]
 is_coh_iterate_refine[where \<sigma> = "the o res"]
 is_coh_final_ok_correct for res

lemma check_comcoh_sound:
  "ta_check_comcoh_trim TA R res prs \<le> SPEC(\<lambda>err. err = None \<longrightarrow> rstep R `` ta_lang TA \<subseteq> ta_lang TA)"
unfolding ta_check_comcoh_trim_def
apply (refine_vcg comcoh_aux[THEN order_trans] sum_rule; (intro comcoh_closed)?)
apply (simp_all add: fin_R fin_TA rel_finite_inv_def)
apply (auto intro: rel_empty_inv_finite is_coh_iterate_finite)
done

lemma check_comcoh_complete:
  assumes res: "\<And>q. q \<in> ta_states TA \<Longrightarrow> is_ad_res_wit TA q (the (res q))"
  assumes prs: "\<And>q. q \<in> ta_states TA \<Longrightarrow> is_prs_wit TA q (the (prs q))"
  shows "ta_check_comcoh_trim TA R res prs \<le>
    SPEC(case_option True (\<lambda>(wl,wr). (wl,wr) \<in> rstep R \<and> wl \<in> ta_lang TA \<and> wr \<notin> ta_lang TA))"
proof -
  from res have res':
    "\<And>t. vars_term t \<subseteq> ta_states TA \<Longrightarrow> (\<And>q. q \<in> vars_term t \<Longrightarrow> is_ad_res_wit TA q (the (res q)))"
  by blast

  note rule =
    comcoh_aux(1,2)[THEN order_trans]
    is_coh_final_wit[where \<sigma> = "the o res", THEN order_trans]
  note simps = rel_finite_inv_def rel_wit_inv_def rel_wit_final_inv_def
  note intros =
    ta_lang_wit_rstep ta_lang_wit[OF assms] ta_lang_nowit[OF det_TA res']
    res_wit_subst_lang[OF res'] res_nowit_subst_lang[OF det_TA res']

  show ?thesis unfolding ta_check_comcoh_trim_def    
  apply (refine_vcg rule sum_rule; simp add: simps; (intro conjI intros)?)
  apply (auto intro: rel_empty_inv_finite is_coh_iterate_finite)
  done
qed
end
end

definition ta_check_comcoh where
  "ta_check_comcoh TA R \<equiv> do {
    (TA, res, prs) \<leftarrow> trim_ta_wits TA;
    ta_check_comcoh_trim TA R res prs
  }"

lemma ta_check_comcoh_correct:
    fixes R :: "(('f,'v)term \<times> ('f,'v)term)set"
  assumes ta_finite: "ta_finite TA" and trs_finite: "finite R"
      and det: "ta_det TA"
      and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    shows "ta_check_comcoh TA R \<le>
            SPEC(\<lambda>err. case err of
              None \<Rightarrow> rstep R `` ta_lang TA \<subseteq> ta_lang TA
            | Some (wl,wr) \<Rightarrow> (wl,wr) \<in> rstep R \<and> wl \<in> ta_lang TA \<and> wr \<notin> ta_lang TA)"
unfolding ta_check_comcoh_def
proof (refine_vcg trim_ta_wits_correct[OF ta_finite, THEN order_trans, where ?'x1 = 'v], goal_cases)
  case (1 _ TA' _ res prs)
    then have
      trim: "ta_trim TA'" and
      subset: "ta_subset TA' TA" and
      lang: "(ta_lang TA::('f,'v) terms) = ta_lang TA'" and
       res: "\<And>q. q \<in> ta_states TA' \<Longrightarrow> is_ad_res_wit TA' q (the (res q))" and
       prs: "\<And>q. q \<in> ta_states TA' \<Longrightarrow> is_prs_wit TA' q (the (prs q))"
    by simp_all
    note det = ta_subset_det[OF subset det] and ta_finite = ta_subset_finite[OF subset ta_finite]
    interpret ta_fin_trim_det TA' R by (unfold_locales) (intro det ta_finite trs_finite wf)+
    note rule = SPEC_rule_conjI[OF check_comcoh_sound check_comcoh_complete[OF res prs]]
    show ?case by (refine_vcg rule[THEN order_trans], auto split: option.split simp: lang)
qed

end
