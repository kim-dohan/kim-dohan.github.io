theory Tree_Automata_Det_Impl
imports
  Tree_Automata_Wit_Impl
  Tree_Automata_Det
begin

no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open>Refinement to Executable Version\<close>

definition ps_states_nil where
  "ps_states_nil eps rules = {q | q f. q = ps_state eps rules f [] \<and> q \<noteq> {}}"

lemma ps_states_nil:
  "ps_states_nil eps rules = ps_states_new eps rules {}"
unfolding ps_states_new_def ps_states_nil_def by auto

abbreviation eps_cl where "eps_cl eps q \<equiv> {p. (q,p) \<in> eps\<^sup>*}"

definition "rhs_eps_cl_memo memo rules \<equiv> \<Union>((memo o r_rhs) ` rules)"

lemma rhs_eps_cl_memo:
  "rhs_eps_cl_memo (memo_rtrancl eps) rules = {q' | f qs q q'. f qs \<rightarrow> q \<in> rules \<and> (q,q') \<in> eps\<^sup>*}"
unfolding rhs_eps_cl_memo_def memo_rtrancl_def[abs_def] by (force simp: r_rhs_unfold split: ta_rule.splits)

definition ps_states_nil_impl where
  "ps_states_nil_impl meps rules \<equiv>
    let rsz = {r \<in> rules. r_lhs_states r = []} in
      (\<lambda>f. rhs_eps_cl_memo meps {r \<in> rsz. r_root r = f}) ` (r_root ` rsz)"

definition ps_states_cons where
  "ps_states_cons eps rules Q = {q | q ps f. set ps \<subseteq> Q \<and> ps \<noteq> [] \<and> q = ps_state eps rules f ps \<and> q \<noteq> {}}"

fun list_inter where
  "list_inter [] = UNIV"
| "list_inter [x] = x"
| "list_inter (x#xs) = x \<inter> list_inter xs"

lemma list_inter: "list_inter x = \<Inter>(set x)" 
proof (induction x)
  case (Cons x xs) then show ?case by (cases xs) auto
qed simp

definition sym_parts where
  "sym_parts rules \<equiv> (\<lambda>(f,n). (f,n,{r \<in> rules. r_sym r = (f,n)})) ` (r_sym ` rules)"

definition ps_states_cons_impl where
  "ps_states_cons_impl meps parts rules Q \<equiv> 
    let lhs_nth_in_Q = \<lambda>(n,rs). map (\<lambda>i.((\<lambda>p. {r \<in> rs . r_lhs_states r ! i \<in> p}) ` Q) - {{}}) [0 ..< n] in
    \<Union>((\<lambda>(f, nrs). ((\<lambda>rs. rhs_eps_cl_memo meps (list_inter rs)) ` (listset (lhs_nth_in_Q nrs))) - {{}}) ` parts)"

lemma ps_states_init_new:
  "ps_states_nil eps rules \<union> ps_states_cons eps rules Q = ps_states_new eps rules Q"
unfolding ps_states_nil_def ps_states_cons_def ps_states_new_def by force

lemma ps_states_nil_impl:
  "ps_states_nil eps rules = ps_states_nil_impl (memo_rtrancl eps) rules"
unfolding ps_states_nil_def ps_states_nil_impl_def ps_state_def
by (auto simp: Union_eq image_def rhs_eps_cl_memo) (force simp: r_root_def split: ta_rule.splits)+

(* TODO: cleanup this proof *)
lemma ps_states_cons_impl:
  "ps_states_cons eps rules Q =
   ps_states_cons_impl (memo_rtrancl eps) (sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}) rules Q" (is "?L = ?R")
proof standard
  let ?rhs_eps = "rhs_eps_cl_memo (memo_rtrancl eps)"
  let ?rss = "sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}"

  show "?R \<subseteq> ?L" proof standard
    fix x assume x: "x \<in> ?R"
    note this[unfolded ps_states_new_def]
    let ?lhs_nth = "\<lambda>(n,rs). map (\<lambda>i.((\<lambda>p. {r \<in> rs . r_lhs_states r ! i \<in> p}) ` Q) - {{}}) [0 ..< n]"
    from x obtain f n rs where
      x_in: "x \<in> ((\<lambda>rs. ?rhs_eps (list_inter rs)) ` listset (?lhs_nth (n,rs))) - {{}}" and
      rss: "(f, n,rs) \<in> ?rss"
    unfolding ps_states_cons_impl_def by auto
    have r_sym: "r_sym r = (case r of f qs \<rightarrow> q \<Rightarrow> (f, length qs))" for r by (cases r, simp) 
    from rss have n: "n > 0" unfolding sym_parts_def by (auto elim!: r_sym.elims[OF sym])
    with rss obtain f where rs: "rs = {r \<in> rules. r_lhs_states r \<noteq> [] \<and> r_sym r = (f,n)}"
      unfolding sym_parts_def by (auto elim!: r_sym.elims[OF sym])
    from n have r_lhs: "r_sym r = (f,n) \<Longrightarrow> r_lhs_states r \<noteq> []" for r by (auto simp: r_sym r_lhs_states_def split: ta_rule.split)
    with rs have rs: "rs = {r \<in> rules. r_sym r = (f,n)}" by blast

    from x_in obtain rsi where
      x_eq: "x = ?rhs_eps (\<Inter> (set rsi))" and rsi: "rsi \<in> listset (?lhs_nth (n,rs))"
    by (auto simp: list_inter)
    let ?ps_rules = "\<Inter> (set rsi)"
    from rsi have "\<forall>i. \<exists>p. i < n \<longrightarrow> rsi ! i = {r \<in> rules. r_sym r = (f, n) \<and> r_lhs_states r ! i \<in> p} \<and> p \<in> Q" by (auto simp: listset rs)
    with choice[OF this] obtain fps
      where fps: "\<And>i. i < n \<Longrightarrow> rsi ! i = {r \<in> rules. r_sym r = (f, n) \<and> r_lhs_states r ! i \<in> (fps i)} \<and> (fps i) \<in> Q"
    by blast

    have n_len: "n = length rsi" using rsi by (simp add: listset)

    have rsi: "rsi = map (\<lambda>i. {r \<in> rules. r_sym r = (f, n) \<and> r_lhs_states r ! i \<in> (fps i)}) [0..<n]"
      using fps unfolding n_len by (metis (no_types, lifting) atLeastLessThan_iff map_cong map_nth set_upt) 

    define ps where "ps = map fps [0 ..< n]"
    from fps have subset: "set ps \<subseteq> Q" by (auto simp: ps_def)
    from n have not_nil: "ps \<noteq> []" by (auto simp: ps_def)
    from x_in have not_empty: "x \<noteq> {}" by auto
    have "x = ps_state eps rules f ps"
    proof standard
      show "x \<subseteq> ps_state eps rules f ps" proof standard
        fix q
        assume *: "q \<in> x"
        from this obtain r where
          r: "r \<in> \<Inter> (set rsi)" and
          eps: "(r_rhs r, q) \<in> eps\<^sup>*" unfolding x_eq rhs_eps_cl_memo by auto
        with this n obtain qs qr where [simp]: "r = f qs \<rightarrow> qr" and len: "length qs = n" by (cases r) (auto simp: rsi)
        have ps: "list_all2 (\<in>) qs ps" using r len by (auto simp: list_all2_conv_all_nth rsi ps_def)
        from r have rules: "r \<in> rules"
        by (auto simp: rsi)
           (metis (no_types, lifting) length_greater_0_conv length_map n_len nth_mem r_lhs r_sym.simps rsi set_upt ta_rule.sel(2))
        from rules ps eps show "q \<in> ps_state eps rules f ps" unfolding ps_state_def by auto
      qed
      show "ps_state eps rules f ps \<subseteq> x" proof standard
        fix q
        assume *: "q \<in> ps_state eps rules f ps"
        from this obtain qs qr where "f qs \<rightarrow> qr \<in> rules" "list_all2 (\<in>) qs ps" and eps: "(qr,q) \<in> eps\<^sup>*"
          unfolding ps_state_def by auto
        then have "f qs \<rightarrow> qr \<in> \<Inter> (set rsi)" unfolding rsi by (auto simp: ps_def list_all2_conv_all_nth)
        with eps show "q \<in> x" unfolding x_eq rhs_eps_cl_memo by (auto intro: bexI[of _ "f qs \<rightarrow> qr"])
      qed
    qed
    with subset not_nil not_empty show "x \<in> ?L" by (auto simp: ps_states_cons_def)
  qed

  show "?L \<subseteq> ?R" proof standard
    fix p assume "p \<in> ?L"
    from this obtain ps f where
      ps: "set ps \<subseteq> Q" "ps \<noteq> []" and
      p: "p = ps_state eps rules f ps" and
      p_ne: "p \<noteq> {}"
      unfolding ps_states_cons_def by blast
    then have len: "length ps > 0" by blast
    define rs where "rs = {r \<in> rules. r_root r = f \<and> list_all2 (\<in>) (r_lhs_states r) ps}"
    have p_eq: "p = ?rhs_eps rs" by (force simp: p ps_state_def rhs_eps_cl_memo rs_def)
    with p_ne have rs_ne: "rs \<noteq> {}" unfolding rhs_eps_cl_memo rs_def by force
    let ?n = "length ps"
    define rsi where "rsi = map (\<lambda>i. {r \<in> rules. r_sym r = (f, ?n) \<and> r_lhs_states r ! i \<in> ps ! i}) [0..<?n]"
    have rsi: "rs = \<Inter>(set rsi)" using len
      apply (auto simp: list_all2_conv_all_nth rsi_def rs_def)
      apply (auto elim!: ballE r_sym.elims simp: r_root_def split: ta_rule.split)[4]
      by (metis atLeastLessThan_iff le0 len prod.sel(2) r_sym.simps ta_rule.exhaust_sel)
    let ?rs_part = "{r \<in> rules. r_sym r = (f, length ps)}"
    from rs_ne obtain qs q where rule: "f qs \<rightarrow> q \<in> rs" "list_all2 (\<in>) qs ps" by (auto simp: rs_def) (metis ta_rule.exhaust_sel) 
    then have rss: "(f, length ps, ?rs_part) \<in> ?rss" unfolding sym_parts_def rs_def using len
      by (auto simp: image_iff list_all2_conv_all_nth intro!: exI[of _ "f qs \<rightarrow> q"] elim!: r_sym.elims)
    define lhs_nth where "lhs_nth \<equiv> \<lambda>(n,rs :: ('a, 'b) ta_rule set). map (\<lambda>i.((\<lambda>p. {r \<in> rs . r_lhs_states r ! i \<in> p}) ` Q) - {{}}) [0 ..< n]"
    have len_lhs_nth: "length (lhs_nth (n, rs)) = n" for n rs unfolding lhs_nth_def by simp
    have "rsi \<in> listset (lhs_nth (length ps, ?rs_part))" 
      apply (simp add: lhs_nth_def image_iff rsi_def listset len_lhs_nth)
      apply (intro allI conjI impI)
      apply (rule_tac x = "ps ! i" in bexI)
      by (insert ps rule, auto simp: list_all2_conv_all_nth rs_def intro!: exI[of _ "f qs \<rightarrow> q"])
    then show "p \<in> ?R" using p_ne rss
      by (auto intro!: bexI[of _ "(f, length ps, ?rs_part)"] bexI[of _ "rsi"]
                 simp: lhs_nth_def image_iff p_eq list_inter rsi ps_states_cons_impl_def Let_def)
  qed
qed

definition ps_states_impl_ref where
  "ps_states_impl_ref eps rules \<equiv>
    let meps = memo_rtrancl eps in
    let parts = sym_parts {r \<in> rules. r_lhs_states r \<noteq> []} in
    let Qinit = ps_states_nil_impl meps rules in
    while (\<lambda>(Qold, Qnew). \<not>(Qnew \<subseteq> Qold))
      (\<lambda>(Qold, Qnew). (Qnew, Qinit \<union> ps_states_cons_impl meps parts rules Qnew))
    ({}, Qinit)"

lemma ps_states_impl_ref:
  "ps_states_impl eps rules = ps_states_impl_ref eps rules"
unfolding
ps_states_impl_def
ps_states_impl_ref_def
ps_states_nil[symmetric]
ps_states_nil_impl[symmetric]
ps_states_cons_impl[symmetric]
ps_states_init_new
Let_def
..

(* TODO: unify implementation of ps_rules and ps_states (implement latter in terms of the former?) *)

definition ps_rules_nil where
  "ps_rules_nil eps rules = {f [] \<rightarrow> q | q f. q = ps_state eps rules f [] \<and> q \<noteq> {}}"

definition ps_rules_cons where
  "ps_rules_cons eps rules Q = {f ps \<rightarrow> q | q ps f. set ps \<subseteq> Q \<and> ps \<noteq> [] \<and> q = ps_state eps rules f ps \<and> q \<noteq> {}}"

lemma ps_rules_nil_cons:
  "ps_rules eps rules Q = ps_rules_nil eps rules \<union> ps_rules_cons eps rules Q"
unfolding ps_rules_def ps_rules_nil_def ps_rules_cons_def by auto

definition ps_rules_nil_impl where
  "ps_rules_nil_impl meps rules \<equiv>
    let rsz = {r \<in> rules. r_lhs_states r = []} in
      (\<lambda>f. f [] \<rightarrow> rhs_eps_cl_memo meps {r \<in> rsz. r_root r = f}) ` (r_root ` rsz)"

lemma ps_rules_nil_impl:
  "ps_rules_nil eps rules = ps_rules_nil_impl (memo_rtrancl eps) rules" (is "?L = ?R")
proof standard
  show "?L \<subseteq> ?R" proof standard
    fix r assume *: "r \<in> ?L"
    from this obtain f where
      r: "r = f [] \<rightarrow> ps_state eps rules f []" and
      rhs: "ps_state eps rules f [] \<noteq> {}"
    by (auto simp: ps_rules_nil_def)
    with *[unfolded r] obtain q where "f [] \<rightarrow> q \<in> rules" by (auto simp: ps_state_def)
    then show "r \<in> ?R" unfolding ps_rules_nil_impl_def
    by (auto intro!: exI[of _ "f [] \<rightarrow> q"] simp: image_iff r ps_state_def rhs_eps_cl_memo)
  qed
  show "?R \<subseteq> ?L" proof standard
    fix r assume *: "r \<in> ?R"
    let ?rs = "\<lambda>f. {r \<in> rules. r_lhs_states r = [] \<and> r_root r = f}"
    let ?rhs_eps = "rhs_eps_cl_memo (memo_rtrancl eps)"
    from * obtain f where r: "r = f [] \<rightarrow> ?rhs_eps (?rs f)" and rhs: "(?rs f) \<noteq> {}"
      by (auto simp: ps_rules_nil_impl_def)
    from rhs obtain q where "f [] \<rightarrow> q \<in> rules" by auto (metis ta_rule.exhaust_sel)
    then show "r \<in> ?L"  by (auto simp: ps_rules_nil_def r rhs_eps_cl_memo ps_state_def intro!: exI[of _ f])
  qed
qed

definition ps_rules_cons_impl where
  "ps_rules_cons_impl meps parts rules Q \<equiv> 
    let lhs_nth = \<lambda>(n,rs). map
      (\<lambda>i. { x \<in> (
        (\<lambda>p. (p, {r \<in> rs . r_lhs_states r ! i \<in> p}))
        ` Q) . snd x \<noteq> {}})
      [0 ..< n] in
    \<Union>((\<lambda>(f, nrs).
      {r \<in> (
        (\<lambda>rs. f (map fst rs) \<rightarrow> rhs_eps_cl_memo meps (list_inter (map snd rs)))
        ` (listset (lhs_nth nrs)))
        . r_rhs r \<noteq> {}})
      ` parts)"

(* TODO: cleanup this proof, unify with ps_states_cons_impl *)

lemma ps_rules_cons_impl:
  "ps_rules_cons eps rules Q =
   ps_rules_cons_impl (memo_rtrancl eps) (sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}) rules Q" (is "?L = ?R")
proof
  let ?rhs_eps = "rhs_eps_cl_memo (memo_rtrancl eps)"
  let ?rss = "sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}"

  show "?R \<subseteq> ?L" proof standard
    fix x assume x: "x \<in> ?R"
    let ?rss = "sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}"
    define lhs_nth where "lhs_nth \<equiv> \<lambda>(n,rs :: ('a, 'b) ta_rule set). map
      (\<lambda>i. { x \<in> (
        (\<lambda>p. (p, {r \<in> rs . r_lhs_states r ! i \<in> p}))
        ` Q) . snd x \<noteq> {}})
      [0 ..< n]"
    from x obtain f n rs where
      x_in: "x \<in> {r \<in> (
        (\<lambda>rs. f (map fst rs) \<rightarrow> ?rhs_eps (\<Inter>r\<in>set rs. snd r))
        ` (listset (lhs_nth (n,rs))))
        . r_rhs r \<noteq> {}}" and
      rss: "(f,n,rs) \<in> ?rss"
    by (auto simp: list_inter ps_rules_cons_impl_def lhs_nth_def)
    have r_sym: "r_sym r = (case r of f qs \<rightarrow> q \<Rightarrow> (f, length qs))" for r by (cases r, simp) 
    from rss have n: "n > 0" unfolding sym_parts_def by (auto elim!: r_sym.elims[OF sym])
    with rss have rs: "rs = {r \<in> rules. r_lhs_states r \<noteq> [] \<and> r_sym r = (f,n)}"
      unfolding sym_parts_def by (auto elim!: r_sym.elims[OF sym])
    from n have r_lhs: "r_sym r = (f,n) \<Longrightarrow> r_lhs_states r \<noteq> []" for r by (auto simp: r_sym r_lhs_states_def split: ta_rule.split)
    with rs have rs: "rs = {r \<in> rules. r_sym r = (f,n)}" by blast

    from x_in obtain rsi where
      x_eq: "x = f (map fst rsi) \<rightarrow> ?rhs_eps (\<Inter>r\<in>set rsi. snd r)" and
      rsi: "rsi \<in> listset (lhs_nth (n,rs))" and
      rhs_ne: "?rhs_eps (\<Inter>r\<in>set rsi. snd r) \<noteq> {}"
    by force
    let ?ps_rules = "(\<Inter>r\<in>set rsi. snd r)"
    from rsi have
      fps: "\<And>i. i < n \<Longrightarrow> snd (rsi ! i) = {r \<in> rules. r_sym r = (f, n) \<and> r_lhs_states r ! i \<in> fst (rsi ! i)} \<and> fst (rsi ! i) \<in> Q"
    by (auto simp: listset rs lhs_nth_def)

    have n_len: "n = length rsi" using rsi by (simp add: listset lhs_nth_def)

    have rsi: "map snd rsi = map (\<lambda>i. {r \<in> rules. r_sym r = (f, n) \<and> r_lhs_states r ! i \<in> fst (rsi ! i)}) [0..<n]"
      using fps unfolding map_upt_len_conv[of snd rsi, symmetric] n_len by (intro map_cong) auto

    define ps where "ps = map fst rsi"
    from fps have subset: "set ps \<subseteq> Q" by (force simp: ps_def in_set_conv_nth n_len) 
    from n have not_nil: "ps \<noteq> []" by (auto simp: ps_def n_len)
    (*from x_in have not_empty: "x \<noteq> {}" by auto*)
    have "?rhs_eps (\<Inter>r\<in>set rsi. snd r) = ps_state eps rules f ps" (is "?L' = ?R'")
    proof standard
      show "?L' \<subseteq> ?R'" proof standard
        fix q
        assume *: "q \<in> ?L'"
        from this obtain r where
          r: "r \<in> (\<Inter> (set (map snd rsi)))" and
          eps: "(r_rhs r, q) \<in> eps\<^sup>*" unfolding rhs_eps_cl_memo by auto
        with n this obtain qs qr where [simp]: "r = f qs \<rightarrow> qr" and len: "length qs = n" by (cases r) (auto simp: rsi)
        have ps: "list_all2 (\<in>) qs ps" using r n by (auto simp: list_all2_conv_all_nth rsi ps_def len n_len)
        from r have rules: "r \<in> rules"
        by (auto simp: rsi)
           (metis (no_types, lifting) length_greater_0_conv length_map n_len nth_mem r_lhs r_sym.simps rsi set_upt ta_rule.sel(2))
        from rules ps eps show "q \<in> ?R'" unfolding ps_state_def by auto
      qed
      show "?R' \<subseteq> ?L'" proof standard
        fix q
        assume *: "q \<in> ps_state eps rules f ps"
        from this obtain qs qr where "f qs \<rightarrow> qr \<in> rules" "list_all2 (\<in>) qs ps" and eps: "(qr,q) \<in> eps\<^sup>*"
          unfolding ps_state_def by auto
        then have "f qs \<rightarrow> qr \<in> (\<Inter> (set (map snd rsi)))" unfolding rsi by (auto simp: ps_def list_all2_conv_all_nth n_len)
        with eps show "q \<in> ?L'" unfolding rhs_eps_cl_memo by (auto intro: bexI[of _ "f qs \<rightarrow> qr"])
      qed
    qed
    with subset not_nil rhs_ne show "x \<in> ?L" unfolding x_eq ps_def[symmetric] by (auto simp: ps_rules_cons_def)
  qed

  show "?L \<subseteq> ?R" proof standard
    fix r assume "r \<in> ?L"
    from this obtain ps f where
      ps: "set ps \<subseteq> Q" "ps \<noteq> []" and
      p: "r = f ps \<rightarrow> ps_state eps rules f ps" and
      p_ne: "ps_state eps rules f ps \<noteq> {}"
      unfolding ps_rules_cons_def by blast
    then have len: "length ps > 0" by blast
    define rs where "rs = {r \<in> rules. r_root r = f \<and> list_all2 (\<in>) (r_lhs_states r) ps}"
    have p_eq: "ps_state eps rules f ps = ?rhs_eps rs" by (force simp: ps_state_def rhs_eps_cl_memo rs_def)
    with p_ne have rs_ne: "rs \<noteq> {}" unfolding rhs_eps_cl_memo rs_def by force
    let ?n = "length ps"
    define rsi where "rsi = map (\<lambda>i. (ps ! i, {r \<in> rules. r_sym r = (f, ?n) \<and> r_lhs_states r ! i \<in> ps ! i})) [0..<?n]"
    have ps_rsi: "ps = map fst rsi" by (auto simp: rsi_def comp_def map_upt_len_conv[where f = id, simplified])
    have rsi: "rs = \<Inter>(set (map snd rsi))" using len
      apply (auto simp: list_all2_conv_all_nth rsi_def rs_def)
      apply (auto elim!: ballE r_sym.elims simp: r_root_def split: ta_rule.split)[4]
      by (metis atLeastLessThan_iff le0 len prod.sel(2) r_sym.simps ta_rule.exhaust_sel)
    let ?rss = "sym_parts {r \<in> rules. r_lhs_states r \<noteq> []}"
    let ?rs_part = "{r \<in> rules. r_sym r = (f, length ps)}"
    from rs_ne obtain qs q where rule: "f qs \<rightarrow> q \<in> rs" "list_all2 (\<in>) qs ps" by (auto simp: rs_def) (metis ta_rule.exhaust_sel) 
    then have rss: "(f, length ps, ?rs_part) \<in> ?rss" unfolding sym_parts_def rs_def using len
      by (auto simp: image_iff list_all2_conv_all_nth intro!: exI[of _ "f qs \<rightarrow> q"] elim!: r_sym.elims)
    define lhs_nth where "lhs_nth \<equiv> \<lambda>(n,rs :: ('a, 'b) ta_rule set). map
      (\<lambda>i. { x \<in> (
        (\<lambda>p. (p, {r \<in> rs . r_lhs_states r ! i \<in> p}))
        ` Q) . snd x \<noteq> {}})
      [0 ..< n]"
    have len_lhs_nth: "length (lhs_nth (n, rs)) = n" for n rs unfolding lhs_nth_def by simp
    have "rsi \<in> listset (lhs_nth (length ps, ?rs_part))" unfolding listset len_lhs_nth
      apply (simp add: lhs_nth_def image_iff rsi_def)
      apply (intro allI conjI impI)
      by (insert rule ps, auto simp: list_all2_conv_all_nth rs_def intro!: exI[of _ "f qs \<rightarrow> q"])
    then show "r \<in> ?R" unfolding ps_rules_cons_impl_def Let_def using p_ne
      apply (simp add: image_iff p_eq list_inter)
      apply (intro bexI[of _ "(f, length ps, ?rs_part)"])
      apply (auto intro!: bexI[of _ "rsi"])
      apply (auto simp: p ps_rsi p_eq[unfolded ps_rsi] rsi)[1]
      apply (auto simp: lhs_nth_def image_iff)[]
      by (auto simp: p p_ne rss)
  qed
qed

lemma ps_ta_impl[code]:
  "ps_ta TA = (
    let eps = ta_eps TA; rules = ta_rules TA in
    if finite eps \<and> finite rules then
      let meps = memo_rtrancl eps in
      let parts = sym_parts {r \<in> rules. r_lhs_states r \<noteq> []} in
      let Qinit = ps_states_nil_impl meps rules in
      let Q = fst (while (\<lambda>(Qold, Qnew). \<not>(Qnew \<subseteq> Qold))
                    (\<lambda>(Qold, Qnew). (Qnew, Qinit \<union> ps_states_cons_impl meps parts rules Qnew))
                  ({}, Qinit)) in
      let final = {q \<in> Q. q \<inter> ta_final TA \<noteq> {}} in
      let rules = ps_rules_nil_impl meps rules \<union> ps_rules_cons_impl meps parts rules Q in
      \<lparr>ta_final = final, ta_rules = rules, ta_eps = {} \<rparr>
    else
      ps_ta TA)"
proof (cases "finite (ta_eps TA) \<and> finite (ta_rules TA)")
  case True
    then have finite: "finite (ta_eps TA)" "finite (ta_rules TA)" by blast+
    show ?thesis unfolding
      Let_def if_P[OF True]
      ps_states_impl_ref[unfolded Let_def ps_states_impl_ref_def, symmetric]
      ps_rules_nil_impl[symmetric]
      ps_rules_cons_impl[symmetric]
      ps_rules_nil_cons[symmetric]
      ps_states_impl[OF finite, symmetric]
      ps_ta_def
      ..
   next
   case False
    show ?thesis unfolding
      Let_def
      if_not_P[OF False]
      ..
qed

end
