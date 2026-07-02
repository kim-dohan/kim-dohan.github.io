theory Tree_Automata_NF_Impl
imports
  Tree_Automata_NF
  First_Order_Terms.Option_Monad
  First_Order_Rewriting.Term_Impl
begin

hide_const Wfrec.cut

fun merge where
  "merge (Fun f ts) (Fun f' ts') = do {
     guard (f = f');
     guard (length ts = length ts');
     ts \<leftarrow> mapM (\<lambda>(t,t'). merge t t') (zip ts ts');
     Some (Fun f ts)
   }"
| "merge (Var ()) x = Some x"
| "merge x (Var ()) = Some x"

lemma merge_var[simp]: "merge x (Var ()) = Some x" by (cases x) auto

lemma merge_some: "merge s t = Some m \<longleftrightarrow> pmerge s t m"
proof (induction s t arbitrary: m rule: merge.induct)
  have map: "\<And>x y f. length x = length y \<Longrightarrow> (y = map f x) \<longleftrightarrow> (\<forall>i<length y. f (x ! i) = y ! i)"
    using map_nth_eq_conv by metis
  case 1
  then show ?case
    apply (auto elim!: mergeE intro!: merge_fun dest!: mapM_Some simp: guard_simps set_zip mapM_map map split: bind_splits)
      apply (metis option.sel)
     apply (metis option.sel)
    apply (fastforce)
    done
qed (auto elim: mergeE)

lemma pmerge_exists:
  "(\<exists>m. pmerge (Fun f ts) (Fun f' ts') m) \<longleftrightarrow> (f = f' \<and> list_all2 (\<lambda>t t'. (\<exists>m. pmerge t t' m)) ts ts')"
  (is "?L = ?R")
proof standard
  assume ?L
  from this obtain m where "pmerge (Fun f ts) (Fun f' ts') m" by blast
  then show ?R by (auto elim!: mergeE simp: list_all2_conv_all_nth)
  next
  assume ?R
  from this have "\<forall>i. \<exists>m. i < length ts \<longrightarrow>  pmerge (ts!i) (ts'!i) m" by (simp add: list_all2_conv_all_nth)
  from choice[OF this] obtain w where w: "\<And>i. i < length ts \<Longrightarrow> pmerge (ts!i) (ts'!i) (w i)" by blast
  let ?gs = "map w [0 ..< length ts]"
  from w \<open>?R\<close> show ?L by (intro exI[of _ "Fun f ?gs"]) (auto simp: list_all2_conv_all_nth intro: merge_fun)
qed

lemma merge_none: "merge s t = None \<longleftrightarrow> \<not>(\<exists>m. pmerge s t m)"
by (induction s t rule: merge.induct,
    auto elim!: mergeE intro!: merge_fun split: bind_splits
          simp: mapM_map guard_simps set_zip pmerge_exists list_all2_conv_all_nth)
    fastforce+

fun match where
  "match (Var ()) x = True"
| "match (Fun f ts) (Fun f' ts') = ((f = f') \<and> list_all2 match ts ts')"
| "match x y = False"

lemma match:
  "match a b = pmatch a b"
by (induction a b rule: match.induct) (auto elim: matchE simp: list_all2_conv_all_nth)

inductive_set merge_cl :: "('f,unit) term set \<Rightarrow> ('f,unit) term set" for T :: "('f,unit) term set" where
  init: "m \<in> T \<Longrightarrow> m \<in> merge_cl T"
| merge: "\<lbrakk>s \<in> merge_cl T; t \<in> merge_cl T; pmerge s t m\<rbrakk> \<Longrightarrow> m \<in> merge_cl T"

lemma merge_cl_increase: "T \<subseteq> merge_cl T" by (auto intro: merge_cl.init)

lemma merge_cl_mono:
  "S \<subseteq> T \<Longrightarrow> merge_cl S \<subseteq> merge_cl T"
proof standard
  fix x assume "x \<in> merge_cl S" "S \<subseteq> T"
  then show "x \<in> merge_cl T" by (induction rule: merge_cl.induct) (blast intro: init merge)+
qed

lemma merge_cl_code:
  "merge_cl S =
    (let new = Option.these ((\<lambda>(t,t'). merge t t') ` (S \<times> S)) - S in
      if new = {} then S else merge_cl (S \<union> new))"
proof -
  let ?merge = "Option.these ((\<lambda>(t,t'). merge t t') ` (S \<times> S))"
  have merge_pmerge: "?merge = {m | m s t. s \<in> S \<and> t \<in> S \<and> pmerge s t m}"
    by (auto simp: in_these_eq merge_some[symmetric]) force+
  have pmerge_refl: "pmerge s s s" for s by (induction s) (auto intro!: merge_fun)
  {
    fix m
    assume "m \<in> ?merge"
    from this obtain s t where "s \<in> S" "t \<in> S" "pmerge s t m" by (auto simp: merge_pmerge)
    moreover then have "s \<in> merge_cl S" "t \<in> merge_cl S" by (auto intro!: merge_cl.init)
    ultimately have "m \<in> merge_cl S" by (auto intro: merge_cl.merge)
  } note merge_subset = this

  show ?thesis proof (cases "?merge - S = {}")
    case True
      have "merge_cl S = S" proof - {
          fix s assume "s \<in> merge_cl S"
          then have "s \<in> S" proof (induction rule: merge_cl.induct)
            case (merge s t m)
              then have "m \<in> ?merge" by (auto simp: merge_pmerge)
              with True show ?case by blast next
          qed 
        }
        moreover {
          fix m assume "m \<in> S"
          then have "m \<in> ?merge" by (auto simp: merge_pmerge intro!: exI[of _ m] pmerge_refl)
          from merge_subset[OF this] have "m \<in> merge_cl S" .
        }
        ultimately show ?thesis by blast next
      qed
      with True show ?thesis by simp next

    case False
      have "merge_cl S = merge_cl (S \<union> (?merge - S))" (is "?L = ?R") proof standard
        show "?L \<subseteq> ?R" by (auto intro!: merge_cl_mono) next
        show "?R \<subseteq> ?L" proof standard
          fix s assume "s \<in> ?R"
          then show "s \<in> ?L" proof (induction rule: merge_cl.induct)
            case (init m)
              then have "m \<in> S \<or> m \<in> ?merge" by blast
              then show ?case proof (elim disjE)
                assume "m \<in> S"
                then show "m \<in> merge_cl S" by (auto intro!: merge_cl.init) next
                assume "m \<in> ?merge"
                from merge_subset[OF this] show "m \<in> merge_cl S" .
              qed next
            case (merge s t m)
              then show ?case by (auto intro: merge_cl.merge[of s _ t])
          qed
        qed
      qed
      with False show ?thesis by simp
  qed
qed

lemma subt_cutD:
  "t \<rhd> s \<Longrightarrow> cut t \<rhd> cut s"
by (induction rule: supt.induct) (auto intro!: supt.subt)

lemma cut_subtD:
  assumes "cut t \<rhd> s" shows "\<exists>u. t \<rhd> u \<and> cut u = s"
using assms proof (induction t)
  case (Fun f ts)
    with Fun obtain ti where ti: "ti \<in> set ts" "cut ti \<unrhd> s" by (auto elim!: Fun_supt) 
    show ?case proof (cases "cut ti = s")
      case True
        then show ?thesis using ti by (intro exI[of _ ti], simp add: cut_eq_sym) next
      case False
        with ti have "cut ti \<rhd> s" by auto
        from Fun.IH[OF ti(1) this] obtain u where "u \<lhd> ti" "cut u = s" by blast
        then show ?thesis using ti by (intro exI[of _ u], auto simp: cut_eq_sym)
    qed
qed auto

lemma cut_subtE:
  assumes "cut t \<rhd> s" obtains u where "t \<rhd> u \<and> cut u = s"
using cut_subtD[OF assms] by blast

lemma subt_merge_cl_code:
  "subt_merge_cl S = merge_cl ({Var ()} \<union> \<Union>((\<lambda>t. {s. t \<rhd> s}) ` (cut ` S)))" (is "?L = ?R")
proof standard
  show "?L \<subseteq> ?R" proof standard
    fix x assume "x \<in> ?L"
    then show "x \<in> ?R"
    by (induction rule: subt_merge_cl.induct)
       (auto dest: subt_cutD 
            intro: merge_cl.merge merge_cl_increase[THEN subsetD])
  qed
  show "?R \<subseteq> ?L" proof standard
    fix x assume "x \<in> ?R"
    then show "x \<in> ?L"
     by (induction rule: merge_cl.induct)
        (auto elim!: cut_subtE intro: subt_merge_cl.merge subt_merge_cl.subterm)
  qed
qed

definition shrinks :: "('a, unit)term \<Rightarrow> ('a, unit)term set \<Rightarrow> ('a, unit)term set" where
   "shrinks t T \<equiv> let S = {s \<in> T. match s t} in {s \<in> S. (\<forall>s' \<in> S. funs_count s' \<le> funs_count s)}"

lemma shrinks_code:
  "shrinks t T =
    (let S = {s \<in> T. match s t}; max = Max (funs_count ` S) in {s \<in> S. funs_count s = max})"
proof -
  have finite: "finite {s \<in> T. match s t}" using match_finite[of t] by (auto simp: match)
  then show ?thesis unfolding shrinks_def by (auto intro!: Max_eqI[symmetric])
qed

lemma shrinks:
  "shrinks t (subt_merge_cl T) = {s. pshrink t T s}" (is "?L = ?R")
unfolding shrinks_def pshrink_def subt_mcl_match_def by (simp add: match)

primrec generate_listset where
  "generate_listset 0 S = {[]}"
| "generate_listset (Suc n) S = set_Cons S (generate_listset n S)"

lemma generate_listset:
  "generate_listset n S \<equiv> {xs. length xs = n \<and> set xs \<subseteq> S}"
by (induction n) (auto simp: set_Cons_def length_Suc_conv)

definition "nf_rules_states_impl T sig \<equiv>
    let mcl = subt_merge_cl T;
        states = {q \<in> mcl. \<forall>t \<in> T. \<not> match (cut t) q};
        lhss = \<Union>((\<lambda>(f,n). Pair f ` (generate_listset n states)) ` sig);
        flhss = {q \<in> lhss. \<forall>t \<in> T. \<not> match (cut t) (Fun (fst q) (snd q))};
        rules = (\<lambda>(f,qs). TA_rule f qs ` (shrinks (Fun f qs) mcl)) ` flhss in
          (\<Union>rules, states)"

lemma nf_rules_impl:
  "nf_rules T sig = fst (nf_rules_states_impl T sig)"
by (auto simp: nf_rules_states_impl_def nf_rules_def nf_states_def match shrinks Let_def image_iff generate_listset)
   force

lemma nf_states_impl:
  "nf_states T = snd (nf_rules_states_impl T sig)"
unfolding nf_rules_states_impl_def nf_states_def by (simp add: Let_def match)

lemma ta_nf_code:
  "ta_nf T sig =
    (let (rules, states) = nf_rules_states_impl T sig in
      \<lparr>ta_final = states, ta_rules = rules, ta_eps = {}\<rparr>)"
by (simp add: ta_nf_def nf_rules_impl nf_states_impl[of T sig] split: prod.splits)

lemmas [code] =
  merge_cl_code
  shrinks_code
  subt_merge_cl_code
  ta_nf_code

lemmas [code_unfold] = supt_list_sound[symmetric, unfolded supt_impl]

end
