theory Tree_Automata_NF
  imports Tree_Automata
begin

text \<open>
Definitions of cut, match and merge from  "Transforming Outermost into Context-Sensitive Rewriting"
(10.2168/LMsubst_closure-6(2:5)2010, Definition 7.2)
\<close>

hide_const Wfrec.cut
abbreviation "cut \<equiv> map_vars_term (\<lambda>x. ())"
abbreviation "funs_count \<equiv> length o funs_term_list"

lemma cut_FunE:
  assumes "cut t = Fun f ts"
  obtains ts' where "t = Fun f ts'" "ts = map cut ts'"
using assms by (cases t) auto

lemma cut_VarE:
  assumes "cut t = Var ()"
  obtains x where "t = Var x"
using assms by (cases t) auto

lemmas cutE = cut_FunE cut_VarE

lemma cut_idem[simp]: "cut (cut t) = cut t" by (induction t) auto

lemma cut_idem'[simp]: "cut \<circ> cut = cut" unfolding fun_eq_iff by simp

lemma cut_eq_sym: "cut s = t \<longleftrightarrow> cut t = s" 
by (induction s arbitrary: t, auto elim!: cutE intro!: map_idI map_idI[symmetric] simp: image_iff)
   (metis cut_idem)+

inductive pmerge :: "('f, unit) term \<Rightarrow> ('f, unit) term \<Rightarrow> ('f, unit) term \<Rightarrow> bool" where
  merge_var_l[simp,intro]: "pmerge (Var ()) t t"
| merge_var_r[simp,intro]: "pmerge t (Var ()) t"
| merge_fun: "\<lbrakk>length fs = length gs; length gs = length hs;
                \<And>i. i < length fs \<Longrightarrow> pmerge (fs!i) (gs!i) (hs!i)\<rbrakk>
                  \<Longrightarrow> pmerge (Fun f fs) (Fun f gs) (Fun f hs)"

lemma mergeD1:
  "pmerge t (Var ()) m \<Longrightarrow> t = m"
  "pmerge (Var ()) t m \<Longrightarrow> t = m"
using pmerge.cases by blast+

lemma mergeE2:
  assumes "pmerge (Fun f fs) (Fun g gs) m"
  obtains hs where
    "m = Fun f hs" "f = g" "length fs = length gs" "length gs = length hs"
    "\<And>i. i < length fs \<Longrightarrow> pmerge (fs!i) (gs!i) (hs!i)"
  using pmerge.cases[OF assms] by auto

lemma mergeE3:
  "pmerge (Fun f fs) (Fun g gs) (Fun h hs) \<Longrightarrow>
    (\<lbrakk>length fs = length gs; length gs = length hs; f = g; g = h; 
      (\<And>i. i < length fs \<Longrightarrow> pmerge (fs!i) (gs!i) (hs!i))\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
using pmerge.cases by blast

lemmas mergeE = mergeD1[elim_format] mergeE2 mergeE3

inductive pmatch :: "('f, unit) term \<Rightarrow> ('f, unit) term \<Rightarrow> bool" where
  match_var[simp,intro]: "pmatch (Var ()) t"
| match_fun[intro]: "list_all2 pmatch rs ts \<Longrightarrow> pmatch (Fun f rs) (Fun f ts)"

lemma matchE1:
  assumes "pmatch (Fun f ts) t"
  obtains ts' where "t = Fun f ts'" "list_all2 pmatch ts ts'"
using assms by (auto simp: pmatch.simps)

lemma matchD2:
  "pmatch t (Var ()) \<Longrightarrow> t = Var ()"
  "pmatch (Fun f ts) (Fun g ts') \<Longrightarrow> f = g \<and> list_all2 pmatch ts ts'"
by (auto simp: pmatch.simps)

lemmas matchE = matchE1 matchD2[elim_format]

lemma match_refl:
  "pmatch t t"
by (induction t, auto simp: list_all2_same)

lemma match_trans:
  assumes "pmatch r s"
      and "pmatch s t"
    shows "pmatch r t"
using assms by
(induction r s arbitrary: t rule: pmatch.induct)
(auto elim: matchE intro: list_all2_trans[of "\<lambda>x y. pmatch x y \<and> (\<forall>z. pmatch y z \<longrightarrow> pmatch x z)"])

lemma match_antisym:
  assumes "pmatch s t"
      and "pmatch t s"
    shows "s = t"
using assms by
(induction s t rule: pmatch.induct)
(auto elim: matchE intro: list_all2_antisym[of "(\<lambda>x y. pmatch x y \<and> (pmatch y x \<longrightarrow> x = y))"])

lemma match_size:
  assumes "pmatch s t"
    shows "size s \<le> size t"
using assms proof (induction s t rule: pmatch.induct)
  case (match_var t)
    then show ?case by (cases t, simp_all)
qed (simp add: list_all2_conv_all_nth size_list_pointwise2)

lemma match_funs_count:
  assumes "pmatch s t"
    shows "funs_count s \<le> funs_count t"
using assms proof (induction s t rule: pmatch.induct)
  case (match_var t)
    then show ?case by (cases t, simp_all add: funs_term_list.simps)
  next
  case (match_fun ss ts f)
    then have "length ss = length ts" and
          "list_all2 (\<lambda>s t. funs_count s \<le> funs_count t) ss ts"
            by (simp_all add: list_all2_conv_all_nth)
    then show ?case by (induction rule: list_induct2, simp_all add: funs_term_list.simps)
qed

lemma match_funs_count_strict:
  assumes "pmatch s t" and "s \<noteq> t"
    shows "funs_count s < funs_count t"
using assms proof (induction s t rule: pmatch.induct)
  case (match_var t)
    then show ?case by (cases t, simp_all add: funs_term_list.simps)
  next
  case (match_fun ss ts f)
    then have "length ss = length ts"
          "list_all2 (\<lambda>s t. funs_count s \<le> funs_count t) ss ts"
          "list_all2 (\<lambda>s t. s \<noteq> t \<longrightarrow> funs_count s < funs_count t) ss ts"
          "ss \<noteq> ts" by (auto simp: list_all2_conv_all_nth match_funs_count)
    then show ?case proof (induction rule: list_induct2, simp)
      case (Cons x xs y ys)
        then show ?case proof (cases "xs = ys")
          case True
            with Cons have "x \<noteq> y" by simp
            with Cons True show ?thesis by (simp add: funs_term_list.simps)
        qed (simp add: funs_term_list.simps)
    qed
qed

(* merge is an upper bound w.r.t match *)
lemma merge_match:
  assumes "pmerge s t m"
    shows "pmatch s m \<and> pmatch t m"
using assms proof (induction s t m rule: pmerge.induct)
  case (merge_fun fs gs hs f)
    then have "list_all2 pmatch fs hs"
      and "list_all2 pmatch gs hs" using list_all2_all_nthI by force+
    then show ?case by auto
qed (simp_all add: match_refl)

lemma merge_unique:
  "(\<exists>m. pmerge s t m) \<longleftrightarrow> (\<exists>!m. pmerge s t m)"
proof
  assume "\<exists>m. pmerge s t m"
  from this obtain m where "pmerge s t m" ..
  then show "\<exists>!m. pmerge s t m"
    by (rule ex1I, induction rule: pmerge.induct) (auto elim!: mergeE intro: nth_equalityI)
qed blast

(* merge is the least upper bound w.r.t match *)
lemma match_merge:
  assumes "pmatch s b" and "pmatch t b"
  shows "\<exists>m. pmerge s t m \<and> pmatch m b"
using assms proof (induction b arbitrary: s t rule: term.induct)
  case (Var x)
    then have st: "s = Var ()" "t = Var()" by (auto elim: matchE)
    show ?case unfolding st by (intro exI[of _ "Var ()"], simp)
  next
  case (Fun f fs)
    then show ?case proof (cases s, intro exI[of _ t], simp, cases t, intro exI[of _ s], simp, goal_cases)
      case prems: (1 _ ss _ ts)
        with Fun have st: "s = Fun f ss" "t = Fun f ts"
          "list_all2 pmatch ss fs"
          "list_all2 pmatch ts fs" by (auto elim: matchE)
        then have len: "length ss = length fs" "length fs = length ts" using list_all2_lengthD by force+
        {
          fix i assume i: "i < length fs"
          then have "fs ! i \<in> set fs" by simp
          moreover from i st have "pmatch (ss!i) (fs!i)" using list_all2_nthD2 by auto
          moreover from i st have "pmatch (ts!i) (fs!i)" using list_all2_nthD2 by auto
          ultimately have "\<exists>m. pmerge (ss!i) (ts!i) m \<and> pmatch m (fs!i)" by (rule Fun.IH)
        }
        then have "\<forall>i. \<exists>m. i < length fs \<longrightarrow> pmerge (ss!i) (ts!i) m \<and> pmatch m (fs!i)" by blast
        from choice[OF this] obtain mf where mf:
          "\<And>i. i < length fs \<Longrightarrow> pmerge (ss!i) (ts!i) (mf i) \<and> pmatch (mf i) (fs!i)" by blast
        let ?ms = "map mf [0 ..< length fs]"
        have "pmerge (Fun f ss) (Fun f ts) (Fun f ?ms)" by (intro merge_fun, insert mf, simp_all add: len)
        moreover have "pmatch (Fun f ?ms) (Fun f fs)" using mf by (auto elim: matchE intro!: list_all2_all_nthI)
        ultimately show ?thesis unfolding st by blast
    qed
qed

lemma match_merge_unique:
  assumes "pmatch s b" and "pmatch t b"
  shows "\<exists>!m. pmerge s t m \<and> pmatch m b"
using merge_unique match_merge[OF assms] by blast 

lemma match_finite:
  shows "finite {t . pmatch t s}"
proof (induction s)
  case (Var x)
    have s: "{t. pmatch t (Var x)} = {Var ()}"  by (auto elim: matchE)
    show ?case unfolding s by simp
  next
  case (Fun f ts)
    let ?args = "\<Union>{ms | ta ms. ms = {t.  pmatch t ta } \<and> ta \<in> set ts}"
    let ?argls = "{ts'. set ts' \<subseteq> ?args \<and> length ts' = length ts}"
    let ?funs = "Fun f ` ?argls \<union> {Var()}"
    have "finite (set ts)" by simp
    with Fun have "finite ?args" by (intro finite_Union, auto)
    then have "finite ?funs" using finite_lists_length_eq by auto
    moreover have "{t. pmatch t (Fun f ts)} \<subseteq> ?funs"
    proof
      fix t' assume "t' \<in> {t. pmatch t (Fun f ts)}"
      then have *: "pmatch t' (Fun f ts)" by simp
      show "t' \<in> ?funs"
      proof (cases "t' = Var()")
        case False
          with * obtain ts' where t': "t' = Fun f ts'" and all: "list_all2 pmatch ts' ts" by (cases t', auto)
          have "set ts' \<subseteq> ?args"
          proof
            fix x' assume "x' \<in> set ts'"
            from all this obtain x where "x \<in> set ts" "pmatch x' x" by (induction, auto)
            then show "x' \<in> ?args" by auto
          qed
          moreover from all have "length ts' = length ts" using list_all2_lengthD by auto
          ultimately show ?thesis unfolding t' by simp
      qed simp
    qed
    ultimately show ?case using finite_subset by auto
qed

lemma match_merge_bound:
  assumes "pmerge s t m"
      and "pmatch s b" "pmatch t b"
    shows "pmatch m b"
using assms proof (induction s t m arbitrary: b rule: pmerge.induct)
  case (merge_fun fs gs hs f)
    from this obtain bs where b: "b = Fun f bs"
    and all_fs: "list_all2 pmatch fs bs"
    and all_gs: "list_all2 pmatch gs bs" by (auto elim!: matchE)
    then have len: "length gs = length bs" using list_all2_lengthD by auto
    {
      fix i assume i: "i < length fs"
      moreover then have "pmatch (fs!i) (bs!i)" using list_all2_nthD[OF all_fs] by blast
      moreover from i have "pmatch (gs!i) (bs!i)" using list_all2_nthD[OF all_gs] by (simp add: merge_fun(1))
      ultimately have "pmatch (hs ! i) (bs ! i)" by (rule merge_fun.IH)
    }
    then have "list_all2 pmatch hs bs" by (simp add: list_all2_conv_all_nth merge_fun(1,2) len[symmetric])
    then show ?case by (auto simp: b)
qed simp


text \<open>
Domain of the algebra \<A>, as in Definition 7.3 of the mentioned paper.
\<close>

inductive_set subt_merge_cl :: "('f,'v) term set \<Rightarrow> ('f,unit) term set" for T :: "('f,'v) term set" where
  bottom[intro,simp]: "Var () \<in> subt_merge_cl T"
| subterm: "\<lbrakk>t \<in> T; s \<lhd> t; s' = cut s\<rbrakk> \<Longrightarrow> s' \<in> subt_merge_cl T"
| merge: "\<lbrakk>s \<in> subt_merge_cl T; t \<in> subt_merge_cl T; pmerge s t m\<rbrakk> \<Longrightarrow> m \<in> subt_merge_cl T"

definition "subt_mcl_match b T \<equiv> {t \<in> subt_merge_cl T. pmatch t b}"

text \<open>
The function shrink, as defined in the paper, but restricted to @{const subt_mcl_match} so that
it is total.
\<close>

definition pshrink where
  "pshrink s T t \<equiv> t \<in> subt_mcl_match s T \<and> (\<forall>t' \<in> subt_mcl_match s T. funs_count t' \<le> funs_count t)"
  
lemma ms_not_empty:
  shows "subt_mcl_match b T \<noteq> {}"
unfolding ex_in_conv[symmetric] by (rule exI[of _ "Var ()"], simp add: subt_mcl_match_def)

lemma ms_finite:
  shows "finite (subt_mcl_match b T)"
proof -
  have "subt_mcl_match b T \<subseteq> {t. pmatch t b}" by (auto simp: subt_mcl_match_def)
  then show ?thesis by (rule finite_subset[OF _ match_finite])
qed

lemma ms_merge_closed:
  assumes "r \<in> subt_mcl_match b T" and "s \<in> subt_mcl_match b T"
    shows "\<exists>t. pmerge r s t \<and> t \<in> subt_mcl_match b T \<and> pmatch r t \<and> pmatch s t"
proof -
  from assms have car: "r \<in> subt_merge_cl T" "s \<in> subt_merge_cl T"
            and match: "pmatch r b" "pmatch s b" by (auto simp: subt_mcl_match_def)
  from match_merge[OF match] obtain m where m: "pmerge r s m" "pmatch m b" by blast
  with car have "m \<in> subt_merge_cl T" by (auto intro: merge)
  with merge_match[OF m(1)] m show ?thesis unfolding subt_mcl_match_def by blast
qed

lemma pshrink_exists:
  "\<exists>t. pshrink s T t"
proof -
  note ms_finite[of s T]
  moreover note ms_not_empty[of s T]
  ultimately show ?thesis unfolding pshrink_def
  proof (induction rule: finite_induct)
    case (insert x xs)
      then show ?case proof (cases "xs = {}")
        case False
          with insert obtain x' where x': "x' \<in> xs"
            "\<forall>t' \<in> xs. funs_count t' \<le> funs_count x'" by blast
          then show ?thesis proof (cases "funs_count x \<le> funs_count x'")
            case True
              with x' show ?thesis by (intro exI[of _ x'], auto)
            next
            case False
              with x' show ?thesis by (intro exI[of _ x], auto)
          qed
      qed simp
  qed simp
qed

lemma pshrink_unique:
  assumes "pshrink s T t"
      and "pshrink s T t'"
    shows "t = t'"
proof (rule ccontr)
  from assms have
    t'_max: "\<forall>v \<in> subt_mcl_match s T. funs_count v \<le> funs_count t'" and
    t_max: "\<forall>v \<in> subt_mcl_match s T. funs_count v \<le> funs_count t" unfolding pshrink_def by blast+  
  assume *: "t \<noteq> t'"
  from ms_merge_closed assms obtain b where 
    b: "b \<in> subt_mcl_match s T" and t': "pmatch t' b" and t: "pmatch t b"
    unfolding pshrink_def by blast
  show False proof (cases "b = t")
    case True
      with * have "t' \<noteq> b" by blast
      from match_funs_count_strict[OF t' this] have "funs_count t' < funs_count b" .
      with t'_max b show False by auto
    next
    case False
      with * have "t \<noteq> b" by blast
      from match_funs_count_strict[OF t this] have "funs_count t < funs_count b" .
      with t_max b show False by auto
  qed
qed

lemma pshrink_welldef:
  "\<exists>!t. pshrink s T t"
using pshrink_exists pshrink_unique by blast

lemma shrink_not_match:
  assumes nmatch: "\<not> pmatch r s"
      and shrink: "pshrink s T t"
    shows "\<not> pmatch r t"
proof
  assume "pmatch r t"
  moreover from shrink have "pmatch t s" by (auto simp: pshrink_def subt_mcl_match_def)
  ultimately have "pmatch r s" by (rule match_trans)
  then show False using nmatch by blast
qed

lemma shrink_match:
  assumes s: "s \<in> subt_merge_cl T" "pmatch s l"
      and shrink: "pshrink l T t"
    shows "pmatch s t"
proof -
  from s have s: "s \<in> subt_mcl_match l T" by (auto simp: subt_mcl_match_def)
  from shrink have t: "t \<in> subt_mcl_match l T" by (auto simp: subt_mcl_match_def pshrink_def)
  from ms_merge_closed[OF s t] obtain b where 
    b: "b \<in> subt_mcl_match l T" and bs: "pmatch s b" and bt: "pmatch t b"
      unfolding pshrink_def by blast
  from bt have "funs_count t \<le> funs_count b" using match_funs_count by simp
  with shrink b have "pshrink l T b" unfolding pshrink_def by auto
  from pshrink_unique[OF shrink this] have "b = t" by simp
  with bs show ?thesis by simp
qed

text \<open>
Definitions adapted from "Sequentiality, Monadic Second-Order Logic and Tree Automata" (10.1006/inco.1999.2838, page 13-14). 
Note: subt_merge_cl (lhss \<R>) = cut ` S(\<R>)
\<close>
   
definition "nf_states T \<equiv> {t \<in> subt_merge_cl T. \<forall>t' \<in> T. \<not> pmatch (cut t') t}"

text \<open>
The set of rules S1, as defined in the paper (page 14).
Rules S2 and S3 are only required for building a complete automaton.
\<close>

definition nf_rules where
  "nf_rules T sig \<equiv>
    {TA_rule f qs q | f qs q.
      set qs \<subseteq> nf_states T \<and>
      pshrink (Fun f qs) T q \<and>
      (f, length qs) \<in> sig \<and>
      (\<forall>t' \<in> T. \<not> pmatch (cut t') (Fun f qs))}"

definition ta_nf where
  "ta_nf T sig \<equiv> \<lparr>ta_final = nf_states T, ta_rules = nf_rules T sig, ta_eps = {}\<rparr>"

lemma ta_nf_det:
  shows "ta_det (ta_nf T sig)"
unfolding ta_det_def ta_nf_def nf_rules_def using pshrink_unique by auto

lemma ta_nf_sig:
  shows "ta_syms (ta_nf T sig) \<subseteq> sig"
unfolding ta_syms_def ta_nf_def nf_rules_def by auto

lemma nf_rules_welldef:
  assumes "(f qs \<rightarrow> q) \<in> nf_rules T sig"
    shows "q \<in> nf_states T"
proof -
  from assms have nmatch: "\<forall>t \<in> T. \<not> pmatch (cut t) (Fun f qs)" and
                  shrink: "pshrink (Fun f qs) T q" by (auto simp: nf_rules_def)
  from shrink_not_match[OF _ shrink] nmatch have
    "\<forall>t \<in> T. \<not> pmatch (cut t) q" by blast
  moreover from shrink have "q \<in> subt_merge_cl T" by (auto simp: pshrink_def subt_mcl_match_def)
  ultimately show ?thesis by (simp add: nf_states_def)
qed

lemma ta_nf_welldef:
  assumes ground: "ground t"
      and res: "q \<in> ta_res (ta_nf T sig) (adapt_vars t)"
    shows "q \<in> nf_states T"
using ground proof (cases t)
  case (Fun f ts)
    with res nf_rules_welldef show ?thesis by (auto simp: ta_nf_def)
qed simp

lemma match_eq_weak_match:
  shows "weak_match s t \<longleftrightarrow> pmatch t s"
proof
  show "pmatch t s \<Longrightarrow> weak_match s t"
    by (induction rule: pmatch.induct, simp_all add: list_all2_conv_all_nth)
  show "weak_match s t \<Longrightarrow> pmatch t s"
  proof (induction t arbitrary: s)
    case (Fun f ts)
      from this(2) obtain us where s: "s = Fun f us" by (cases s, simp_all)
      with Fun(2) have "length ts = length us" by simp
      moreover {
        fix i assume "i < length ts"
        moreover with Fun(2)[unfolded s] have "weak_match (us!i) (ts!i)" by simp
        ultimately have "pmatch (ts!i) (us!i)" using Fun.IH by simp
      }
      ultimately have "list_all2 pmatch ts us" by (auto simp: list_all2_conv_all_nth)
      then show ?case unfolding s by (auto elim: matchE)
  qed simp
qed

lemma instance_match:
  assumes "t \<cdot> \<sigma> = t'"
    shows "pmatch (cut t) (cut t')"
using assms proof (induction t arbitrary: t' \<sigma>)
  case (Fun f ts)
    then show ?case proof (cases t')
      case (Fun f' ts')
        with Fun.prems have f: "f = f'" by simp
        note prems = Fun.prems[unfolded Fun this] and IH = Fun.IH[unfolded Fun this]
        {
          fix i assume i: "i < length ts"
          moreover with prems have "(ts!i) \<cdot> \<sigma> = (ts'!i)" by auto
          ultimately have "pmatch (cut (ts!i)) (cut (ts'!i))" using Fun.IH by simp
        }
        moreover with prems have "length ts = length ts'" by auto
        ultimately show ?thesis by (auto simp: Fun f pmatch.simps intro: list_all2_all_nthI)
    qed simp
qed simp

lemma instance_match':
  assumes "t \<cdot> \<sigma> = t'"
    shows "pmatch (cut t) t'"
using assms proof (induction t arbitrary: t' \<sigma>)
  case (Fun f ts)
    then show ?case proof (cases t')
      case (Fun f' ts')
        with Fun.prems have f: "f = f'" by simp
        note prems = Fun.prems[unfolded Fun this] and IH = Fun.IH[unfolded Fun this]
        {
          fix i assume i: "i < length ts"
          moreover with prems have "(ts!i) \<cdot> \<sigma> = (ts'!i)" by auto
          ultimately have "pmatch (cut (ts!i)) (ts'!i)" using Fun.IH by simp
        }
        moreover with prems have "length ts = length ts'" by auto
        ultimately show ?thesis by (auto simp: Fun f pmatch.simps intro: list_all2_all_nthI)
    qed simp
qed simp
            
lemma match_instance:
  assumes match: "pmatch (cut t) t'"
      and linear: "linear_term t"
    shows "\<exists>\<sigma>. t \<cdot> \<sigma> = t'"
using assms proof -
  from match have weak: "weak_match t' (cut t)" unfolding match_eq_weak_match .
  have "cut t = t \<cdot> (\<lambda>x. Var ())" using map_vars_term_as_subst by blast 
  from linear_weak_match[OF linear weak this] show ?thesis by blast
qed

lemma ll_match_instance:
  assumes "linear_term t"
    shows "(\<exists>\<sigma>. t \<cdot> \<sigma> = s) \<longleftrightarrow> (pmatch (cut t) s)"
using match_instance[OF _ assms] instance_match' by blast

lemma var_nf_reachable:
  assumes "Var x \<in> T"
    shows "ta_reachable (ta_nf T sig) = {}"
proof -
  have "\<And>t. pmatch (cut (Var x)) t" by simp
  with assms have "nf_rules T sig = {}" unfolding nf_rules_def by blast
  then show ?thesis by (simp add: ta_nf_def)
qed

lemma var_nf_lang:
  assumes "Var x \<in> T"
    shows "ta_lang (ta_nf T sig) = {}"
using var_nf_reachable[OF assms] unfolding ta_reachable_def ta_lang_def by auto 

lemma ta_nf_res_match_lower:
  assumes "ground t"
      and "q \<in> ta_res (ta_nf T sig) (adapt_vars t)"
    shows "pmatch q (adapt_vars t)"
using assms proof (induction t arbitrary: q)
  case (Fun f ts)
    from Fun.prems obtain qs where
      rule: "(f qs \<rightarrow> q) \<in> ta_rules (ta_nf T sig)" and
      len: "length qs = length ts" and
      res: "\<And>i. i<length ts \<Longrightarrow> qs ! i \<in> ta_res (ta_nf T sig) (adapt_vars (ts ! i))" unfolding ta_nf_def by auto
    {
      fix i assume i: "i < length ts"
      then have "pmatch (qs!i) (adapt_vars (ts!i))" using Fun.IH Fun.prems(1) res by simp
    }
    with len have match: "pmatch (Fun f qs) (adapt_vars (Fun f ts))" by (auto elim: matchE intro!: list_all2_all_nthI)
    from rule have "pshrink (Fun f qs) T q" unfolding ta_nf_def nf_rules_def by simp
    then have "pmatch q (Fun f qs)" unfolding pshrink_def subt_mcl_match_def by auto
    from match_trans[OF this match] show ?case .
qed simp

text \<open>
Main lemma for soundness, a similar lemma is used in the proof of Theorem 7.7 (ii) of the LMsubst_closure paper
\<close>

(* TODO: cleanup match/cut/adapt mess *)
lemma ta_nf_res_match_upper:
  defines [simp]: "adapt_cut \<equiv> map_vars_term (\<lambda>x. Var ())"
  assumes "l \<in> T" and "s \<lhd> l" and "pmatch (cut s) m"
      and "t \<in> ta_res (ta_nf T sig) (adapt_cut m)"
    shows "pmatch (cut s) t"
using assms proof (induction s arbitrary: t m, simp)
  case (Fun f ss)
    note in_t = Fun.prems(1) and subt = Fun.prems(2) and match = Fun.prems(3) and res = Fun.prems(4)
    from match obtain ms where m: "m = Fun f ms" "length ms = length ss"
      by (auto elim!: matchE dest: list_all2_lengthD)
    from res[unfolded m] obtain qs where
      rule: "(f qs \<rightarrow> t) \<in> nf_rules T sig" and
      len: "length qs = length ms" and
      res: "\<And>i. i<length ms \<Longrightarrow>  qs ! i \<in> ta_res (ta_nf T sig) (adapt_cut (ms ! i))" by (auto simp: ta_nf_def)
    let ?l = "Fun f (map cut ss)" and ?q = "Fun f qs"
    {
      fix i assume i: "i < length ss"
      with subt have subt: "(ss!i) \<lhd> l" using nth_mem subterm.less_trans by blast
      from match[unfolded m] i have match:
        "pmatch (cut (ss!i)) (ms!i)" by (auto elim!: matchE simp: list_all2_conv_all_nth)
      have "pmatch (cut (ss!i)) (qs!i)"
        using Fun.hyps(1)[OF _ Fun.hyps(2) in_t subt match res[unfolded m, OF i]] i by simp
    }
    with len[unfolded m] have match: "pmatch ?l ?q" by (auto elim: matchE intro!: list_all2_all_nthI)
    from rule[unfolded nf_rules_def] have shrink: "pshrink ?q T t" by simp
    from subt in_t have "?l \<in> subt_merge_cl T" by (intro subterm[of l], auto)
    from shrink_match[OF this match shrink] show ?case by simp
qed

lemma adapt_cut_adapt:
  assumes "ground t"
    shows "map_vars_term (\<lambda>x. Var ()) (adapt_vars (t)) = adapt_vars (t)"
using assms by (induction t, simp_all)

(* TODO: cleanup match/cut/adapt mess *)
lemma ta_nf_sound: 
  assumes ground: "ground t"
      and lhs: "l \<in> T" and inst: "l\<cdot>\<sigma> = t"
    shows "ta_res (ta_nf T sig) (adapt_vars t) = {}"
proof (cases l)
  case (Var x)
    from var_nf_reachable[OF lhs[unfolded this]] ground show ?thesis by (auto simp: ta_reachable_def)
  next
  from ground have adc: "cut t = adapt_vars t" by (induction t) (simp_all add: adapt_vars_def)
  case (Fun f ls)
    with inst obtain ts where t: "t = Fun f ts" by simp
    with Fun inst have len_ts: "length ls = length ts" by auto
    from Fun have subt: "\<And>i. i < length ls \<Longrightarrow> (ls!i) \<lhd> l" by simp
    from len_ts instance_match[OF inst, unfolded adc, unfolded t Fun]
      have match: "\<And>i. i < length ls \<Longrightarrow> pmatch (cut (ls!i)) (adapt_vars (ts!i))"
    by (auto elim: matchE simp: list_all2_conv_all_nth)
    show ?thesis unfolding t proof (rule equals0I)
      fix q
      assume "q \<in> ta_res (ta_nf T sig) (adapt_vars (Fun f ts))"
      thm this[simplified]
      from this obtain qs where
        rule: "(f qs \<rightarrow> q) \<in> nf_rules T sig" and
        len_qs: "length ts = length qs" and
        res: "\<And>i. i<length ts \<Longrightarrow>  qs ! i \<in> ta_res (ta_nf T sig) (adapt_vars (ts!i))" by (auto simp: ta_nf_def)
      note len = len_ts[unfolded len_qs]
      moreover {
        fix i assume i: "i < length qs"
        with ground have ground: "ground (ts!i)" by (auto simp: len_qs t)
        note prems[unfolded len, OF i] = subt match
        note ta_nf_res_match_upper[OF lhs prems, unfolded adapt_cut_adapt[OF ground], OF res, unfolded len_qs, OF i]
        then have "pmatch (cut (ls ! i)) (qs ! i)" .
      }
      ultimately have "pmatch (cut l) (Fun f qs)" by (auto simp: Fun pmatch.simps intro: list_all2_all_nthI)
      with lhs have "(f qs \<rightarrow> q) \<notin> nf_rules T sig" unfolding nf_rules_def by blast
      then show False using rule by blast
    qed
qed

lemma ta_nf_lang_sound:
  assumes "l \<in> T"
    shows "C\<langle>l\<cdot>\<sigma>\<rangle> \<notin> ta_lang (ta_nf T sig)"
proof (rule ccontr, simp)
  assume *: "C\<langle>l\<cdot>\<sigma>\<rangle> \<in> ta_lang (ta_nf T sig)"
  then have "ground (C\<langle>l\<cdot>\<sigma>\<rangle>)" unfolding ta_lang_def by force
  then have "ground (l\<cdot>\<sigma>)" by simp
  from ta_nf_sound[OF this assms refl] have res: "ta_res (ta_nf T sig) (adapt_vars (l \<cdot> \<sigma>)) = {}" .
  from ta_langE2 * obtain q where "q \<in> ta_res (ta_nf T sig) (adapt_vars (C\<langle>l\<cdot>\<sigma>\<rangle>))" by blast
  with ta_res_ctxt_decompose[OF this[unfolded adapt_vars_ctxt]] res show False by blast
qed

lemma ta_nf_complete: 
  assumes "ground t" and "funas_term t \<subseteq> sig"
      and "\<And>l s. l \<in> T \<Longrightarrow> s \<unlhd> t \<Longrightarrow> \<not> pmatch (cut l) (adapt_vars s)"
    shows "\<exists>q. q \<in> ta_res (ta_nf T sig) (adapt_vars t)"
using assms proof (induction t)
  case (Fun f ts)
    note ground = Fun.prems(1) and sig = Fun.prems(2) and nf = Fun.prems(3)
    let ?res = "\<lambda>q i. q \<in> ta_res (ta_nf T sig) (adapt_vars (ts!i)) \<and>
                      q \<in> nf_states T \<and> pmatch q (adapt_vars (ts ! i))"
    {
      fix i assume i: "i < length ts"
      moreover with ground have ground: "ground (ts!i)" by simp
      moreover from i sig have "funas_term (ts!i) \<subseteq> sig" using nth_mem by auto
      moreover {
        fix l s
        assume l: "l \<in> T" and s: "(ts!i) \<unrhd> s"
        from arg_subteq[OF nth_mem[OF i]] s have "Fun f ts \<unrhd> s" using supteq_trans by blast
        from nf[OF l this] have "\<not> pmatch (cut l) (adapt_vars s)" .
      }
      ultimately have res: "\<exists>q. q \<in> ta_res (ta_nf T sig) (adapt_vars (ts!i))" using Fun.IH by simp
      with ta_nf_welldef[OF ground] ta_nf_res_match_lower[OF ground] have "\<exists>q. ?res q i" by blast
    }
    then have "\<forall>i. \<exists>q. i < length ts \<longrightarrow> ?res q i" by blast
    with choice[OF this] obtain qf where qf: "\<And>i. i < length ts \<Longrightarrow> ?res (qf i) i" by blast
    let ?qt = "map qf [0 ..< length ts]"
    from qf have "set ?qt \<subseteq> nf_states T" by auto
    moreover {
      fix l
      assume l: "l \<in> T"
      {
        assume "pmatch (cut l) (Fun f ?qt)"
        moreover from qf have "pmatch (Fun f ?qt) (adapt_vars (Fun f ts))" by (auto simp: pmatch.simps intro: list_all2_all_nthI)
        ultimately have "pmatch (cut l) (adapt_vars (Fun f ts))" using match_trans by blast
        with nf[OF l, of "Fun f ts"] have False by blast
      }
      then have "\<not> pmatch (cut l) (Fun f ?qt)" by blast
    }
    moreover note sig pshrink_exists
    ultimately obtain q where "(f ?qt \<rightarrow> q) \<in> nf_rules T sig" unfolding nf_rules_def by force
    with qf have "q \<in> ta_res (ta_nf T sig) (adapt_vars (Fun f ts))" unfolding ta_nf_def by auto
    then show ?case by blast
qed simp

lemma ta_nf_lang_complete:
  assumes ground: "ground t" and sig: "funas_term t \<subseteq> sig"
      and linear: "\<forall>l \<in> T. linear_term l"
      and nf: "\<And>C \<sigma> l. l \<in> T \<Longrightarrow> C\<langle>l\<cdot>\<sigma>\<rangle> \<noteq> t"
    shows "t \<in> ta_lang (ta_nf T sig)"
proof -
  {
    fix l s
    assume l: "l \<in> T" and s: "s \<unlhd> t"
    with l linear have linear: "linear_term l" by blast 
    from supteq_ctxtE[OF s] obtain C where t: "t = C\<langle>s\<rangle>" by blast
    with nf[OF l, of C] have ninst: "\<And>\<sigma>. l \<cdot> \<sigma> \<noteq> s" by simp
    have "\<not> pmatch (cut l) (adapt_vars s)" proof (rule ccontr, simp)
      assume "pmatch (cut l) (adapt_vars s)"
      from match_instance[OF this linear] obtain \<sigma> where "l \<cdot> \<sigma> = s"
        by (metis t adapt_vars_adapt_vars adapt_vars_subst ground ground_ctxt_apply)
      with ninst show False by blast
    qed
  }
  note ta_nf_complete[OF ground sig] this
  from this obtain q where "q \<in> ta_res (ta_nf T sig) (adapt_vars t)" by metis
  moreover with ta_nf_welldef[OF ground] have "q \<in> nf_states T" by blast
  ultimately show ?thesis by (intro ta_langI2[OF ground], simp add: ta_nf_def)
qed

lemma ta_nf_eq_ground_nf:
  assumes "left_linear_trs R"
  shows "ta_lang (ta_nf (lhss R) sig) = {t \<in> NF_trs R. ground t \<and> funas_term t \<subseteq> sig}" (is "?lhs = ?rhs")
proof
  let ?T = "lhss R"
  from assms have linear: "\<forall>l\<in>?T. linear_term l" unfolding left_linear_trs_def by auto
  show "?rhs \<subseteq> ?lhs"
  proof
    fix t assume "t \<in> ?rhs"
    then have ground: "ground t" and sig: "funas_term t \<subseteq> sig" and nf: "t \<in> NF_trs R" by auto
    from nf have "t \<in> NF_terms ?T" by simp
    with NF_ctxt_subst[of ?T] have "\<And>C \<sigma> l. l \<in> ?T \<Longrightarrow> C\<langle>l\<cdot>\<sigma>\<rangle> \<noteq> t" by blast
    with ta_nf_lang_complete[OF ground sig linear] show "t \<in> ?lhs" by blast
  qed
  show "?lhs \<subseteq> ?rhs"
  proof
    fix t assume in_lang: "t \<in> ?lhs"
    show "t \<in> ?rhs"
    proof (rule ccontr)
      assume "t \<notin> ?rhs"
      then have "t \<notin> NF_trs R \<or> \<not> ground t \<or> \<not> funas_term t \<subseteq> sig" by blast
      then show False proof (elim disjE)
        assume "t \<notin> NF_trs R"
        from notin_NF_E[OF this] obtain C l \<sigma> where l: "l \<in> lhss R" and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" by metis
        from ta_nf_lang_sound[OF l, of C \<sigma>, folded t] in_lang show False by blast
        next
        assume "\<not> ground t"
        with in_lang show False by (auto simp: ta_lang_def)
        next
        assume "\<not> funas_term t \<subseteq> sig"
        with ta_syms_lang[OF in_lang] ta_nf_sig show False by blast
      qed
    qed
  qed
qed

definition "ta_contains_nf TA R \<equiv> \<not> ta_empty (intersect_ta (ta_nf (lhss R) (ta_syms TA)) TA)"

lemma ta_contains_nf:
  fixes TA :: "('q, 'f) ta"
  assumes "left_linear_trs R"
  shows "ta_contains_nf TA R \<longleftrightarrow> (ta_lang TA :: ('f, 'v)term set) \<inter> NF_trs R \<noteq> {}" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  from this obtain t :: "('f, 'v)term" where "t \<in> NF_trs R" "t \<in> ta_lang TA"
    by (auto simp: ta_contains_nf_def intersect_ta ta_nf_eq_ground_nf[OF assms] ta_empty[where ?'c = 'v])
  then show "?R" by auto
  next
  let ?nfg = "{t \<in> NF_trs R. ground t \<and> funas_term t \<subseteq> ta_syms TA}"
  assume "?R"
  from this obtain t where "t \<in> NF_trs R" and lang: "t \<in> ta_lang TA" by blast
  with ta_syms_lang[OF lang] have "t \<in> ?nfg" by (auto simp: ta_lang_def)
  with ta_nf_eq_ground_nf[OF assms] have "t \<in> ta_lang (ta_nf (lhss R) (ta_syms TA))" by blast
  with lang show ?L by (auto simp: ta_contains_nf_def intersect_ta ta_empty[where ?'c = 'v])
qed

end
