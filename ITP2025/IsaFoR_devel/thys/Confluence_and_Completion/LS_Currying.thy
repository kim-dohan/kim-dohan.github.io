(*
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Preservation of confluence by currying\<close>

theory LS_Currying
  imports 
    LS_Modularity 
    First_Order_Terms.Position 
    Strongly_Closed
begin

text \<open>Here we instantiate the layer framework for currying.
      See {cite \<open>Section 5.4\<close> FMZvO15}.\<close>

locale pp_cr =
  fixes sigF :: "'f \<Rightarrow> nat option" and \<R> :: "('f, 'v :: infinite) trs" and Ap :: 'f
  assumes
    wfR: "wf_trs \<R>" and
    fresh: "sigF Ap = None" and
    sigR: "funas_trs \<R> \<subseteq> { (f, n) . sigF f = Some n }"
begin

definition \<F> where "\<F> \<equiv> { (f, n) . sigF f = Some n }"
definition \<F>\<^sub>U where "\<F>\<^sub>U \<equiv> { (Ap, 2) } \<union> { (f, m). (\<exists>n. sigF f = Some n \<and> m \<le> n)}"
definition \<F>\<^sub>C\<^sub>u where "\<F>\<^sub>C\<^sub>u \<equiv> { (Ap, 2) } \<union> { (f, m). (\<exists>n. sigF f = Some n \<and> m = 0)}"
definition \<U> where "\<U> \<equiv> { (Fun Ap ((Fun f ts) # [t]), Fun f (ts @ [t]))
                    | f n ts (t :: ('f, 'v) term). (f, n) \<in> \<F> \<and> length ts < n \<and>
                      is_Var t \<and> (\<forall>t\<^sub>i \<in> set ts. is_Var t\<^sub>i) \<and> distinct (ts @ [t])}"

definition arity where "arity f \<equiv> the (sigF f)"

lemma root_\<R>_notAp:
  assumes "(Fun f ts, r) \<in> \<R>"
  shows "f \<noteq> Ap"
using assms sigR fresh unfolding funas_trs_def funas_rule_def by fastforce

lemma size_list_butlast[termination_simp]:
  "xs \<noteq> [] \<Longrightarrow> size_list f (butlast xs) = size_list f xs - Suc (f (last xs))"
using arg_cong[OF append_butlast_last_id[of xs], of "size_list f", unfolded size_list_append]
by auto

lemma size_list_non_empty_minus_Suc[termination_simp]:
  "xs \<noteq> [] \<Longrightarrow> size_list f xs - Suc y < size_list f xs"
by (cases xs) auto

fun Cu :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "Cu (Var x) = Var x"
| "Cu (Fun f []) = Fun f []"
| "Cu (Fun f (x # xs)) = (if f = Ap
     then Fun Ap (map Cu (x # xs))
     else Fun Ap [Cu (Fun f (butlast (x # xs))), Cu (last (x # xs))])"

(*
abbreviation ap :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixl "\<bullet>\<^sub>c" 50) where
  "ap x y \<equiv> Fun Ap [x,y]"

term "f \<bullet>\<^sub>c a \<bullet>\<^sub>c b :: ('f, 'v) term"

term "if f = Ap
     then Fun Ap (map Cu (x # xs))
     else Fun Ap [Cu (Fun f (butlast (x # xs))), Cu (last (x # xs))]"
*)

lemma Cu_last1 [simp]:
  "Cu (Fun Ap xs) = Fun Ap (map Cu xs)"
by (induction xs) auto

lemma Cu_last2 [simp]:
  "f \<noteq> Ap \<Longrightarrow> Cu (Fun f (xs @ [x])) = Fun Ap [Cu (Fun f xs), Cu x]"
by (induction xs) auto

lemma Cu_const [simp]: "Cu (Fun f ts) = Fun f' [] \<Longrightarrow> f' = f \<and> ts = []"
by (cases "f = Ap"; cases "f' = Ap"; cases ts) auto

definition Cu\<^sub>R where "Cu\<^sub>R \<equiv> \<lambda>R. { (Cu l, Cu r) | l r. (l, r) \<in> R }"

lemma vars_term_Cu [simp]: "vars_term (Cu t) = vars_term t"
proof (induction t)
  case (Fun f ts) then show ?case
  proof (cases "f = Ap")
    case notAp: False then show ?thesis using Fun
    proof (induction "length ts" arbitrary: ts)
      case (Suc n)
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
      have "Cu (Fun f ts) = Fun Ap [Cu (Fun f ts'), Cu a]"
        using notAp unfolding ts_def by simp
      then have "vars_term (Cu (Fun f ts)) = vars_term (Fun f ts') \<union> vars_term a" 
        using Suc(1)[of ts'] Suc(2-) ts_def by auto
      moreover have "vars_term (Fun f ts) = vars_term (Fun f ts') \<union> vars_term a"
        unfolding ts_def by auto
      ultimately show ?case unfolding ts_def by argo
    qed simp
  qed ((cases ts), simp+)
qed simp

lemma wf_rule_Cu: 
  assumes "wf_rule (l, r)"
  shows "wf_rule (Cu l, Cu r)"
using assms vars_term_Cu unfolding wf_rule_def
  by (cases l) (auto, (metis (full_types) Cu.cases Cu.simps is_FunI))

lemma wf_Cu: "wf_trs (Cu\<^sub>R \<R>)"
proof -
  { fix l r
    assume "(l, r) \<in> Cu\<^sub>R \<R>"
    then obtain l' r' where "l = Cu l'" "r = Cu r'" "(l', r') \<in> \<R>" by (auto simp: Cu\<^sub>R_def)
    then have "wf_rule (l, r)" using wfR wf_rule_Cu[of l' r']
      by (auto simp: wf_trs_def wf_rule_def)
  }
  then show ?thesis unfolding wf_trs_def wf_rule_def by force
qed

lemma funas_Cu_helper:
  assumes "f \<noteq> Ap"
  shows "funas_term (Cu (Fun f ts)) \<subseteq> {(f, 0)} \<union> {(Ap, 2)} \<union> (\<Union>t\<in>set ts. funas_term (Cu t))"
using assms
proof (induction "length ts" arbitrary: f ts)
  case (Suc n)
  then obtain ts' a where ts_def: "ts = ts' @ [a]"
    by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
  show ?case
  proof (cases "f = Ap")
    case isAp: True
    show ?thesis using Suc(3) fresh unfolding isAp \<F>_def by simp
  next
    case notAp: False
    have Cu_unfold: "Cu (Fun f (ts' @ [a])) = Fun Ap [Cu (Fun f ts'), Cu a]"
      using notAp unfolding ts_def by simp
    then have "funas_term (Cu (Fun f ts')) \<subseteq> {(f, 0)} \<union> {(Ap, 2)} \<union> (\<Union>t\<in>set ts'. funas_term (Cu t))"
      using Suc(1)[OF _  Suc(3), of ts'] Suc(2) unfolding ts_def by simp
    then show ?thesis using notAp unfolding ts_def Cu_unfold by auto
  qed
qed simp

lemma funas_Cu: "funas_term t \<subseteq> \<F> \<Longrightarrow> funas_term (Cu t) \<subseteq> \<F>\<^sub>C\<^sub>u"
proof (induction t)
  case (Fun f ts)
  then have in_\<F>: "(f, length ts) \<in> \<F>" by simp
  then have "f \<noteq> Ap" using fresh unfolding \<F>_def by force
  then have "funas_term (Cu (Fun f ts)) \<subseteq> {(f, 0)} \<union> {(Ap, 2)} \<union> (\<Union>t\<in>set ts. funas_term (Cu t))"
    using funas_Cu_helper[of f] by blast
  moreover { fix x
    assume "x \<in> set ts"
    then have "funas_term (Cu x) \<subseteq> \<F>\<^sub>C\<^sub>u" using Fun by auto
  }
  ultimately show ?case using in_\<F> unfolding \<F>\<^sub>C\<^sub>u_def \<F>_def by auto
qed simp

lemma funas_Cu\<^sub>R: "funas_trs (Cu\<^sub>R \<R>) \<subseteq> \<F>\<^sub>C\<^sub>u"
using funas_Cu sigR unfolding funas_trs_def funas_rule_def Cu\<^sub>R_def \<F>_def
  by auto (fastforce, metis (no_types, lifting) rhs_wf set_mp sigR)

(* Calculates the number of missing args of the first non-Ap symbol
   in the left spine of the given mctxt plus 1(!), such that it is 
   0, if this symbol is a hole or var. *)
fun missing_args :: "('f, 'v) mctxt \<Rightarrow> nat \<Rightarrow> nat" where
  "missing_args MHole n = 0"
| "missing_args (MVar x) n = 0"
| "missing_args (MFun f Cs) n = (if f = Ap \<and> length Cs = 2
         then missing_args (Cs ! 0) (Suc n) else Suc (arity f) - length Cs - n)"

inductive \<LL>\<^sub>1 :: "('f, 'v) mctxt \<Rightarrow> bool" where
  mhole [intro]: "\<LL>\<^sub>1 MHole"
| mvar  [intro]: "\<LL>\<^sub>1 (MVar x)"
| mfun  [intro]: "(f, m) \<in> \<F>\<^sub>U - { (Ap, 2) } \<Longrightarrow> length Cs = m \<Longrightarrow> 
                  (\<forall>C' \<in> set Cs. \<LL>\<^sub>1 C') \<Longrightarrow> \<LL>\<^sub>1 (MFun f Cs)"
| addAp [intro]: "\<LL>\<^sub>1 C \<Longrightarrow> \<LL>\<^sub>1 C' \<Longrightarrow> missing_args C (Suc 0) \<ge> 1 \<Longrightarrow> \<LL>\<^sub>1 (MFun Ap [C, C'])"

inductive \<LL>\<^sub>2 :: "('f, 'v) mctxt \<Rightarrow> bool" where
  mvarhole [intro]: "\<LL>\<^sub>1 C \<Longrightarrow> x = MHole \<or> x = MVar v \<Longrightarrow> \<LL>\<^sub>2 (MFun Ap [x, C])"

definition \<LL> :: "('f, 'v) mctxt set" where
  "\<LL> \<equiv> { C. \<LL>\<^sub>1 C \<or> \<LL>\<^sub>2 C }"

fun check_first_non_Ap :: "nat \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "check_first_non_Ap n (Var x) = False"
| "check_first_non_Ap n (Fun f ts) = (if (f, length ts) = (Ap, 2)
    then check_first_non_Ap (Suc n) (ts ! 0)
    else arity f \<ge> n + length ts)"

lemma missing_args_unfold:
  "missing_args (mctxt_of_term t) n \<ge> 1 \<longleftrightarrow> check_first_non_Ap n t"
  by (induct n t rule: check_first_non_Ap.induct) auto

declare if_cong[cong]

fun max_top_cu :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "max_top_cu (Var x) = MVar x"
| "max_top_cu (Fun f ts) = (if check_first_non_Ap 0 (Fun f ts)
     then MFun f (map max_top_cu ts)
     else MHole)"

fun max_top_cu' :: "nat \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "max_top_cu' n (Var x) = MVar x"
| "max_top_cu' n (Fun f ts) =
    (if check_first_non_Ap n (Fun f ts)
        then if f = Ap \<and> length ts = 2
                then MFun Ap [max_top_cu' (Suc n) (ts ! 0), max_top_cu' 0 (ts ! 1)]
                else MFun f (map (max_top_cu' 0) ts)
        else MHole)"

lemma rules_missing_persist:
  assumes "r \<in> \<R> \<union> \<U>" "is_Fun (snd r)"
  shows "missing_args (mctxt_of_term (fst r \<cdot> \<sigma>)) n = missing_args (mctxt_of_term (snd r \<cdot> \<sigma>)) n"
         (is "missing_args ?l n = missing_args ?r n")
using assms(1)
proof
  assume "r \<in> \<R>"
  then obtain f ts g ss where rule_def: "fst r = Fun f ts" "snd r = Fun g ss"
    using wfR assms(2) unfolding wf_trs_def by (metis is_Fun_Fun_conv prod.collapse)
  then have arities: "sigF f = Some (length ts)" "sigF g = Some (length ss)"
    using \<open>r \<in> \<R>\<close> sigR
    unfolding funas_trs_def funas_rule_def by fastforce+
  then have "f \<noteq> Ap" "g \<noteq> Ap" using fresh by fastforce+
  then show ?thesis using rule_def arity_def arities by simp
next
  assume "r \<in> \<U>"
  then obtain f ts t m i where rule_def: 
      "fst r = Fun Ap [Fun f ts, t]" "snd r = Fun f (ts @ [t])"
      "(f, m) \<in> \<F>" "length ts = i" "i < m"
    using \<U>_def by force
  from rule_def(3-) have "f \<noteq> Ap" using fresh unfolding \<F>_def by fastforce
  then show ?thesis using rule_def by fastforce
qed

lemma check_first_non_Ap_persists:
  assumes "check_first_non_Ap n t" "m \<le> n"
  shows "check_first_non_Ap m t"
using assms
by (induction t arbitrary: m rule: check_first_non_Ap.induct) auto

lemma max_top_cu_equiv' [simp]:
  "n = 0 \<or> check_first_non_Ap n t \<Longrightarrow> max_top_cu' n t = max_top_cu t"
proof (induction t arbitrary: n)
  case (Fun f ts) then show ?case
  proof (cases "check_first_non_Ap n (Fun f ts)")
    case True then show ?thesis
    proof (cases "f = Ap \<and> length ts = 2")
      case Ap2: True
      then have "check_first_non_Ap (Suc 0) (ts ! 0)"
        using check_first_non_Ap_persists[OF True, of 0] by auto
      moreover have "max_top_cu' (Suc n) (ts ! 0) = max_top_cu (ts ! 0)"
        using Ap2 Fun(1)[of "ts ! 0" "Suc n"] Fun(2) True by auto
      moreover have "max_top_cu' 0 (ts ! 1) = max_top_cu (ts ! 1)"
        using Fun True Ap2 by force
      moreover have " map max_top_cu ts = [max_top_cu (ts ! 0), max_top_cu (ts ! Suc 0)]"
        using Ap2 unfolding map_eq_Cons_conv[of max_top_cu ts]
        by (metis Cons_nth_drop_Suc Suc_leI drop_all lessI list.simps(8,9)
            nth_drop_0 numeral_2_eq_2 one_add_one zero_less_two)
      ultimately show ?thesis using True Ap2 by auto
    next
      case not_Ap2: False
      then show ?thesis using Fun
        by (cases "check_first_non_Ap n (Fun f ts)") auto
    qed
  next
    case False
    then show ?thesis using Fun by force
  qed
qed simp

lemma max_top_cu_equiv [simp]: "max_top_cu' 0 t = max_top_cu t"
using max_top_cu_equiv' by fast

declare if_cong[cong del]

fun max_top_curry :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "max_top_curry (Var x) = MVar x"
| "max_top_curry (Fun f ts) = (if check_first_non_Ap 0 (Fun f ts) \<or> (\<exists>x. ts ! 0 = Var x)
     then MFun f (map max_top_cu ts)
     else MFun f [MHole, max_top_cu (ts ! 1)])"

lemma max_top_curry_cu_equiv [simp]: "check_first_non_Ap 0 (Fun f ts) \<longleftrightarrow>
   max_top_curry (Fun f ts) = max_top_cu (Fun f ts)"
by simp

lemma wfU: "wf_trs \<U>"
unfolding \<U>_def wf_trs_def by force

lemma sigU: "funas_trs \<U> \<subseteq> \<F>\<^sub>U"
proof
  fix f m
  assume "(f, m) \<in> funas_trs \<U>"
  then obtain r where r_in_\<U>: "r \<in> \<U>" "(f, m) \<in> funas_rule r" unfolding \<U>_def funas_trs_def by blast
  then obtain f' n i x ts t where r_props: "r = (Fun Ap [Fun f' ts, t], Fun f' (ts @ [t]))"
        "(f', n) \<in> \<F>" "i < n" "t = Var x" "length ts = i" "\<forall>t\<^sub>i \<in> set ts. is_Var t\<^sub>i"
    using \<U>_def by force
  then consider "f = Ap \<and> m = 2" | "f = f' \<and> m = i" | "f = f' \<and> m = i + 1" |
                "\<exists>x\<in>set ts. (f, m) \<in> funas_term x"
    using \<F>\<^sub>U_def r_in_\<U> unfolding funas_rule_def by simp linarith
  then show "(f, m) \<in> \<F>\<^sub>U" using r_props unfolding \<F>\<^sub>U_def \<F>_def is_Var_def by (cases) auto
qed

lemma list1_map:
  assumes "length ls = Suc 0" 
  shows "[f (ls ! 0)] = map f ls"
using assms[symmetric] unfolding Suc_length_conv by force

lemma list2_props:
  assumes "P (ls ! 0) \<and> R (ls ! 1)" "length ls = 2"
  shows "\<exists>a b. ls = [a, b] \<and> P a \<and> R b"
using assms by (metis Cons_nth_drop_Suc One_nat_def Suc_leI
  drop_all lessI nth_drop_0 numeral_2_eq_2 one_add_one zero_less_two)

lemma pos_mreplace_at:
  assumes "p \<in> all_poss_mctxt C" "mreplace_at C p D = MFun f Cs"
          "D = MHole \<or> (\<exists>x. D = MVar x)"
  shows "\<exists>i p' Cs'. p = i # p' \<and> i < length Cs \<and> C = MFun f Cs' \<and>
         p' \<in> all_poss_mctxt (Cs' ! i) \<and> i < length Cs' \<and>
         Cs = (take i Cs') @ mreplace_at (Cs' ! i) p' D # drop (i+1) Cs'"
using assms
proof (cases C)
  case (MFun f' Cs')
  then show ?thesis using assms by (cases p) (auto simp: nth_append_take)
qed auto

lemma mreplace_at_eps:
  assumes "p \<in> all_poss_mctxt C" "\<exists>x y. mreplace_at C p x = y \<and>
    (x = MHole \<or> (\<exists>x'. x = MVar x')) \<and> (y = MHole \<or> (\<exists>x'. y = MVar x'))"
  shows "p = []"
using assms
proof (induction C)
  case (MFun f Cs)
  then show ?case by force
qed auto

lemma replace_in_missing_args:
  assumes "p \<in> all_poss_mctxt C"
          "x = MHole \<or> (\<exists>v. x = MVar v)" "y = MHole \<or> (\<exists>v'. y = MVar v')"
  shows "missing_args (mreplace_at C p y) n = missing_args (mreplace_at C p x) n"
  using assms
proof (induction "mreplace_at C p x" n arbitrary: C p rule: missing_args.induct)
  case (1 n)
  then have "p = []" using mreplace_at_eps by metis
  then show ?case using 1 by force
next
  case (2 x n)
  then have "p = []" using mreplace_at_eps by metis
  then show ?case using 2 by force
next
  case (3 f Cs n)
  obtain Cs' where Cs'_props: "mreplace_at C p y = MFun f Cs'" "length Cs = length Cs'"
    using 3(2-) by (cases C) force+
  then show ?case
  proof (cases "f = Ap \<and> length Cs = 2")
    case True
    then show ?thesis
    proof (cases p)
      case Nil
      then show ?thesis using 3(2-) by fastforce
    next
      case (Cons i p')
      obtain Ds where Ds_props: "C = MFun f Ds" "Cs ! i = mreplace_at (Ds ! i) p' x"
                                "p' \<in> all_poss_mctxt (Ds ! i)"
        using pos_mreplace_at[OF 3(3) 3(2)[symmetric] 3(4)]
        unfolding Cons by (metis less_imp_le_nat nth_append_take list.inject)
      consider "i = 0" | "i = 1" using True 3(2,3) less_numeral_extra(2)
        unfolding Ds_props(1) Cons by force
      then show ?thesis
      proof (cases)
        case 1
        have "Cs' ! 0 = mreplace_at (Ds ! 0) p' y"
          using 3(4) Cs'_props(1) Ds_props unfolding Cons 1 by auto
        moreover have "missing_args (mreplace_at (Ds ! 0) p' y) (Suc n) =
                       missing_args (mreplace_at (Ds ! 0) p' x) (Suc n)"
          using Ds_props 3(1)[OF True] 3(4,5) unfolding 1 by auto
        ultimately show ?thesis using Ds_props True
          unfolding Cons 1 by auto
      next
        case 2
        have "Cs ! 0 = Ds ! 0" using 3(2,3) unfolding Ds_props(1) Cons 2
          by (simp add: nth_append_take_is_nth_conv)
        moreover have "Cs' ! 0 = Ds ! 0" using 3(3) Cs'_props(1)[symmetric]
          unfolding Ds_props(1) Cons 2
          by (simp add: nth_append_take_is_nth_conv)
        ultimately have "missing_args (Cs' ! 0) (Suc n) = missing_args (Cs ! 0) (Suc n)"
          using 3(2,3) missing_args.simps(3)[of f _ n] True 
          unfolding Ds_props(1) Cons 2 by metis
        then show ?thesis using missing_args.simps(3)[of f _ n] True Cs'_props 3(2)
          unfolding Ds_props(1) Cons 2 by metis
      qed
    qed
  next
    case False
    then show ?thesis using 3(2) Cs'_props
      by (metis missing_args.simps(3))
  qed
qed

lemma replace_var_holes1_helper:
  assumes "\<LL>\<^sub>1 (mreplace_at C p x)" and "p \<in> all_poss_mctxt C" and
          x_def: "x = MHole \<or> (\<exists>v. x = MVar v)" and y_def: "y = MHole \<or> (\<exists>v'. y = MVar v')"
  shows "\<LL>\<^sub>1 (mreplace_at C p y)"
using assms
proof (induction "(mreplace_at C p x)" arbitrary: C p rule: "\<LL>\<^sub>1.induct")
  case mhole then show ?case by (cases C) auto
next
  case mvar then show ?case by (cases C) auto
next
  case (mfun f m Cs) then show ?case
  proof (induction p)
    case (Cons i p)
    from Cons(5-6) obtain Cs' where C_def: "C = MFun f Cs'" "length Cs = length Cs'"
        "i < length Cs'" "p \<in> all_poss_mctxt (Cs' ! i)"
        "Cs = (take i Cs') @ mreplace_at (Cs' ! i) p x # drop (i+1) Cs'" by (cases C) auto
    moreover have "Cs ! i = mreplace_at (Cs' ! i) p x"
      using C_def(2-) Cons(5-6) unfolding C_def(1) by (simp add: nth_append_take)
    moreover have "Cs ! i \<in> set Cs" using Cons(6) C_def(1-2) by simp
    ultimately have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mreplace_at (Cs' ! i) p y)" using Cons(4,7,8) by blast
    let ?Cs' = "(take i Cs') @ mreplace_at (Cs' ! i) p y # drop (i+1) Cs'"
    have "\<forall>C'\<in>set Cs. \<LL>\<^sub>1 C'" using mfun(3) by blast
    then have "\<forall>C'\<in>set ?Cs'. \<LL>\<^sub>1 C'" using in_\<LL>\<^sub>1  C_def nth_mem[OF C_def(3)]
       append_Cons_nth_not_middle by auto
    then show ?case using in_\<LL>\<^sub>1 mfun(1-2) \<LL>\<^sub>1.mfun unfolding C_def(1,5) by simp
  qed auto
next
  case (addAp C' C'') then show ?case
  proof (induction p)
    case (Cons i p)
    from Cons(7,8) obtain D where C_def:
      "(C = MFun Ap [C', D] \<and> C'' = mreplace_at D p x \<and> i = 1) \<or>
       (C = MFun Ap [D, C''] \<and> C' = mreplace_at D p x \<and> i = 0)"
      "p \<in> all_poss_mctxt D" apply (cases C, auto simp: Cons_eq_append_conv)
       apply (metis drop0 drop_Suc_Cons neq_Nil_conv nth_Cons_0) 
      by (metis Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id
           length_Cons less_antisym list.size(3) not_Cons_self2 take_eq_Nil drop_eq_Nil)
    from C_def(1) show ?case
    proof (elim disjE)
      assume in_C'': "C = MFun Ap [C', D] \<and> C'' = mreplace_at D p x \<and> i = 1"
      then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mreplace_at D p y)" using Cons(5) C_def(2) in_C'' x_def y_def by auto
      show ?thesis using \<LL>\<^sub>1.addAp[OF Cons(2) in_\<LL>\<^sub>1 Cons(6)] in_C'' C_def(2) by simp
    next
      assume in_C': "C = MFun Ap [D, C''] \<and> C' = mreplace_at D p x \<and> i = 0"
      then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mreplace_at D p y)" using Cons(3) C_def(2) x_def y_def by auto
      have "missing_args (mreplace_at D p y) (Suc 0) \<ge> 1"
        using replace_in_missing_args[OF  C_def(2) x_def y_def, of "Suc 0"] Cons(6) in_C' by argo
      then show ?thesis using \<LL>\<^sub>1.addAp[OF in_\<LL>\<^sub>1 Cons(4)] in_C' C_def(2) by simp
    qed
  qed auto
qed

lemma replace_var_holes1:
  assumes "p \<in> all_poss_mctxt C" and x_def: "x = MHole \<or> (\<exists>v. x = MVar v)"
                             and y_def: "y = MHole \<or> (\<exists>v'. y = MVar v')"
  shows "\<LL>\<^sub>1 (mreplace_at C p x) = \<LL>\<^sub>1 (mreplace_at C p y)"
using assms(2-) replace_var_holes1_helper[OF _ assms(1)] by metis

lemma replace_var_holes2_helper:
  assumes "\<LL>\<^sub>2 (mreplace_at C p x)" and "p \<in> all_poss_mctxt C" and
          x_def: "x = MHole \<or> (\<exists>v. x = MVar v)" and y_def: "y = MHole \<or> (\<exists>v'. y = MVar v')"
  shows "\<LL>\<^sub>2 (mreplace_at C p y)"
using assms
proof (induction "(mreplace_at C p x)" arbitrary: C p rule: "\<LL>\<^sub>2.induct")
  case (mvarhole C' x' v)
  let ?Cs = "[x', C']"
  from mvarhole(3-) obtain i p' Cs where props: "p = i # p'" "i < length ?Cs"
      "C = MFun Ap Cs" "p' \<in> all_poss_mctxt (Cs ! i)" "i < length Cs"
      "?Cs = (take i Cs) @ mreplace_at (Cs ! i) p' x # drop (i+1) Cs"
    using pos_mreplace_at[OF mvarhole(4) mvarhole(3)[symmetric]] by blast
  have lengths: "length Cs = length ?Cs" using props by force
  have var_occurs: "subm_at (mreplace_at (Cs ! i) p' x) p' = x"
    using subm_at_mreplace_at props(4) all_poss_mctxt_conv by blast
  consider "i = 0" | "i = 1" using props(2) by fastforce
  then show ?case
  proof cases
    case i0: 1
    then have is_x': "mreplace_at (Cs ! 0) p' x = x'" using props(6) by simp
    then have "p' \<in> all_poss_mctxt x'" using props(4) all_poss_mctxt_conv
      var_occurs all_poss_mctxt_mreplace_atI1[of p' "Cs ! 0" p' x] unfolding i0 by force
    then show ?thesis using lengths var_occurs mvarhole(1,2) props(6) x_def y_def
      unfolding i0 is_x' props(1,3)
      by (metis (no_types, lifting) Cons_eq_append_conv \<LL>\<^sub>2.mvarhole list.inject
          mreplace_at.simps(1) mreplace_at.simps(2) mreplace_at_eps mvarhole.hyps(1)
           replace_at_subm_at take_eq_Nil)
  next
    case i1: 2
    have C'_def: "C' = mreplace_at (Cs ! i) p' x"
      using mvarhole(2-) props unfolding \<open>i = 1\<close>
      by simp (metis (no_types) less_imp_le_nat nth_Cons_0 nth_Cons_Suc nth_append_take)
    then have "\<LL>\<^sub>1 (mreplace_at (Cs ! i) p' y)"
      using mvarhole(1) replace_var_holes1[OF props(4)] x_def y_def by blast
    moreover have "mreplace_at C p y = MFun Ap [x', mreplace_at (Cs ! i) p' y]"
      using mvarhole(3-) props(2-) lengths
      unfolding props(1,3) i1 C'_def by simp
    ultimately show ?thesis using mvarhole(2) by auto
  qed
qed

lemma replace_var_holes2:
  assumes "p \<in> all_poss_mctxt C" and x_def: "x = MHole \<or> (\<exists>v. x = MVar v)"
                             and y_def: "y = MHole \<or> (\<exists>v'. y = MVar v')"
  shows "\<LL>\<^sub>2 (mreplace_at C p x) = \<LL>\<^sub>2 (mreplace_at C p y)"
using assms(2-) replace_var_holes2_helper[OF _ assms(1)] by metis

lemma sub_layers:
  assumes "MFun f Cs \<in> \<LL>" "i < length Cs"
  shows "\<LL>\<^sub>1 (Cs ! i)"
proof -
  consider "\<LL>\<^sub>1 (MFun f Cs)" | "\<LL>\<^sub>2 (MFun f Cs)" using assms(1) unfolding \<LL>_def by blast
  then show ?thesis
  proof cases
    case 1 then show ?thesis using assms(2) \<LL>_def
    proof (cases "MFun f Cs" rule: \<LL>\<^sub>1.cases)
      case (addAp C C')
      then show ?thesis using assms(2) \<LL>_def less_2_cases numeral_2_eq_2 by fastforce
    qed simp
  next
    case 2
    then show ?thesis using assms(2) \<LL>_def
      using \<LL>\<^sub>2.simps[of "MFun f Cs"] less_2_cases[of i] by fastforce
  qed
qed

lemma subm_at_layers [simp]:
  assumes "L \<in> \<LL>" "p \<in> all_poss_mctxt L"
  shows "subm_at L p \<in> \<LL> \<and> (p \<noteq> [] \<longrightarrow> \<LL>\<^sub>1 (subm_at L p))"
using assms sub_layers unfolding \<LL>_def
proof (induction L arbitrary: p)
  case (MFun f Cs)
  then show ?case by (cases p) (simp+, (metis nth_mem subm_at.simps(1)))
qed auto

lemma disjoint:
  shows "\<not> (\<LL>\<^sub>1 L \<and> \<LL>\<^sub>2 L)"
proof
  assume "\<LL>\<^sub>1 L \<and> \<LL>\<^sub>2 L"
  then show "False" unfolding \<LL>\<^sub>1.simps[of L] \<LL>\<^sub>2.simps[of L] by fastforce
qed

lemma missing_args_persist:
  fixes L N :: "('f, 'v) mctxt"
  assumes missing: "missing_args L n \<ge> 1" and
             comp: "(L, N) \<in> comp_mctxt"
  shows "missing_args (L \<squnion> N) n = missing_args L n"
proof -
  from missing obtain f Cs where L_def: "L = MFun f Cs"
    by (metis check_first_non_Ap.simps(1) mctxt.exhaust mctxt_of_term.simps(1)
        missing_args.simps(1) missing_args_unfold not_one_le_zero)
  show ?thesis using assms unfolding L_def
  proof (induction N arbitrary: f Cs n)
    case (MVar x)
    show ?case using MVar(2) unfolding MVar(1) using comp_mctxt.cases by blast
  next
    case (MFun f' Cs')
    have comp_cond: "f = f'" "length Cs = length Cs'"
                    "\<forall> i < length Cs'. (Cs ! i, Cs' ! i) \<in> comp_mctxt"
      using comp_mctxt.cases[OF MFun(3)] by fast+
    consider "f = Ap \<and> length Cs = 2" "missing_args (Cs ! 0) (Suc n) \<ge> 1" |
             "\<not>(f = Ap \<and> length Cs = 2)" "Suc (arity f) - length Cs - n \<ge> 1"
      using missing_args.simps(3)[of f Cs n] MFun(2) by presburger
    then show ?case
    proof cases
      case 1
      then show ?thesis
      proof (cases "Cs ! 0")
        case gDs: (MFun g Ds)
        have Cs'_0: "Cs' ! 0 \<in> set Cs'" using "1"(1) comp_cond(2) by auto
        have "MFun f Cs \<squnion> MFun f' Cs' = MFun Ap (map (\<lambda>(x, y). x \<squnion> y) (zip Cs Cs'))"
          using 1 comp_cond(1,2) by force
        then show ?thesis using MFun(1)[OF Cs'_0, of g Ds "Suc n"] gDs MFun(3) 1 comp_cond
          by fastforce
      qed auto
    next
      case 2
      then show ?thesis using MFun(3) comp_cond by force
    qed
  qed simp
qed

lemma merge_\<LL>\<^sub>1:
  assumes "\<LL>\<^sub>1 L" "(L, N) \<in> comp_mctxt" "N \<in> \<LL>"
  shows "L \<noteq> MHole \<longrightarrow> \<LL>\<^sub>1 (L \<squnion> N)"
using assms
proof (induction L arbitrary: N rule: \<LL>\<^sub>1.induct)
  case (mvar x)
  then show ?case by (metis \<LL>\<^sub>1.simps less_eq_mctxt_MVarE1 sup_mctxt_ge1)
next
  case (mfun f m Cs)
  then show ?case
  proof (cases N)
    case (MFun f' Cs')
    then have similar: "f = f' \<and> length Cs = length Cs'"
      using mfun(4) by (auto elim: comp_mctxt.cases)
    have N_in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (MFun f' Cs')" "(f', length Cs') \<noteq> (Ap, 2)" using similar mfun(1,2,5) \<LL>\<^sub>2.simps
      unfolding MFun \<LL>_def by auto
    let ?Cs = "map (case_prod sup) (zip Cs Cs')"
    have sup_def: "MFun f Cs \<squnion> MFun f' Cs' = MFun f ?Cs"
      using similar mfun(1,2,4) by simp
    have length_combined: "length ?Cs = length Cs" "length ?Cs = length (zip Cs Cs')"
      using similar by simp+
    { fix i
      assume i_assm: "i < length Cs"
      moreover have "\<LL>\<^sub>1 (Cs ! i)" using mfun(3) nth_mem i_assm by blast
      moreover have "(Cs ! i, Cs' ! i) \<in> comp_mctxt"
        using mfun(4) \<open>i < length Cs\<close> unfolding MFun by (auto elim: comp_mctxt.cases)
      moreover have "\<LL>\<^sub>1 (Cs' ! i)" using sub_layers[OF mfun(5)[unfolded MFun]] i_assm similar by simp
      ultimately have "\<LL>\<^sub>1 (Cs ! i \<squnion> Cs' ! i)" using mfun(3) nth_mem unfolding \<LL>_def
        by (cases "Cs ! i") fastforce+
    }
    then show ?thesis using similar mfun(2) length_combined nth_map[of _ "zip Cs Cs'" "case_prod sup"]
        nth_zip[of _ Cs Cs'] \<LL>\<^sub>1.mfun[OF mfun(1), of ?Cs] unfolding MFun sup_def
      by (metis (mono_tags, lifting) all_nth_imp_all_set old.prod.case)
  qed (auto elim: comp_mctxt.cases)
next
  case (addAp C C') then show ?case
  proof (cases N)
    case (MFun f' Cs')
    have Cs'_props: "length Cs' = 2" "\<forall>i < length Cs'. ([C, C'] ! i, Cs' ! i) \<in> comp_mctxt" "f' = Ap"
      using comp_mctxt.cases[OF addAp(6)] unfolding MFun
      by (simp, metis length_Cons list.size(3) numeral_2_eq_2, auto)
    have in_\<LL>: "\<forall>i < length Cs'. Cs' ! i \<in> \<LL>"
      using sub_layers[OF addAp(7)[unfolded MFun]] \<LL>_def by simp
    obtain g Ds where C_def: "C = MFun g Ds" using addAp(3)
      by (metis mctxt.exhaust missing_args.simps(1) missing_args.simps(2) not_one_le_zero)
    obtain C\<^sub>1 C\<^sub>2 where Cs'_def: "Cs' = [C\<^sub>1, C\<^sub>2]" using Cs'_props(1)
      by (metis (no_types, lifting) length_0_conv length_Suc_conv numeral_2_eq_2)
    have "\<LL>\<^sub>1 (C \<squnion> C\<^sub>1)" using Cs'_props(2) addAp(1,4) in_\<LL> unfolding Cs'_def C_def by fastforce
    consider "\<LL>\<^sub>1 N" | "\<LL>\<^sub>2 N" using addAp(7) unfolding MFun \<LL>_def by blast
    then have "\<LL>\<^sub>1 C\<^sub>2" unfolding MFun Cs'_def
    proof cases
      case 1
      then show ?thesis by (auto elim: \<LL>\<^sub>1.cases)
    next
      case 2
      then show ?thesis by (auto elim: \<LL>\<^sub>2.cases)
    qed
    then have "\<LL>\<^sub>1 (C' \<squnion> C\<^sub>2)" using Cs'_props(2) addAp(2,5) in_\<LL> unfolding Cs'_def C_def
      by (metis length_Cons lessI list.size(3) nth_Cons_0 nth_Cons_Suc
          sup_mctxt_MHole sup_mctxt_comm)
    have "(C, C\<^sub>1) \<in> comp_mctxt" using Cs'_def Cs'_props(2) by auto
    then have "missing_args (C \<squnion> C\<^sub>1) (Suc 0) \<ge> 1" using missing_args_persist[OF addAp(3)]
      using addAp.hyps(3) by auto
    then show ?thesis using \<open>\<LL>\<^sub>1 (C \<squnion> C\<^sub>1)\<close> \<open>\<LL>\<^sub>1 (C' \<squnion> C\<^sub>2)\<close> Cs'_props(2,3) unfolding MFun Cs'_def by auto
  qed (auto elim: comp_mctxt.cases)
qed auto

lemma merge_\<LL>\<^sub>2:
  assumes "\<LL>\<^sub>2 L" "\<LL>\<^sub>2 N" "(L, N) \<in> comp_mctxt"
  shows "\<LL>\<^sub>2 (L \<squnion> N)"
proof -
  obtain x C where L_def: "L = MFun Ap [x, C]" and "\<LL>\<^sub>1 C"
               and x_def: "x = MHole \<or> (\<exists>x'. x = MVar x')" 
    using \<LL>\<^sub>2.cases[OF assms(1)] by metis
  obtain y C' where N_def: "N = MFun Ap [y, C']" and "\<LL>\<^sub>1 C'"
                and y_def: "y = MHole \<or> (\<exists>y'. y = MVar y')"
    using \<LL>\<^sub>2.cases[OF assms(2)] by metis
  have comp: "(x, y) \<in> comp_mctxt" "(C, C') \<in> comp_mctxt"
    using comp_mctxt.cases[OF \<open>(L, N) \<in> comp_mctxt\<close>] unfolding L_def N_def
    by (-, simp, (metis (no_types) length_Cons nth_Cons_0 zero_less_Suc),
           simp, (metis length_Cons lessI list.size(3) nth_Cons_0 nth_Cons_Suc))
  have "\<LL>\<^sub>1 (C \<squnion> C')" using merge_\<LL>\<^sub>1[OF \<open>\<LL>\<^sub>1 C\<close> comp(2)] \<open>\<LL>\<^sub>1 C'\<close> \<LL>_def unfolding N_def by auto
  moreover have "x \<squnion> y = MHole \<or> (\<exists>z. x \<squnion> y = MVar z)"
    using x_def y_def comp_mctxt.cases[OF comp(1)] by fastforce
  ultimately show ?thesis using \<LL>_def x_def y_def unfolding L_def N_def by force
qed

lemma missing_mreplace:
  assumes "missing_args C n \<ge> 1" "\<forall>n. missing_args (subm_at C p) n \<ge> 1 \<longrightarrow> missing_args D n \<ge> 1"
          "p \<in> all_poss_mctxt C"
  shows "missing_args (mreplace_at C p D) n \<ge> 1"
using assms 
proof (induction C p D arbitrary: n rule: mreplace_at.induct)
  case (2 f Cs i p D)
  let ?Cs = "take i Cs @ mreplace_at (Cs ! i) p D # drop (Suc i) Cs"
  have length: "i < length Cs" using 2(4) by (auto simp: fun_poss_mctxt_def)
  then have lengths: "length ?Cs = length Cs" by auto
  show ?case
  proof (cases "f = Ap \<and> length Cs = 2")
    case True
    then have missing: "missing_args (Cs ! 0) (Suc n) \<ge> 1" using 2(2) by simp
    consider "i = 0" | "i = 1" using True length by fastforce
    then show ?thesis
    proof cases
      case i0: 1
      have "\<forall>n. missing_args (subm_at (Cs ! 0) p) n \<ge> 1 \<longrightarrow> missing_args D n \<ge> 1"
        using 2(3) by (simp add: i0)
      moreover have "p \<in> all_poss_mctxt (Cs ! i)"
         using 2(4) length unfolding fun_poss_mctxt_def by simp
      ultimately have "missing_args (mreplace_at (Cs ! 0) p D) (Suc n) \<ge> 1"
        using 2(1)[unfolded i0, OF missing] length unfolding i0 by fast
      then show ?thesis using True unfolding i0 by force
    next
      case i1: 2
      show ?thesis using True missing unfolding i1
        by (simp add: nth_append_take_is_nth_conv)
    qed
  next
    case False
    then have "Suc (arity f) - length Cs - n \<ge> 1" using 2(2) by (simp add: False)
    then show ?thesis using lengths False mreplace_at.simps(2)[of f Cs i p]
      missing_args.simps(3)[of f ?Cs n] by (metis Suc_eq_plus1)
  qed
qed auto

lemma replace_\<LL>\<^sub>1:
  assumes "\<LL>\<^sub>1 L" "\<LL>\<^sub>1 (subm_at L p)" "\<LL>\<^sub>1 N" "p \<in> all_poss_mctxt L" and
          missing: "\<forall>n. missing_args (subm_at L p) n \<ge> 1 \<longrightarrow> missing_args N n \<ge> 1"
  shows "\<LL>\<^sub>1 (mreplace_at L p N)"
using assms unfolding \<LL>_def
proof (induction L p N rule: mreplace_at.induct)
  case (2 f Cs i p D)
  let ?Cs = "take i Cs @ mreplace_at (Cs ! i) p D # drop (Suc i) Cs"
  have length: "i < length Cs" using 2(5) by (auto simp: fun_poss_mctxt_def)
  then have lengths: "length ?Cs = length Cs" by auto
  have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (Cs ! i) \<longrightarrow> \<LL>\<^sub>1 (mreplace_at (Cs ! i) p D)" using 2 unfolding \<LL>_def
    by (auto simp: fun_poss_mctxt_def)
  from 2(2) show ?case
  proof (cases rule: \<LL>\<^sub>1.cases[of "MFun f Cs"])
    case (mfun m)
    then have "(f, length ?Cs) \<in> \<F>\<^sub>U - {(Ap, 2)}" using length lengths by simp
    moreover have "Ball (set ?Cs) \<LL>\<^sub>1" using in_\<LL>\<^sub>1 length lengths mfun(3)
      by (metis in_set_conv_nth less_imp_le_nat nth_append_take nth_append_take_drop_is_nth_conv)
    ultimately have "\<LL>\<^sub>1 (MFun f ?Cs)" by blast
    then show ?thesis by (metis Suc_eq_plus1 mreplace_at.simps(2))
  next
    case (addAp C C')
    then consider "i = 0" | "i = 1" using length by fastforce
    then show ?thesis
    proof cases
      case i0: 1
      have "missing_args (mreplace_at C p D) (Suc 0) \<ge> 1"
        using addAp(5) 2(5,6) missing_mreplace[OF addAp(5), of p D]
        unfolding addAp(2) i0 fun_poss_mctxt_def by simp
      then show ?thesis using 2(3-) addAp(3-) in_\<LL>\<^sub>1 unfolding i0 addAp(1,2) by auto
    next
      case i1: 2
      show ?thesis using addAp(3-5) in_\<LL>\<^sub>1 unfolding i1 addAp(1,2) by auto
    qed
  qed
qed (auto simp: fun_poss_mctxt_def)

lemma replace_\<LL>\<^sub>2:
  assumes "\<LL>\<^sub>2 L" "\<LL>\<^sub>1 (subm_at L p)" "\<LL>\<^sub>1 N" "p \<in> fun_poss_mctxt L \<or> (p \<in> all_poss_mctxt L \<and> p \<noteq> [0])" and
          missing: "\<forall>n. missing_args (subm_at L p) n \<ge> 1 \<longrightarrow> missing_args N n \<ge> 1"
  shows "(mreplace_at L p N) \<in> \<LL>"
using assms unfolding \<LL>_def
proof (induction L p N rule: mreplace_at.induct)
  case (2 f Cs i p D)
  let ?Cs = "take i Cs @ mreplace_at (Cs ! i) p D # drop (Suc i) Cs"
  have length: "i < length Cs" using 2(5) by (auto simp: fun_poss_mctxt_def)
  then have lengths: "length ?Cs = length Cs" by auto
  from 2(2) show ?case
  proof (cases rule: \<LL>\<^sub>2.cases[of "MFun f Cs"])
    case (mvarhole C x v)
    consider "i = 0" | "i = 1" using mvarhole(2) length by fastforce
    then show ?thesis
    proof cases
      case i0: 1
      show ?thesis using 2(5) mvarhole(4) unfolding i0 mvarhole(1,2) fun_poss_mctxt_def by auto
    next
      case i1: 2
      show ?thesis using replace_\<LL>\<^sub>1[OF mvarhole(3) _ 2(4), of p] 2(3,5,6) mvarhole(4)
        fun_poss_mctxt_subset_all_poss_mctxt[of "C"]
        unfolding i1 mvarhole(1,2) fun_poss_mctxt_def by auto
    qed
  qed
qed (auto simp: fun_poss_mctxt_def)

lemma pp_layer_system: "layer_system \<F>\<^sub>U \<LL>"
proof
  show "\<LL> \<subseteq> layer_system_sig.\<C> \<F>\<^sub>U"
  proof
    fix C
    assume "C \<in> \<LL>"
    { fix C
      assume "\<LL>\<^sub>1 C"
      then have "C \<in> layer_system_sig.\<C> \<F>\<^sub>U" unfolding layer_system_sig.\<C>_def
        by (induction C) (auto simp: \<F>\<^sub>U_def)
    } note \<LL>\<^sub>1_case = this
    { assume "\<LL>\<^sub>2 C"
      then have "C \<in> layer_system_sig.\<C> \<F>\<^sub>U" using \<LL>\<^sub>1_case
      unfolding layer_system_sig.\<C>_def \<F>\<^sub>U_def by (induction C) auto
    } note \<LL>\<^sub>2_case = this
    from \<open>C \<in> \<LL>\<close> consider "\<LL>\<^sub>1 C" | "\<LL>\<^sub>2 C" unfolding \<LL>_def by blast
    then show "C \<in> layer_system_sig.\<C> \<F>\<^sub>U" using \<LL>\<^sub>1_case \<LL>\<^sub>2_case by cases
  qed
next (* L1 *)
  fix t :: "('f, 'v) term"
  assume funas_t: "funas_term t \<subseteq> \<F>\<^sub>U"
  then show "\<exists>L\<in>\<LL>. L \<noteq> MHole \<and> L \<le> mctxt_of_term t"
  proof (cases t)
    case (Var x)
    then have "mctxt_of_term t \<noteq> MHole \<and> mctxt_of_term t \<le> mctxt_of_term t" by simp
    moreover have "\<LL>\<^sub>1 (mctxt_of_term t)" using Var by auto
    ultimately show ?thesis using \<LL>_def by blast
  next
    case (Fun f Cs)
    then have length_Cs: "(f, length Cs) \<in> \<F>\<^sub>U" using funas_t unfolding \<F>\<^sub>U_def by simp
    let ?top = "MFun f (replicate (List.length Cs) MHole)"
    have cond: "?top \<noteq> MHole \<and> ?top \<le> mctxt_of_term t"
      using Fun by (auto simp: less_eq_mctxt_def o_def map_replicate_const)
    moreover have "?top \<in> \<LL>"
    proof (cases "f = Ap")
      case isAp: True
      have "replicate 2 MHole = [MHole, MHole]" by (simp add: numeral_2_eq_2)
      then have "\<LL>\<^sub>2 ?top" using isAp Fun length_Cs \<F>\<^sub>U_def fresh by (auto simp: \<LL>\<^sub>2.simps)
      then show ?thesis using \<LL>_def by simp
    next
      case notAp: False
      then have "(f, length Cs) \<in> \<F>\<^sub>U - { (Ap, 2) }" using funas_t Fun by simp
      then have "\<LL>\<^sub>1 ?top" using Fun length_Cs \<F>\<^sub>U_def by fastforce
      then show ?thesis using \<LL>_def by simp
    qed
      ultimately show ?thesis using \<LL>_def by blast
  qed
next (* L2 *)
  fix C :: "('f, 'v) mctxt" and p :: pos and x :: 'v
  assume p_in_possC: "p \<in> poss_mctxt C"
  then show "(mreplace_at C p (MVar x) \<in> \<LL>) = (mreplace_at C p MHole \<in> \<LL>)"
    using \<LL>_def replace_var_holes1 replace_var_holes2 all_poss_mctxt_conv[of C] by fastforce
next (* L3 *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume "L \<in> \<LL>" and "N \<in> \<LL>" and p_in_fun_poss: "p \<in> fun_poss_mctxt L" and 
         comp_context: "(subm_at L p, N) \<in> comp_mctxt"
  consider "p = [] \<and> \<LL>\<^sub>2 (subm_at L p)" | "\<LL>\<^sub>1 (subm_at L p)" using subm_at_layers[OF \<open>L \<in> \<LL>\<close>]  
    p_in_fun_poss fun_poss_mctxt_subset_all_poss_mctxt disjoint \<LL>_def by blast
  then show "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>"
  proof cases
    case 1
    consider "\<LL>\<^sub>1 N" | "\<LL>\<^sub>2 N" using \<open>N \<in> \<LL>\<close> \<LL>_def by blast
    then show ?thesis
    proof cases
      case N1: 1
      have "(N \<squnion> L) \<in> \<LL>"
        using 1 \<LL>_def merge_\<LL>\<^sub>1[OF N1 comp_mctxt_sym[OF comp_context]] sup_mctxt_MHole[of N]
        by (cases N) force+
      then show ?thesis using sup_mctxt_comm[of N L] 1 by simp
    next
      case N2: 2
      show ?thesis using merge_\<LL>\<^sub>2[OF _ N2 comp_context] 1 \<LL>_def sup_mctxt_comm[of L N]
        by fastforce
    qed
  next
    case 2
    obtain f Cs where "subm_at L p = MFun f Cs"
      using p_in_fun_poss fun_poss_mctxt_def[of L] fun_poss_fun_conv
      by (metis fun_poss_imp_poss poss_mctxt_term_conv subm_at_subt_at_conv term_mctxt_conv.simps(3))
    then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (subm_at L p \<squnion> N)" using merge_\<LL>\<^sub>1[OF 2 comp_context \<open>N \<in> \<LL>\<close>] by auto
    then show ?thesis using missing_args_persist[OF _ comp_context] replace_\<LL>\<^sub>1[OF _ 2 in_\<LL>\<^sub>1]
      replace_\<LL>\<^sub>2[OF _ 2 in_\<LL>\<^sub>1] p_in_fun_poss fun_poss_mctxt_subset_all_poss_mctxt
      \<open>L \<in> \<LL>\<close> 2 in_\<LL>\<^sub>1 p_in_fun_poss unfolding \<LL>_def by auto
  qed
qed


interpretation layer_system \<F>\<^sub>U \<LL> using pp_layer_system .

lemma lhs_rhs_in_\<T>:
  assumes "r \<in> \<R> \<union> \<U>"
  shows "fst r \<in> \<T>" "snd r \<in> \<T>"
using assms sigR sigU \<T>_def \<F>\<^sub>U_def unfolding funas_trs_def funas_rule_def by auto

lemma \<R>_props: 
  assumes "t = fst r \<or> t = snd r" "r \<in> \<R>"
  shows "(Ap, 2) \<notin> funas_term t" "funas_term t \<subseteq> \<F>\<^sub>U"
using assms sigR \<F>\<^sub>U_def fresh unfolding funas_trs_def funas_rule_def by auto

lemma \<U>r_props: 
  assumes "r \<in> \<U>"
  shows "(Ap, 2) \<notin> funas_term (snd r)" "funas_term (snd r) \<subseteq> \<F>\<^sub>U"
using assms \<F>\<^sub>U_def fresh unfolding \<U>_def \<F>_def by fastforce+

lemma check_lhs:
  assumes "r \<in> \<R> \<union> \<U>"
  shows "check_first_non_Ap 0 (fst r \<cdot> \<sigma>)"
proof -
  obtain f ts where fst_r_def: "fst r = Fun f ts"
    using assms wfR wfU unfolding wf_trs_def by (metis UnE prod.collapse)
  then have in_\<F>\<^sub>U: "(f, length ts) \<in> \<F>\<^sub>U"
    using lhs_rhs_in_\<T>(1)[OF assms] unfolding \<T>_def by simp
  consider "r \<in> \<R>" | "r \<in> \<U>" using assms by blast
  then show ?thesis
  proof cases
    case 1
    then have "f \<noteq> Ap" using root_\<R>_notAp fst_r_def by (metis prod.collapse)
    then show ?thesis using in_\<F>\<^sub>U arity_def unfolding fst_r_def \<F>\<^sub>U_def by fastforce
  next
    case 2
    then have Ap2: "f = Ap \<and> length ts = 2" using \<U>_def fst_r_def by force
    then obtain f' ts' where "ts ! 0 = Fun f' ts'"
      "arity f' > length ts'" "f' \<noteq> Ap"
      using 2 \<U>_def fst_r_def fresh unfolding \<F>_def \<F>\<^sub>U_def arity_def by force
    then show ?thesis using Ap2 unfolding fst_r_def by simp
  qed
qed

lemma check_lhs_\<R>_k0:
  assumes "r \<in> \<R>" "check_first_non_Ap k (fst r \<cdot> \<sigma>)"
  shows "k = 0"
proof -
  obtain f ts where fst_r_def: "fst r = Fun f ts"
    using assms(1) wfR unfolding wf_trs_def by (metis prod.collapse)
  then have in_\<F>: "(f, length ts) \<in> \<F>"
    using sigR assms(1) \<F>_def unfolding funas_trs_def funas_rule_def by force
  then have "f \<noteq> Ap" using fresh unfolding \<F>_def by fastforce
  then show ?thesis using assms(2) in_\<F> arity_def
    unfolding fst_r_def \<F>_def \<F>\<^sub>U_def by simp
qed

lemma nothing_missing_lhs_\<R>:
  assumes "r \<in> \<R>"
  shows "missing_args (mctxt_of_term (fst r \<cdot> \<sigma>)) 0 = 1"
proof -
  obtain f ts where fst_r_def: "fst r = Fun f ts"
    using assms(1) wfR unfolding wf_trs_def by (metis prod.collapse)
  then have in_\<F>: "(f, length ts) \<in> \<F>"
    using sigR assms(1) \<F>_def unfolding funas_trs_def funas_rule_def by force
  then have "f \<noteq> Ap" using fresh unfolding \<F>_def by fastforce
  then show ?thesis using in_\<F> arity_def
    unfolding fst_r_def \<F>_def \<F>\<^sub>U_def by simp
qed

lemma check_mt_cu'_equiv:
  assumes "check_first_non_Ap 0 t"
  shows "max_top_curry t = max_top_cu' 0 t"
using assms
proof (induction t)
  case (Fun f ts)
  then show ?case unfolding max_top_cu_equiv by simp
qed simp

lemma not_missing_persists:
  assumes "missing_args L n = 0" "M \<le> L"
  shows "missing_args M n = 0"
proof -
  { assume "missing_args M n \<ge> 1"
    then have "missing_args L n \<ge> 1" using assms(2)
    proof (induction arbitrary: L rule: missing_args.induct)
      case (3 f Cs n)
      obtain Cs' where L_def: "L = MFun f Cs'" "length Cs = length Cs'"
                              "(\<And>i. i < length Cs \<Longrightarrow> Cs ! i \<le> Cs' ! i)"
        using less_eq_mctxt_MFunE1[OF 3(3)] by metis
      then show ?case
      proof (cases "f = Ap \<and> length Cs = 2")
        case True
        then have "missing_args (Cs' ! 0) (Suc n) \<ge> 1"
          using L_def(2-) 3(1)[OF True, of "Cs' ! 0"] 3(2-) unfolding L_def(1) by auto
        then show ?thesis using True L_def by simp
      next
        case False
        then have "Suc (arity f) - length Cs' - n \<ge> 1" using 3(2) L_def(2) by auto
        then show ?thesis using L_def(2) False unfolding L_def(1) by auto
      qed
    qed auto
    then have False using assms(1) by simp
  }
  then show ?thesis by fastforce
qed

lemma check_missing_args_equiv:
  assumes "(f, length ts) = (Ap, 2)"
  shows "check_first_non_Ap n (Fun f ts) = (missing_args (max_top_cu (ts ! 0)) (Suc n) \<ge> 1)"
proof
  assume "check_first_non_Ap n (Fun f ts)"
  then show "missing_args (max_top_cu (ts ! 0)) (Suc n) \<ge> 1" using assms
  proof (induction n "Fun f ts" arbitrary: f ts rule: check_first_non_Ap.induct)
    case (2 n f ts)
    then obtain f' ts' where ts0 : "ts ! 0 = Fun f' ts'" by (cases "ts ! 0") simp+
    then have check_rec: "check_first_non_Ap (Suc n) (Fun f' ts')" using 2(2,3) by fastforce
    then show ?case
    proof (cases "(f', length ts') = (Ap, 2)")
      case Ap2: True
      have "check_first_non_Ap 0 (Fun f' ts')"
        using check_first_non_Ap_persists[OF check_rec, of 0] by blast
      then have "max_top_cu (ts ! 0) = MFun Ap (map max_top_cu ts')"
        using Ap2 unfolding ts0 by simp
      moreover have "missing_args (max_top_cu (ts' ! 0)) (Suc (Suc n)) \<ge> 1"
        using 2(1)[OF 2(3) ts0 check_rec Ap2] .
      ultimately show ?thesis using ts0 Ap2 by fastforce
    next
      case False
      then have "arity f' \<ge> (Suc n) + length ts'" using ts0 check_rec by simp
      then have "length (map max_top_cu ts') + n < arity f'" by fastforce
      then show ?thesis using ts0 False by auto
    qed
  qed
next
  assume "missing_args (max_top_cu (ts ! 0)) (Suc n) \<ge> 1"
  then show "check_first_non_Ap n (Fun f ts)" using assms
  proof (induction "max_top_cu (ts ! 0)" n arbitrary: f ts rule: missing_args.induct)
    case (2 x n) then show ?case by (metis le_numeral_extra(2) missing_args.simps(2))
  next
    case (3 f' Cs n)
    have "0 < length ts" using 3(4) by simp
    obtain g ts' where ts0: "ts ! 0 = Fun g ts'"
      using \<open>0 < length ts\<close> max_top_cu.elims[OF 3(2)[symmetric]] by fastforce
    then have g_ts_props: "g = f'" "length ts' = length Cs"
      using max_top_cu.simps(2)[of g ts'] 3(2) by (auto split: if_splits) 
    have "check_first_non_Ap (Suc n) (Fun f' ts')"
    proof (cases "(f', length ts') = (Ap, 2)")
      case True
      then have missing: "missing_args (max_top_cu (ts' ! 0)) (Suc (Suc n)) \<ge> 1"
        using 3(2-4) ts0[unfolded \<open>g = f'\<close>] by (auto split: if_splits)
      have f'Cs: "f' = Ap \<and> length Cs = 2"
        using True 3(2) unfolding ts0 \<open>g = f'\<close> g_ts_props by blast
      have Cs0: "Cs ! 0 = max_top_cu (ts' ! 0)" using 3(2-4) ts0 True \<open>0 < length ts\<close>
        by (metis Pair_inject max_top_cu.simps(2) mctxt.inject(2) mctxt.simps(8) nth_map)
      show ?thesis using 3(1)[OF f'Cs Cs0 missing True] missing by fastforce
    next
      case False
      then have "Suc (arity f') - length ts' - (Suc n) \<ge> 1"
        using 3(2-4) ts0[unfolded \<open>g = f'\<close>] g_ts_props(2)
        by (metis missing_args.simps(3))
      then show ?thesis using False by auto
    qed
    then show ?case using ts0 \<open>g = f'\<close> 3(4) by simp
  qed auto
qed

lemma max_top_cu_in_layers1 [simp]:
  assumes "t \<in> \<T>"
  shows "\<LL>\<^sub>1 (max_top_cu t)"
using assms
proof (induction t rule: max_top_cu.induct)
  case (2 f ts) then show ?case
  proof (cases "(\<not>(check_first_non_Ap 0 (Fun f ts)) \<or>
                 ((f, length ts) = (Ap, 2) \<and> (\<exists>x. ts ! 0 = Var x)))")
    case False
    then have mt_cu: "max_top_cu (Fun f ts) = MFun f (map max_top_cu ts)" by simp
    have check: "check_first_non_Ap 0 (Fun f ts)" using False by blast
    then show ?thesis using 2 False
    proof (cases "(f, length ts) = (Ap, 2)")
      case Ap2: True
      then obtain C C' where C_C': "C = max_top_cu (ts ! 0)" "C' = max_top_cu (ts ! 1)" by blast
      have not_var: "\<not>(\<exists>x. ts ! 0 = Var x)" using Ap2 False by blast
      { fix i n
        assume "i < length ts"
        then have "(ts ! i) \<in> \<T>" using 2(2) \<T>_def by fastforce
        then have "\<LL>\<^sub>1 (max_top_cu (ts ! i))" using \<open>i < length ts\<close> 2 False Ap2 by force
        { fix n
          assume assms: "i = 0" "check_first_non_Ap n (Fun f ts)"
          then have "missing_args (max_top_cu (ts ! i)) (Suc n) \<ge> 1"
            using Ap2 not_var
            proof (induction n "Fun f ts" arbitrary: i f ts rule: check_first_non_Ap.induct)
              case (2 n f ts)
              show ?case using check_missing_args_equiv[OF 2(4), of n] 2(2,3) by blast
            qed
        }
        then have "\<LL>\<^sub>1 (max_top_cu (ts ! i)) \<and>
                         (i = 0 \<longrightarrow> missing_args (max_top_cu (ts ! i)) (Suc 0) \<ge> 1)"
          using check \<open>\<LL>\<^sub>1 (max_top_cu (ts ! i))\<close> by blast
      }
      then have "\<LL>\<^sub>1 C \<and> \<LL>\<^sub>1 C' \<and> missing_args C (Suc 0) \<ge> 1" using C_C' Ap2 by force
      then have "\<LL>\<^sub>1 (MFun Ap [C, C'])" by auto
      then show ?thesis using Ap2 nth_map[of _ ts max_top_cu] length_map[of max_top_cu ts]
        unfolding mt_cu C_C'
        by (metis (no_types, lifting) One_nat_def nth_Cons_Suc length_0_conv length_Suc_conv 
            lessI list.inject nth_drop_0 numeral_2_eq_2 one_add_one prod.inject zero_less_two)
    next
      case f: False
      then have f_in_\<F>\<^sub>U: "(f, length ts) \<in> \<F>\<^sub>U - { (Ap, 2) }" using 2(2) \<T>_def by fastforce
      { fix i
        assume "i < length ts"
        then have "(ts ! i) \<in> \<T>" using 2(2) \<T>_def by fastforce
        then have "\<LL>\<^sub>1 (max_top_cu (ts ! i))" using \<open>i < length ts\<close> 2 False f by force
      }
      then show ?thesis using mfun[OF f_in_\<F>\<^sub>U] nth_map[of _ ts max_top_cu]
        unfolding mt_cu by (metis (no_types, lifting) in_set_conv_nth length_map)
    qed
  qed fastforce
qed auto

lemma check_fails_Ap:
  assumes "\<not> check_first_non_Ap 0 (Fun f ts)" "Fun f ts \<in> \<T>"
  shows "f = Ap \<and> length ts = 2"
using assms \<F>\<^sub>U_def \<T>_def by (auto simp: arity_def split: if_splits)

lemma max_top_curry_cu_equiv1:
  assumes "\<LL>\<^sub>1 (max_top_curry t)" "t \<in> \<T>"
  shows "max_top_curry t = max_top_cu t"
using assms
proof (induction t rule: max_top_curry.induct)
  case (2 f ts) then show ?case
  proof (cases "check_first_non_Ap 0 (Fun f ts) \<or> (\<exists>x. ts ! 0 = Var x)")
    case True
    then show ?thesis using 2
    proof (cases "check_first_non_Ap 0 (Fun f ts)")
      case check: True
      then show ?thesis by fastforce
    next
      case not_check: False
      have Ap2: "f = Ap \<and> length ts = 2" using check_fails_Ap[OF not_check 2(2)] .
      have "map max_top_cu ts ! 0 = max_top_cu (ts ! 0)"
        by (simp add: Ap2)
      let ?P = "\<lambda>x. x = max_top_cu (ts ! 0)"
      let ?R = "\<lambda>x. x = max_top_cu (ts ! 1)"
      have mt_simp: "max_top_curry (Fun f ts) =
                               MFun Ap [max_top_cu (ts ! 0), max_top_cu (ts ! 1)]"
        using True Ap2 using list2_props[of ?P "map max_top_cu ts" ?R] by simp
      have "missing_args (max_top_cu (ts ! 0)) (Suc 0) = 0"
        using check_missing_args_equiv not_check Ap2 by simp
      then show ?thesis using 2(1) Ap2 unfolding mt_simp by (auto elim: \<LL>\<^sub>1.cases)
    qed
  next
    case False
    then have Ap2: "f = Ap \<and> length ts = 2" using check_fails_Ap[OF _ 2(2)] by blast
    { assume in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (MFun f [MHole, max_top_cu (ts ! Suc 0)])"
      have "missing_args MHole (Suc 0) = 0" by simp
      then have "False" using in_\<LL>\<^sub>1 Ap2 by (auto elim: \<LL>\<^sub>1.cases)
    }
    then show ?thesis using 2(1) False by simp
  qed
qed simp

lemma max_top_curry_in_layers [simp]:
  assumes "t \<in> \<T>"
  shows "(max_top_curry t) \<in> \<LL>"
using assms unfolding \<LL>_def
proof (induction t rule: max_top_curry.induct)
  case (2 f ts)
  { fix i
    assume "i < length ts"
    then have "ts ! i \<in> \<T>" using 2(1) \<T>_def by force
    then have "\<LL>\<^sub>1 (max_top_cu (ts ! i))" by simp
  } note in_\<LL>\<^sub>1 = this
  then show ?case
  proof (cases "check_first_non_Ap 0 (Fun f ts) \<or> (\<exists>x. ts ! 0 = Var x)")
    case False
    then show ?thesis using in_\<LL>\<^sub>1[of 1] False check_fails_Ap[OF _ 2] by fastforce
  next
    case True then show ?thesis
    proof (cases "(f, length ts) = (Ap, 2)")
      case Ap2: True
      then have "f = Ap" "length ts = 2" by auto
      then have "ts ! Suc 0 # drop (Suc (Suc 0)) ts = drop (Suc 0) ts"
        by (metis (no_types) Cons_nth_drop_Suc lessI numeral_2_eq_2)
      then have ts_def: "ts = [ts ! 0, ts ! 1]" using \<open>length ts = 2\<close> by (simp add: nth_drop_0)
      then show ?thesis
      proof (cases "\<exists>x. ts ! 0 = Var x")
        case True
        then obtain x where "ts ! 0 = Var x" by blast
        then have "max_top_cu (ts ! 0) = MVar x" by auto
        moreover have "\<LL>\<^sub>1 (max_top_cu (ts ! 1))" using in_\<LL>\<^sub>1[of 1] Ap2 by fastforce
        ultimately have "\<LL>\<^sub>2 (MFun Ap [max_top_cu (ts ! 0), max_top_cu (ts ! 1)])"
          using Ap2 by blast
        then show ?thesis using True ts_def 
          unfolding \<open>f = Ap\<close> by simp (metis (no_types) list.simps(8,9))
      next
        case no_var: False
        then show ?thesis using Ap2 True 2 max_top_cu_in_layers1 by fastforce
      qed
    next
      case not_Ap2: False
      then have in_\<F>\<^sub>U: "(f, length ts) \<in> \<F>\<^sub>U - { (Ap, 2) }" using 2 \<T>_def by fastforce
      then have "\<LL>\<^sub>1 (MFun f (map max_top_cu ts))"
        using mfun[OF in_\<F>\<^sub>U, of "map max_top_cu ts"] in_\<LL>\<^sub>1 in_set_idx[of _ "map max_top_cu ts"]
              length_map[of max_top_cu ts] nth_map[of _ ts max_top_cu] by metis
      then show ?thesis using True by force
    qed
  qed
qed auto

lemma top_less_eq1 [simp]: "max_top_cu t \<le> mctxt_of_term t"
proof (induction t rule: max_top_cu.induct)
  case (2 f ts)
  then show ?case
  proof (cases "check_first_non_Ap 0 (Fun f ts)")
    case True
    { fix i
      assume "i < length ts"
      then have "max_top_cu (ts ! i) \<le> mctxt_of_term (ts ! i)" using 2[OF True] by simp
    } note inner = this
    moreover have "max_top_cu (Fun f ts) = MFun f (map max_top_cu ts)"
      using True max_top_cu.simps(2)[of f ts] by argo
    ultimately show ?thesis unfolding mctxt_of_term.simps(2)[of f ts]
      by (metis (mono_tags, opaque_lifting) length_map less_eq_mctxt_intros(3) nth_map)
  qed fastforce
qed simp

lemma top_less_eq [simp]:
  assumes "t \<in> \<T>"
  shows "max_top_curry t \<le> mctxt_of_term t"
using assms
proof (induction t rule: max_top_curry.induct)
  case (2 f ts)
  then show ?case
  proof (cases "check_first_non_Ap 0 (Fun f ts) \<or> (\<exists>x. ts ! 0 = Var x)")
    case False
    then have "length ts = 2" using check_fails_Ap[OF _ 2] by blast
    let ?mt_ts = "[MHole, max_top_cu (ts ! 1)]"
    let ?mctxt_ts = "[mctxt_of_term (ts ! 0), mctxt_of_term (ts ! 1)]"
    have lengths: "length ?mt_ts = length ?mctxt_ts" by fastforce
    have simp_mt: "max_top_curry (Fun f ts) = MFun f ?mt_ts"
      using False by simp    have simp_mctxt: "mctxt_of_term (Fun f ts) = MFun f ?mctxt_ts"
      using \<open>length ts = 2\<close>
      by (metis Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 drop_all lessI list.simps(8,9)
          mctxt_of_term.simps(2) nth_drop_0 one_add_one order_refl zero_less_Suc)
    have "max_top_cu (ts ! 1) \<le> mctxt_of_term (ts ! 1)" by simp
    { fix i :: nat
      assume "i < length ?mt_ts"
      then have "?mt_ts ! i \<le> ?mctxt_ts ! i"
        using \<open>max_top_cu (ts ! 1) \<le> mctxt_of_term (ts ! 1)\<close> less_2_cases numeral_2_eq_2
        by fastforce
    }
    then show ?thesis using less_2_cases lengths \<open>length ts = 2\<close> unfolding simp_mt simp_mctxt
      by (meson less_eq_mctxt_intros(3))
  next
    case True
    { fix i
      assume "i < length ts"
      then have "max_top_cu (ts ! i) \<le> mctxt_of_term (ts ! i)" by simp
    } note inner = this
    moreover have "max_top_curry (Fun f ts) = MFun f (map max_top_cu ts)"
      using True max_top_curry.simps(2)[of f ts] by argo
    ultimately show ?thesis unfolding mctxt_of_term.simps(2)[of f ts]
      by (metis (mono_tags, opaque_lifting) length_map less_eq_mctxt_intros(3) nth_map)
  qed
qed auto

lemma mt_curry_in_tops:
  assumes "t \<in> \<T>"
  shows "max_top_curry t \<in> tops t"
using topsC_def assms by simp

lemma max_top_var1: "layer_system_sig.max_top { L . \<LL>\<^sub>1 L } (Var x) = MVar x"
proof -
  let ?topsC1 = "layer_system_sig.topsC { L . \<LL>\<^sub>1 L }"
  have mvar_in_topsC: "MVar x \<in> ?topsC1 (MVar x)"
    using layer_system_sig.topsC_def[of "{ L . \<LL>\<^sub>1 L }"] by blast
  have "Var x \<in> \<T>" by (simp add: \<T>_def)
  from max_top_not_hole[OF this] have "max_top (Var x) \<noteq> MHole" .
  then show ?thesis
    using mvar_in_topsC layer_system_sig.max_topC_def[of "{ L . \<LL>\<^sub>1 L }"] 
          layer_system_sig.topsC_def[of "{ L . \<LL>\<^sub>1 L }"] by fastforce
qed

lemma max_top_cu_max:
  assumes "L \<le> mctxt_of_term t" and "\<LL>\<^sub>1 L"
  shows "L \<le> max_top_cu t"
using assms
proof (induction L "mctxt_of_term t" arbitrary: t rule: less_eq_mctxt_induct)
  case (2 x)
  then show ?case by (metis eq_iff max_top_cu.simps(1) term_of_mctxt.simps(1)
                 term_of_mctxt_mctxt_of_term_id)
next
  case (3 Cs Ds f)
  obtain ts where t_def: "t = Fun f ts" "map mctxt_of_term ts = Ds" "length ts = length Ds"
    using 3(4) mctxt_of_term.simps(2)
    by (metis length_map mctxt.inject(2) term_of_mctxt.simps(2) term_of_mctxt_mctxt_of_term_id)
  from 3(5) show ?case using t_def (2-) 3 unfolding t_def(1)
  proof (induction "MFun f Cs" arbitrary: f Cs Ds ts rule: \<LL>\<^sub>1.induct)
    case (mfun f m Cs) 
    then have notAp2: "(f, length ts) \<noteq> (Ap, 2)" by auto
    then show ?case
    proof (cases "check_first_non_Ap 0 (Fun f ts)")
      case True
      have simp_mt: "max_top_cu (Fun f ts) = MFun f (map max_top_cu ts)" using True notAp2 by auto
      { fix i
        assume i_props: "i < length Cs" "Ds ! i = mctxt_of_term (ts ! i)"
        then have "\<LL>\<^sub>1 (Cs ! i)" using sub_layers[OF _ i_props(1)] mfun(10) \<LL>_def by blast
        then have "Cs ! i \<le> max_top_cu (ts ! i)" using mfun(8)[OF i_props] by simp
      }
      then show ?thesis using mfun(6,9) simp_mt mfun_leq_mfunI[of f f Cs "map max_top_cu ts"]
        by (simp add: map_nth_eq_conv)
    next
     case False
     have "arity f < length ts" using False notAp2 by auto
     then have "(f, length ts) \<notin> \<F>\<^sub>U" using \<F>\<^sub>U_def notAp2 arity_def by auto
     then show ?thesis using mfun(1,2,5,6) by auto
    qed
  next
    case (addAp C C')
    from addAp(6-9) have C_leq: "C \<le> mctxt_of_term (ts ! 0)" by force
    have length2: "length ts = 2" using addAp(7,8) by auto
    then show ?case
    proof (cases "\<exists>x. ts ! 0 = Var x")
      case is_var: True
      then obtain x where "ts ! 0 = Var x" by blast
      then have "Ds ! 0 = MVar x" using addAp(6-8) nth_map[of _ ts mctxt_of_term] by fastforce
      moreover have "C \<le> Ds ! 0" using addAp(8,9) by force
      ultimately have "C = MHole \<or> C = MVar x" using less_eq_mctxtE2(2) by fastforce
      then show ?thesis using addAp(5) by fastforce
    next
      case not_var: False then show ?thesis
      proof (cases "check_first_non_Ap 0 (Fun Ap ts)")
      case True
      have simp_mt: "max_top_cu (Fun Ap ts) = MFun Ap (map max_top_cu ts)"
        using True not_var by auto
      { fix i
        assume i_props: "i < length [C, C']" "Ds ! i = mctxt_of_term (ts ! i)"
        then have "[C, C'] ! i \<le> max_top_cu (ts ! i)" using addAp(10)[OF i_props] addAp(1,3)
          by (simp add: nth_Cons')
      }
      then show ?thesis
        using addAp(8,11) simp_mt mfun_leq_mfunI[of Ap Ap "[C, C']" "map max_top_cu ts"]
        by (simp add: map_nth_eq_conv)
      next
        case False
        then have not_missing: "missing_args (mctxt_of_term (ts ! 0)) (Suc 0) = 0"
          using missing_args_unfold[of "ts ! 0" "Suc 0"] length2 by simp
        then have "missing_args C (Suc 0) = 0"
          using not_missing_persists[OF _ C_leq] by blast
        then show ?thesis using addAp(5) by linarith
      qed
    qed
  qed
qed auto

abbreviation max_top1 where "max_top1 \<equiv> layer_system_sig.max_top { L . \<LL>\<^sub>1 L }"
abbreviation max_topC1 where "max_topC1 \<equiv> layer_system_sig.max_topC { L . \<LL>\<^sub>1 L }"
abbreviation tops1 where "tops1 \<equiv> layer_system_sig.tops { L . \<LL>\<^sub>1 L }"
abbreviation topsC1 where "topsC1 \<equiv> layer_system_sig.topsC { L . \<LL>\<^sub>1 L }"
lemmas max_topC1_def = layer_system_sig.max_topC_def[of "{ L . \<LL>\<^sub>1 L }"]
lemmas topsC1_def = layer_system_sig.topsC_def[of "{ L . \<LL>\<^sub>1 L }"]

lemma max_top_unique1:
  shows "\<exists>!M. M \<in> topsC1 C \<and> (\<forall>L \<in> topsC1 C. L \<le> M)"
proof -
  have sub_tops: "\<And>C. topsC1 C \<subseteq> topsC C" using topsC_def topsC1_def \<LL>_def by blast
  have mhole_in_tops: "\<And>C. MHole \<in> topsC C"
    using topsC_def less_eq_mctxtI1(1) using \<LL>_def by blast
  then obtain M where M_props: "M \<in> topsC C" "\<forall>L\<in>topsC C. L \<le> M" "M \<in> \<LL>"
      using topsC_def[of C] max_topC_layer max_topC_props by meson
  consider "\<LL>\<^sub>1 M" | "\<LL>\<^sub>2 M" using M_props(3) \<LL>_def by blast
  then show ?thesis
  proof cases
    case 1
    then have "\<exists>!M. M \<in> topsC1 C \<and> (\<forall>L\<in>topsC1 C. L \<le> M)"
      using max_top_unique M_props topsC_def unfolding topsC1_def \<LL>_def by force
    then obtain M where M_props: "M \<in> topsC1 C" "\<forall>L\<in>topsC1 C. L \<le> M" "\<LL>\<^sub>1 M"
      using topsC1_def[of C] by auto
    then have "M \<in> topsC1 C" using M_props by (simp add: layer_system_sig.topsC_def)
    moreover have "\<forall>L\<in>topsC1 C. L \<le> M" using M_props(2)
      by (simp add: topsC1_def)
    ultimately show ?thesis using dual_order.antisym
      unfolding layer_system_sig.topsC_def by blast
  next
    case 2
    then obtain x C' where M_def: "M = MFun Ap [x, C']" "x = MHole \<or> (\<exists>v. x = MVar v)" "\<LL>\<^sub>1 C'"
      by (meson \<LL>\<^sub>2.cases)
    have "M \<le> C" using M_props(1) unfolding topsC_def by simp
    obtain Cs where C_def: "C = MFun Ap Cs" "length [x, C'] = length Cs"
      "(\<And>i. i < length [x, C'] \<Longrightarrow> [x, C'] ! i \<le> Cs ! i)"
      using less_eq_mctxt_MFunE1[OF \<open>M \<le> C\<close>[unfolded M_def]] by blast
    { fix L :: "('f, 'v) mctxt"
      assume "L \<in> topsC1 C"
      then have "L \<le> C" using M_props layer_system_sig.topsC_def by blast
      have "L \<le> M" using sub_tops \<open>\<forall>L\<in>topsC C. L \<le> M\<close> \<open>L \<in> topsC1 C\<close> by blast
      then have "L = MHole"
      proof (cases L)
        case MVar then show ?thesis using \<open>L \<le> C\<close> C_def by (meson less_eq_mctxt_MVarE1 mctxt.simps(6))
      next
        case (MFun f' Cs')
        have props: "f' = Ap" "length Cs' = length [x, C']"
                    "\<And>i. i < length Cs' \<Longrightarrow> Cs' ! i \<le> [x, C'] ! i"
          using \<open>L \<le> M\<close> less_eq_mctxt_MFunE1[of f' Cs' M] mctxt.inject(2)
          unfolding M_def MFun by metis+
        then have "Cs' ! 0 \<le> x" by fastforce
        then have Cs'0: "Cs' ! 0 = MHole \<or> (\<exists>v. Cs' ! 0 = MVar v)"
          using M_def(2) mctxt_order_bot.bot.extremum_uniqueI
          by (auto elim: less_eq_mctxt'.cases) (meson less_eq_mctxtE2(2))
        obtain y C'' where Cs'_def: "Cs' = [y, C'']"
          using props(2) by (auto simp: length_Suc_conv)
        have "\<LL>\<^sub>1 L" using \<open>L \<in> topsC1 C\<close> topsC1_def[of C] by blast
        then show ?thesis using  \<LL>\<^sub>1.simps[of L] Cs'0 unfolding MFun Cs'_def \<open>f' = Ap\<close> by force
      qed
    }
    moreover have "\<And>C. MHole \<in> topsC1 C" unfolding topsC1_def by auto
    ultimately show ?thesis by blast
  qed
qed

lemma max_topC_props1 [simp]:
  shows "max_topC1 C \<in> topsC1 C" and "\<And>L. L \<in> topsC1 C \<Longrightarrow> L \<le> max_topC1 C"
by (auto simp: theI'[OF max_top_unique1] layer_system_sig.max_topC_def)


lemma max_top_cu_correct [simp]:
  assumes "t \<in> \<T>"
  shows "max_top1 t = max_top_cu t"
using assms
proof (induction t)
  case (Var x) then show ?case using max_top_var1 by simp
next
  case (Fun f ts)
  then show ?case
  proof (cases "check_first_non_Ap 0 (Fun f ts)")
    case True
    then have simp_mt: "max_top_cu (Fun f ts) = MFun f (map max_top_cu ts)" by force
    then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (MFun f (map max_top_cu ts))" using max_top_cu_in_layers1[OF Fun(2)] by argo
    have max_top_lt_mt: "(THE m. m \<in> tops1 (Fun f ts) \<and> 
         (\<forall>ma. ma \<in> tops1 (Fun f ts) \<longrightarrow> ma \<le> m)) \<le> MFun f (map max_top_cu ts)"
      using max_top_cu_max[of _ "Fun f ts"] max_topC_props1
      unfolding max_topC1_def topsC1_def simp_mt by force
    have "MFun f (map max_top_cu ts) \<le> max_topC1 (MFun f (map mctxt_of_term ts))"
      using top_less_eq1[of "Fun f ts"] in_\<LL>\<^sub>1 unfolding simp_mt by (simp add: topsC1_def)
    then show ?thesis
      using max_top_lt_mt simp_mt by (simp add: Ball_def_raw max_topC1_def)
  next
    case False
    then have simp_mt: "max_top_cu (Fun f ts) = MHole" by force
    have max_top_lt_mt: "(THE m. m \<in> tops1 (Fun f ts) \<and> 
         (\<forall>ma. ma \<in> tops1 (Fun f ts) \<longrightarrow> ma \<le> m)) \<le> MHole"
      using max_top_cu_max[of _ "Fun f ts"] max_topC_props1
      unfolding max_topC1_def topsC1_def simp_mt by force
    have "MHole \<le> max_topC1 (MFun f (map mctxt_of_term ts))"
      unfolding simp_mt by (simp add: topsC1_def)
    then show ?thesis
      using max_top_lt_mt simp_mt mctxt_order_bot.bot.extremum_uniqueI
      by (simp add: Ball_def_raw max_topC1_def) fastforce
  qed
qed

lemma max_top_leq_mctxt: "max_top t \<le> mctxt_of_term t"
using max_topC_prefix by simp

lemma max_top1_simp:
  assumes "\<LL>\<^sub>1 (max_top t)"
  shows "max_top t = max_top1 t"
using assms
by (intro max_top_mono1[symmetric]) (auto simp: \<LL>_def)

lemma \<LL>\<^sub>2_not_missing:
  assumes "\<LL>\<^sub>2 L"
  shows "missing_args L n = 0"
proof -
  from assms obtain x C v where "L = MFun Ap [x, C]" "x = MHole \<or> x = MVar v"
    using \<LL>\<^sub>2.cases[OF assms] by metis
  then show ?thesis by force
qed

lemma missing_in_\<LL>\<^sub>1:
  assumes "L \<in> \<LL>" "missing_args L 0 \<ge> 1"
  shows "\<LL>\<^sub>1 L"
using assms(2,1) \<LL>\<^sub>2_not_missing \<LL>_def by force

lemma max_top_prefers_\<LL>\<^sub>1:
  assumes "MFun f Cs \<le> mctxt_of_term t" "\<LL>\<^sub>1 (MFun f Cs)"
  shows "\<LL>\<^sub>1 (max_top t)"
proof -
  consider "\<LL>\<^sub>1 (max_top t)" | "\<LL>\<^sub>2 (max_top t)" using max_topC_layer \<LL>_def by blast
  then show ?thesis
  proof cases
    case 2
    then obtain x C v where Ap2: "max_top t = MFun Ap [x, C]" "x = MHole \<or> x = MVar v"
      using \<LL>\<^sub>2.simps by blast
    obtain Ds where Ds_props: "mctxt_of_term t = MFun Ap Ds" "length [x, C] = length Ds"
      using less_eq_mctxt_MFunE1[OF max_top_leq_mctxt[of t, unfolded Ap2]] by metis
    then obtain ts where t_def: "t = Fun Ap ts" "length [x, C] = length ts"
      by (metis length_map term_of_mctxt.simps(2) term_of_mctxt_mctxt_of_term_id)
    have "length Cs = length Ds" "f = Ap" 
      using Ds_props(2) less_eq_mctxt_MFunE1[OF assms(1)]
      unfolding Ds_props(1) t_def by (fastforce, auto)
    then have "length Cs = 2" using Ds_props(2) by auto
    then obtain D D' where Cs_def: "Cs = [D, D']"
      using list2_props[OF _ \<open>length Cs = 2\<close>] by fastforce
    have missing: "missing_args D (Suc 0) \<ge> 1"
      using assms(2) \<LL>\<^sub>1.simps[of "MFun Ap [D, D']"] Cs_def \<open>length Cs = 2\<close> 
      unfolding \<open>f = Ap\<close> Cs_def by blast
    obtain g Ds' where "D = MFun g Ds'" using missing_args.elims missing
      by (metis le_numeral_extra(2))
    have "MFun Ap [D, D'] \<in> tops t"
      using topsC_def assms unfolding \<open>f = Ap\<close> Cs_def(1) \<LL>_def by blast
    then have leq: "MFun Ap [D, D'] \<le> MFun Ap [x, C]" using max_topC_props(2) Ap2 by metis
    have "D \<le> x" using less_eq_mctxt_MFunE1[OF leq]
      by (metis length_greater_0_conv list.distinct(1) mctxt.inject(2) nth_Cons_0)
    then show ?thesis using Ap2(2) \<open>D = MFun g Ds'\<close> using less_eq_mctxt_MFunE1 by fastforce
  qed
qed 

lemma max_top1_simp':
  assumes "Fun f ts \<in> \<T>" "max_top (Fun f ts) = MFun f Cs" "i < length ts"
          "i > 0 \<or> check_first_non_Ap 0 (Fun f ts)"
  shows "Cs ! i = max_top1 (ts ! i)"
proof -
  have lengths: "length Cs = length ts"
    using less_eq_mctxt_MFunE1[OF max_top_leq_mctxt[of "Fun f ts", unfolded assms(2)]]
    by fastforce
  { fix i
    assume "i < length ts"
    have ts_i: "ts ! i \<in> \<T>" using assms(1) \<open>i < length ts\<close> unfolding \<T>_def by fastforce
  } note in_\<T> = this
  consider "\<LL>\<^sub>1 (max_top (Fun f ts))" | "\<LL>\<^sub>2 (max_top (Fun f ts))"
    using max_topC_layer \<LL>_def by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using assms(3) max_top1_simp[OF 1] in_\<T>
        unfolding assms(2) max_top_cu_correct[OF assms(1)]
        by simp (metis assms(1) assms(2) max_top_not_hole mctxt.inject(2) nth_map) 
  next
    case 2
    then obtain x C v where mt_def: "MFun f Cs = MFun Ap [x, C]" "x = MHole \<or> x = MVar v" "\<LL>\<^sub>1 C"
      using \<LL>\<^sub>2.simps[of "MFun f Cs"] unfolding assms(2) by blast
    then have Ap2: "f = Ap" "length ts = 2" using lengths by auto
    from assms(4) show ?thesis
    proof (elim disjE)
      assume "i > 0"
      then have "i = 1" using mt_def(1) assms(3) lengths by auto
      let ?mt = "MFun Ap [x, max_top_cu (ts ! i)]"
      have leq: "MFun Ap [x, C] \<le> mctxt_of_term (Fun f ts)"
        using assms(2) max_topC_prefix unfolding mt_def(1) by metis
      have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (max_top_cu (ts ! i))" "max_top_cu (ts ! i) \<le> (map mctxt_of_term ts) ! i"
        using assms(3) top_less_eq1 in_\<T>[OF assms(3)] unfolding topsC_def by auto
      moreover { fix j
         assume "j < length ts"
         then have "j < 2" using Ap2(2) by auto
         have "\<forall>i<length [x, C]. [x, C] ! i \<le> (map mctxt_of_term ts) ! i"
           using less_eq_mctxt_MFunE1[OF leq] Ap2 unfolding mctxt_of_term.simps(2) by fast
         then have "x \<le> (map mctxt_of_term ts) ! 0" by fastforce
         from less_2_cases[OF \<open>j < 2\<close>] and this have
           "[x, max_top_cu (ts ! 1)] ! j \<le> (map mctxt_of_term ts) ! j"
           using in_\<LL>\<^sub>1(2) Ap2(2) unfolding \<open>i = 1\<close> by (elim disjE) simp+
      } note sub_leq = this
      then have "?mt \<le> mctxt_of_term (Fun f ts)"
        using Ap2(2) unfolding \<open>i = 1\<close> Ap2(1) mctxt_of_term.simps(2) 
        by (auto elim: less_eq_mctxtI1(3)) (metis One_nat_def length_Cons
            length_map less_eq_mctxt_intros(3) list.size(3) numeral_2_eq_2 sub_leq)
      moreover have "\<LL>\<^sub>2 ?mt" using mt_def(2) in_\<LL>\<^sub>1(1) by blast
      ultimately have in_tops: "?mt \<in> tops (Fun f ts)"
        using \<LL>_def unfolding topsC_def by blast
      have "C \<le> mctxt_of_term (ts ! i)"
        using assms(3) less_eq_mctxt_MFunE1[OF max_top_leq_mctxt[of "Fun f ts",
                                            unfolded assms(2)[unfolded mt_def(1)]]]
        unfolding \<open>i = 1\<close>
        by (metis (no_types, lifting) One_nat_def lengths mctxt.inject(2)
            mctxt_of_term.simps(2) mt_def(1) nth_Cons_0 nth_Cons_Suc nth_map)
      then have "C \<le> max_top_cu (ts ! i)" using max_top_cu_max[OF _ \<open>\<LL>\<^sub>1 C\<close>, of "ts ! i"] by simp
      moreover have "C \<ge> max_top_cu (ts ! i)"
        using assms(3) less_eq_mctxt_MFunE1[OF max_topC_props(2)[OF in_tops]]
        unfolding \<open>i = 1\<close> assms(2) mt_def Ap2(2)
        by (metis length_Cons lessI list.size(3) mctxt.inject(2) nth_Cons_0 nth_Cons_Suc)
      ultimately have "C = max_top_cu (ts ! i)" by simp
      then show ?thesis using mt_def(1) \<open>i = 1\<close> lengths in_\<T>[OF assms(3)] by auto
    next
      assume check: "check_first_non_Ap 0 (Fun f ts)"
      then have missing: "missing_args (max_top_cu (ts ! 0)) (Suc 0) \<ge> 1"
        using check_missing_args_equiv[of f ts 0] Ap2 by force
      have lengths_01: "0 < length ts" "1 < length ts" using Ap2 by simp+
      have mt_cu: "max_top_curry (Fun f ts) = MFun f (map max_top_cu ts)"
                   "length (map max_top_cu ts) = 2"
        using check Ap2 by force+
      have map_simp: "\<And>i. i < length ts \<Longrightarrow> max_top_cu (ts ! i) = (map max_top_cu ts) ! i"
        by simp
      have "\<LL>\<^sub>1 (max_top_cu (ts ! 0))" "\<LL>\<^sub>1 (max_top_cu (ts ! 1))"
        using Ap2 by (simp add: in_\<T>)+
      then obtain C C' where CC'_props: "map max_top_cu ts = [C, C']"
                                        "\<LL>\<^sub>1 C" "\<LL>\<^sub>1 C'" "missing_args C (Suc 0) \<ge> 1"
        using list2_props[OF _ mt_cu(2), of \<LL>\<^sub>1 \<LL>\<^sub>1] missing
              list2_props[OF _ mt_cu(2), of "\<lambda>C. missing_args C (Suc 0) \<ge> 1" _] 
        unfolding map_simp[OF lengths_01(1)] map_simp[OF lengths_01(2)] by fastforce
      have mt_cu2: "max_top_curry (Fun f ts) = MFun Ap [C, C']" "\<LL>\<^sub>1 (MFun Ap [C, C'])"
        using mt_cu Ap2 CC'_props(2-) unfolding CC'_props by auto
      have max_top_\<LL>\<^sub>1: "\<LL>\<^sub>1 (max_top (Fun f ts))"
        using max_top_prefers_\<LL>\<^sub>1[OF top_less_eq[OF assms(1), unfolded mt_cu2(1)] mt_cu2(2)] .
      show ?thesis using assms(1,3) max_top1_simp[OF max_top_\<LL>\<^sub>1] in_\<T> Ap2 CC'_props check map_simp
        unfolding assms(2) max_top_cu_correct[OF assms(1)] by auto
    qed
  qed
qed

(* important lemma *)
lemma max_top_curry_correct:
  assumes "t \<in> \<T>"
  shows "max_top t = max_top_curry t"
proof (cases t)
  case (Var x) then show ?thesis using max_top_var by simp
next
  case (Fun f ts)
  then show ?thesis
  proof (cases "check_first_non_Ap 0 (Fun f ts) \<or> (\<exists>x. ts ! 0 = Var x)")
    case True
    then have mt_cu: "max_top_curry (Fun f ts) = MFun f (map max_top_cu ts)" by auto
    obtain Cs where max_top_mfun: "max_top (Fun f ts) = MFun f Cs" "length Cs = length ts"
      using True assms max_topC_layer[of "mctxt_of_term t"] assms
      unfolding Fun
      by (metis (no_types, lifting) length_map less_eq_mctxt_MFunE2 max_topC_props(1)
          max_top_not_hole mctxt_of_term.simps(2) mem_Collect_eq topsC_def)
    { fix i
      assume "i < length ts"
      then have poss: "[i] \<in> all_poss_mctxt (max_top (Fun f ts))" using max_top_mfun by simp
      have "ts ! i \<in> \<T>" using assms \<open>i < length ts\<close> unfolding \<T>_def Fun by fastforce
      have subm_at_simp: "subm_at (max_top (Fun f ts)) [i] = Cs ! i" using max_top_mfun by simp
      have "MFun f Cs \<in> \<LL>" using max_top_mfun max_topC_layer by metis
      have "\<LL>\<^sub>1 (Cs ! i)" using \<open>i < length ts\<close> sub_layers[OF \<open>MFun f Cs \<in> \<LL>\<close>]
        using max_top_mfun(2) by simp
      have leq: "MFun f Cs \<le> mctxt_of_term (Fun f ts)" using max_top_mfun 
        by (metis (no_types, lifting) max_topC_props(1) mem_Collect_eq topsC_def)
      have Cs_i_leq: "Cs ! i \<le> (map mctxt_of_term ts) ! i"
        using \<open>i < length ts\<close> less_eq_mctxt_MFunE1[OF leq]
        unfolding mctxt_of_term.simps(2)[of f ts]
        by (metis max_top_mfun(2) mctxt.inject(2))
      then have "Cs ! i \<le> mctxt_of_term (ts ! i)" by (simp add: \<open>i < length ts\<close>)
      have "Cs ! i = max_top_cu (ts ! i)"
      proof (cases "i = 0")
        case i0: True
        from True show ?thesis
        proof (elim disjE)
          assume "check_first_non_Ap 0 (Fun f ts)"
          then show ?thesis using max_top1_simp'[OF assms[unfolded Fun]
            max_top_mfun(1) \<open>i < length ts\<close>] \<open>ts ! i \<in> \<T>\<close> by fastforce
        next
          assume "\<exists>x. ts ! 0 = Var x"
          then obtain x where ts0_def: "ts ! 0 = Var x" by blast
          then consider "Cs ! 0 = MVar x" | "Cs ! 0 = MHole"
            using max_top_mfun \<open>i < length ts\<close> Cs_i_leq less_eq_mctxtE2(2) unfolding i0 by fastforce
          then show ?thesis
          proof cases
            case 1 then show ?thesis using ts0_def i0 by simp
          next
            case 2
            moreover have "(map max_top_cu ts) ! 0 \<le> Cs ! 0"
              using max_topC_props(2)[OF mt_curry_in_tops[OF assms]] max_top_mfun(2) \<open>i < length ts\<close>
              unfolding Fun mt_cu max_top_mfun(1) i0
              by (metis less_eq_mctxtE2(3) mctxt.distinct(5) mctxt.inject(2))
            ultimately show ?thesis
              using ts0_def \<open>i < length ts\<close> i0 mctxt_order_bot.bot.extremum_uniqueI by auto
          qed
        qed
      next
        case i_greater: False
        then have "i > 0" using \<open>i < length ts\<close> by simp
        then show ?thesis using max_top1_simp'[OF assms[unfolded Fun] max_top_mfun(1) \<open>i < length ts\<close>]
          \<open>ts ! i \<in> \<T>\<close> by fastforce
      qed
      then have "Cs ! i = max_top_cu (ts ! i)"
        using max_top1_simp'[OF _ max_top_mfun(1)] \<open>\<LL>\<^sub>1 (Cs ! i)\<close> \<open>i < length ts\<close> \<open>ts ! i \<in> \<T>\<close>
        unfolding subm_at_simp subt_at.simps(2) by force
    }
    then show ?thesis using mt_cu max_top_mfun Fun by (metis  map_nth_eq_conv)
  next
    case False
    then have mt_cu: "max_top_curry (Fun f ts) = MFun f [MHole, max_top_cu (ts ! 1)]" by auto
    then have Ap2: "f = Ap \<and> length ts = 2" using False check_fails_Ap[OF _ assms[unfolded Fun]] by blast
    have "max_top_curry (Fun f ts) \<in> \<LL>" using max_top_curry_in_layers[OF assms] unfolding Fun .
    have "ts ! 1 \<in> \<T>" using assms Ap2 unfolding \<T>_def Fun by force
    obtain Cs where max_top_mfun: "max_top (Fun f ts) = MFun f Cs" "length Cs = 2"
      using Ap2 False assms max_topC_layer[of "mctxt_of_term t"] max_top_cu_correct[OF assms]
      unfolding Fun
      by (metis (no_types, lifting) \<LL>\<^sub>2.cases \<LL>_def length_Cons list.size(3) max_top_cu.simps(2)
          max_top_not_hole mem_Collect_eq numeral_2_eq_2 max_top1_simp)
    then have "\<LL>\<^sub>2 (max_top (Fun f ts))" using Ap2 max_top_mfun False Fun \<LL>_def max_top1_simp
      by (metis (no_types, lifting) max_topC_layer max_top_cu.simps(2)
          max_top_cu_correct[OF assms] mctxt.simps(8) mem_Collect_eq)
    then obtain x v C where mt: "max_top (Fun f ts) = MFun Ap [x, C]"
                                "\<LL>\<^sub>1 C" "x = MHole \<or> x = MVar v"
      using \<LL>\<^sub>2.simps Ap2 by blast
    have "f = Ap" using Ap2 by blast
    have leq: "MFun Ap [x, C] \<le> mctxt_of_term (Fun f ts)"
      using mt(1) by (metis (no_types, lifting) max_topC_props(1) mem_Collect_eq topsC_def)
    have "x \<le> (map mctxt_of_term ts) ! 0" using Ap2 less_eq_mctxt_MFunE1[OF leq]
      unfolding mctxt_of_term.simps(2)[of f ts]
      by (metis length_greater_0_conv list.distinct(1) mctxt.inject(2) nth_Cons_0)
    moreover have "C \<le> (map mctxt_of_term ts) ! 1" using Ap2 less_eq_mctxt_MFunE1[OF leq]
      unfolding mctxt_of_term.simps(2)[of f ts]
      by (metis One_nat_def length_Cons lessI list.size(3) mctxt.inject(2) nth_Cons_0 nth_Cons_Suc)
    ultimately have leq2: "x \<le> mctxt_of_term (ts ! 0)"
      by (simp add: Ap2)+
    then have "x = MHole" using Ap2 False less_eq_mctxt_MVarE1[of _ "mctxt_of_term (ts ! 0)"] mt(3)
      by (metis mctxt_of_term.simps(1) term_of_mctxt_mctxt_of_term_id)
    have simp_subm_at: "subm_at (max_top (Fun f ts)) [1] = C" using mt(1) by simp
    have "[1] \<in> all_poss_mctxt (max_top (Fun f ts))" unfolding mt(1) poss_mctxt_simp by simp
    then have "C = max_top_cu (ts ! 1)"
      using max_top1_simp'[OF _ mt(1)[unfolded \<open>f = Ap\<close>]] assms[unfolded Fun] Ap2
      unfolding max_top_cu_correct[OF \<open>ts ! 1 \<in> \<T>\<close>, symmetric] simp_subm_at by force
    then show ?thesis using Ap2 unfolding Fun mt(1) mt_cu \<open>x = MHole\<close> by fast
  qed
qed

abbreviation check_persists where
  "check_persists s t \<equiv> \<forall>j. check_first_non_Ap j s \<longrightarrow> check_first_non_Ap j t"

abbreviation check_weak_persists where
  "check_weak_persists j C s t \<equiv> check_first_non_Ap j C\<langle>s\<rangle> \<longrightarrow> check_first_non_Ap j C\<langle>t\<rangle>"

lemma replace_check_persist:
  assumes "check_persists s t"
  shows "check_persists C\<langle>s\<rangle> C\<langle>t\<rangle>"
using assms
proof (induction C)
  case (More f ss1 D ss2)
  then have check_D_s: "\<forall>n > 0. check_first_non_Ap n D\<langle>s\<rangle> \<longrightarrow> check_first_non_Ap n D\<langle>t\<rangle>" by blast
  { fix n
    have "check_persists (More f ss1 D ss2)\<langle>s\<rangle> (More f ss1 D ss2)\<langle>t\<rangle>"
      proof (cases "length ss1 = 0")
        case False
        then have "\<And>x. (ss1 @ x # ss2) ! 0 = ss1 ! 0" by (simp add: append_Cons_nth_left)
        then show ?thesis by (auto split: if_splits)
      qed (simp add: check_D_s)
  }
  then show ?case by blast
qed simp

lemma check_in_\<LL>\<^sub>1:
  assumes "check_first_non_Ap 0 t" "t \<in> \<T>"
  shows "\<LL>\<^sub>1 (max_top_curry t)"
proof (cases t rule: max_top_curry.cases)
  case (2 f ts) then show ?thesis
  proof (cases "f = Ap \<and> length ts = 2")
    case True
    then have "missing_args (max_top_cu (ts ! 0)) (Suc 0) \<ge> 1"
      using assms check_missing_args_equiv[of f ts 0] unfolding 2 by fast
    then have missing: "missing_args (max_top_curry t) 0 \<ge> 1" using assms True unfolding 2 by simp
    show ?thesis using missing_in_\<LL>\<^sub>1 assms(2) missing by auto
  next
    case False
    then show ?thesis using assms max_top_cu_in_layers1 \<T>_def unfolding 2
      by (metis max_top_cu.simps(2) max_top_curry.simps(2))
  qed
qed auto
                                                  
abbreviation mt_cu' where "mt_cu' \<equiv> \<lambda>k t. mctxt_term_conv (max_top_cu' k t)"
abbreviation mt_curry where "mt_curry \<equiv> \<lambda> t. mctxt_term_conv (max_top_curry t)"

lemma push_mt_in_ctxt':
  assumes "hole_pos C \<in> fun_poss_mctxt (max_top_cu' j C\<langle>s\<rangle>)"
  shows "\<exists>D k. mt_cu' j C\<langle>s\<rangle> = D\<langle>mt_cu' k s\<rangle> \<and> hole_pos C = hole_pos D \<and> (C = Hole \<longrightarrow> k = j) \<and>
         max_top_cu' k s \<noteq> MHole \<and> (k = 0 \<and> C \<noteq> Hole \<longrightarrow> check_weak_persists j C s t) \<and>
         (check_persists s t \<or> k = 0 \<longrightarrow> mt_cu' j C\<langle>t\<rangle> = D\<langle>mt_cu' k t\<rangle>)"
using assms
proof (induction C arbitrary: j)
  case Hole
  then have "max_top_cu' j s \<noteq> MHole" using fun_poss_mctxt_subset_poss_mctxt by force
  then show ?case using Hole by simp (metis ctxt.cop_nil hole_pos.simps(1))
next
  case (More f ss1 C' ss2)
  let ?C = "More f ss1 C' ss2"
  let ?ts = "ss1 @ C'\<langle>s\<rangle> # ss2"
  let ?mt = "\<lambda>xs. map (mt_cu' 0) xs"
  let ?mt' = "\<lambda>xs j. map (mt_cu' j) xs"
  show ?case
  proof (cases "check_first_non_Ap j ?C\<langle>s\<rangle>")
    case check: True then show ?thesis
    proof (cases "f = Ap \<and> Suc (length ss1 + length ss2) = 2")
      case Ap2: True
      then consider "length ss1 = 0" | "length ss1 = Suc 0"
        using nat_neq_iff by fastforce
      then show ?thesis
      proof cases
        case 1
        then have hole_pos: "hole_pos C' \<in> fun_poss_mctxt (max_top_cu' (Suc j) C'\<langle>s\<rangle>)"
          using More(2) check Ap2 by (auto simp: fun_poss_mctxt_def)
        obtain D' k' where D'_prop:
            "mt_cu' (Suc j) C'\<langle>s\<rangle> = D'\<langle>mt_cu' k' s\<rangle> \<and> hole_pos C' = hole_pos D' \<and>
              (C' = Hole \<longrightarrow> k' = (Suc j)) \<and> max_top_cu' k' s \<noteq> MHole \<and>
              (k' = 0 \<and> C' \<noteq> Hole \<longrightarrow> check_weak_persists (Suc j) C' s t) \<and>
              (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' (Suc j) C'\<langle>t\<rangle> = D'\<langle>mt_cu' k' t\<rangle>)"
          using More(1)[OF hole_pos] by blast
        let ?D = "More f (?mt ss1) D' (?mt ss2)"
        have length_ss2: "length ss2 = Suc 0"
          using Ap2 1 by (auto simp: length_Suc_conv[of ss2 0])
        then have "mt_cu' j ?C\<langle>s\<rangle> = ?D\<langle>mt_cu' k' s\<rangle> \<and> hole_pos ?C = hole_pos ?D \<and>
               max_top_cu' k' s \<noteq> MHole \<and>
              (k' = 0 \<and> ?C \<noteq> Hole \<longrightarrow> check_weak_persists j ?C s t) \<and>
              (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' j ?C\<langle>t\<rangle> = ?D\<langle>mt_cu' k' t\<rangle>)"
          using D'_prop check Ap2 1 list1_map[OF length_ss2, of "mt_cu' 0"]
                replace_check_persist[of s t "More f ss1 C' ss2"] by force
        then show ?thesis by fast
      next
        case 2
        then have hole_pos: "hole_pos C' \<in> fun_poss_mctxt (max_top_cu' 0 C'\<langle>s\<rangle>)"
          using More(2) check Ap2 nth_append_length[of ss1 "C'\<langle>s\<rangle>"]
          by (auto simp: fun_poss_mctxt_def)
        obtain D' k' where D'_prop:
            "mt_cu' 0 C'\<langle>s\<rangle> = D'\<langle>mt_cu' k' s\<rangle> \<and> hole_pos C' = hole_pos D' \<and>
             max_top_cu' k' s \<noteq> MHole \<and> (k' = 0 \<and> C' \<noteq> Hole \<longrightarrow> check_weak_persists 0 C' s t) \<and>
            (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' 0 C'\<langle>t\<rangle> = D'\<langle>mt_cu' k' t\<rangle>)"
          using More(1)[OF hole_pos] by blast
        let ?D = "More f (mt_cu' (Suc j) (ss1 ! 0) # ?mt (drop 1 ss1)) D' (?mt ss2)"
        have "mt_cu' j ?C\<langle>s\<rangle> = ?D\<langle>mt_cu' k' s\<rangle> \<and> hole_pos ?C = hole_pos ?D \<and>
              max_top_cu' k' s \<noteq> MHole \<and> (k' = 0 \<and> ?C \<noteq> Hole \<longrightarrow> check_weak_persists j ?C s t) \<and>
              (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' j ?C\<langle>t\<rangle> = ?D\<langle>mt_cu' k' t\<rangle>)"
          using D'_prop check Ap2 2 by (simp add: nth_append)
        then show ?thesis by fast
      qed
    next
      case not_Ap2: False
      then have hole_pos: "hole_pos C' \<in> fun_poss_mctxt (max_top_cu' 0 C'\<langle>s\<rangle>)"
        using More(2) check max_top_cu'.simps(2)[of j f ?ts]
        by (simp add: fun_poss_mctxt_def split: if_splits) (metis nth_append_length length_map)
      obtain D' k' where D'_prop:
          "mt_cu' 0 C'\<langle>s\<rangle> = D'\<langle>mt_cu' k' s\<rangle> \<and> hole_pos C' = hole_pos D' \<and>
           max_top_cu' k' s \<noteq> MHole \<and> (k' = 0 \<and> C' \<noteq> Hole \<longrightarrow> check_weak_persists 0 C' s t) \<and>
           (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' 0 C'\<langle>t\<rangle> = D'\<langle>mt_cu' k' t\<rangle>)"
        using More(1)[OF hole_pos] by blast
      let ?D = "More f (?mt ss1) D' (?mt ss2)"
      have "mt_cu' j ?C\<langle>s\<rangle> = ?D\<langle>mt_cu' k' s\<rangle> \<and> hole_pos ?C = hole_pos ?D \<and>
            max_top_cu' k' s \<noteq> MHole \<and> (k' = 0 \<and> ?C \<noteq> Hole \<longrightarrow> check_weak_persists j ?C s t) \<and>
            (check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' j ?C\<langle>t\<rangle> = ?D\<langle>mt_cu' k' t\<rangle>)"
        using D'_prop check not_Ap2
        by (simp (no_asm) only: max_top_cu'.simps intp_actxt.simps) force
      then show ?thesis by blast
    qed
  next
    case False
    then show ?thesis using More(2) by (auto simp: fun_poss_mctxt_def)
  qed
qed

lemma fun_poss_mt_sub:
  assumes "t \<in> \<T>"
  shows "fun_poss (mt_curry t) \<subseteq> fun_poss t"
using top_less_eq[OF assms] fun_poss_mctxt_def
 fun_poss_mctxt_mctxt_of_term fun_poss_mctxt_mono by blast

lemma push_mt_in_ctxt:
  assumes "hole_pos C \<in> fun_poss_mctxt (max_top_curry C\<langle>s\<rangle>)" "C\<langle>s\<rangle> \<in> \<T>" "C\<langle>t\<rangle> \<in> \<T>" "C \<noteq> Hole"
  shows "\<exists>D k. mt_curry C\<langle>s\<rangle> = D\<langle>mt_cu' k s\<rangle> \<and> hole_pos C = hole_pos D \<and> max_top_cu' k s \<noteq> MHole \<and>
   (k = 0 \<and> C \<noteq> Hole \<longrightarrow> check_weak_persists 0 C s t) \<and>
   (check_persists s t \<or> k = 0 \<longrightarrow> mt_curry C\<langle>t\<rangle> = D\<langle>mt_cu' k t\<rangle>)"
proof -
  consider "\<LL>\<^sub>1 (max_top_curry C\<langle>s\<rangle>)" | "\<LL>\<^sub>2 (max_top_curry C\<langle>s\<rangle>)" using assms(2) \<LL>_def by fastforce
  then show ?thesis
  proof cases
    case 1
    have mt_eq: "max_top_cu' 0 C\<langle>s\<rangle> = max_top_curry C\<langle>s\<rangle>"
      using max_top_curry_cu_equiv1[OF 1 assms(2)] by simp
    moreover obtain f ts where is_fun: "C\<langle>s\<rangle> = Fun f ts"
      using assms(1) fun_poss_mt_sub[OF assms(2)] unfolding fun_poss_mctxt_def
      by (metis empty_iff fun_poss.elims subsetCE)
    ultimately have check_Cs: "check_first_non_Ap 0 C\<langle>s\<rangle>" using max_top_curry_cu_equiv 
      unfolding max_top_cu_equiv[symmetric] by metis
    { assume "check_persists s t"
      then have "check_first_non_Ap 0 C\<langle>t\<rangle>"
        using check_Cs replace_check_persist missing_args_unfold by blast
      then have "max_top_cu' 0 C\<langle>t\<rangle> = max_top_curry C\<langle>t\<rangle>"
        using assms(3) check_in_\<LL>\<^sub>1 max_top_curry_cu_equiv1 by auto
    }
    then show ?thesis
      using push_mt_in_ctxt'[of C 0 s t] mt_eq assms(1)
      by (metis (no_types, lifting) assms(4) check_Cs check_mt_cu'_equiv)
  next
    case 2
    then obtain x C'' where in_\<LL>\<^sub>2:
        "max_top_curry C\<langle>s\<rangle> = MFun Ap [x, C'']" "x = MHole \<or> (\<exists>x'. x = MVar x')"
      using \<LL>\<^sub>2.simps by blast
    then obtain ss1 C' ss2 where C_def: "C = More Ap ss1 C' ss2" using assms(4)
    proof (induction C)
      case (More f ss1 C' ss2)
      from More(2,3) show ?thesis using assms(2) by (simp split: if_splits)
    qed simp
    have length1: "length ss1 + length ss2 = Suc 0" using assms(2) fresh
      unfolding C_def layer_system_sig.\<T>_def \<F>\<^sub>U_def by simp
    then consider "length ss1 = 0" | "length ss2 = 0" by linarith
    then have "C'' = max_top_cu' 0 C'\<langle>s\<rangle> \<and> length ss1 = Suc 0"
    proof cases
      case ss1_0: 1
      then have "False" using in_\<LL>\<^sub>2 assms(1) length1
        unfolding C_def fun_poss_mctxt_def by (simp split: if_splits) fastforce
      then show ?thesis by simp
    next
      case ss2_0: 2
      then show ?thesis using in_\<LL>\<^sub>2 assms(1) length1 unfolding C_def
        by (simp split: if_splits) (metis nth_append_length)
    qed
    then have C''_def: "C'' = max_top_cu' 0 C'\<langle>s\<rangle>" "length ss1 = Suc 0" "length ss2 = 0"
      using length1 by simp+
    have pos: "hole_pos C' \<in> fun_poss_mctxt (max_top_cu' 0 C'\<langle>s\<rangle>)"
      using assms(1) in_\<LL>\<^sub>2(1) C''_def(2-)
      unfolding C_def C''_def(1) fun_poss_mctxt_def by (simp split: if_splits)
    obtain D' k' where D'_def: "mt_cu' 0 C'\<langle>s\<rangle> = D'\<langle>mt_cu' k' s\<rangle> \<and> hole_pos C' = hole_pos D' \<and>
          max_top_cu' k' s \<noteq> MHole" "k' = 0 \<and> C' \<noteq> Hole \<longrightarrow> check_weak_persists 0 C' s t"
         "check_persists s t \<or> k' = 0 \<longrightarrow> mt_cu' 0 C'\<langle>t\<rangle> = D'\<langle>mt_cu' k' t\<rangle>"
      using push_mt_in_ctxt'[OF pos] by meson
    have mt_t: "check_persists s t \<or> k' = 0 \<longrightarrow>
          max_top_curry (Fun Ap (ss1 @ C'\<langle>t\<rangle> # ss2)) = MFun Ap [x, max_top_cu' 0 C'\<langle>t\<rangle>]"
      using in_\<LL>\<^sub>2 C''_def(2-) nth_append_length[of ss1] missing_args_unfold
      unfolding C_def C''_def(1) intp_actxt.simps(2)
      by (simp add: nth_append split: if_splits) force
    let ?D = "More Ap [mctxt_term_conv x] D' []"
    have "mt_curry C\<langle>s\<rangle> = ?D\<langle>mt_cu' k' s\<rangle> \<and> hole_pos C = hole_pos ?D \<and>
          max_top_cu' k' s \<noteq> MHole \<and> (k' = 0 \<and> C \<noteq> Hole \<longrightarrow> check_weak_persists 0 C s t)"
      using D'_def(1) in_\<LL>\<^sub>2 C''_def(2-) unfolding C_def C''_def(1) intp_actxt.simps(2)
      by (simp add: append_Cons_nth_left split: if_splits)
    moreover { assume missing: "check_persists s t \<or> k' = 0"
      then have "mt_curry C\<langle>t\<rangle> = ?D\<langle>mt_cu' k' t\<rangle>"
       using in_\<LL>\<^sub>2 C''_def(2-) mt_t unfolding C_def C''_def(1) intp_actxt.simps(2)
         D'_def(3)[THEN mp, OF missing, symmetric] by (simp split: if_splits)
    }
    ultimately show ?thesis by blast
  qed
qed

lemma push_mt_in_subst:
  assumes "(Ap, 2) \<notin> funas_term t" "funas_term t \<subseteq> \<F>\<^sub>U"
  shows "(mt_cu' 0 t) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)) = mt_cu' 0 (t \<cdot> \<sigma>)"
using assms
proof (induction t)
  case (Fun f ts)
  { fix x
    assume "x \<in> set ts"
    then have funas: "(Ap, 2) \<notin> funas_term x"
      using Fun(2) by fastforce
    have "mt_cu' 0 x \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>))
        = mt_cu' 0 (x \<cdot> \<sigma>)"
      using Fun(1)[OF _ funas] \<open>x \<in> set ts\<close> Fun(2,3) by auto
  }
  moreover have not_Ap2: "\<not>(f = Ap \<and> length ts = 2)" using Fun(2) by force
  moreover have check1: "check_first_non_Ap 0 (Fun f ts)"
    using not_Ap2 Fun(3) \<T>_def check_fails_Ap[of f ts] by blast
  moreover have "check_first_non_Ap 0 (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
    using not_Ap2 check1 by force
  ultimately show ?case by (simp only: eval_term.simps max_top_cu'.simps) force
qed auto

lemma push_mt_in_subst_k':
  assumes "(Ap, 2) \<notin> funas_term t" "funas_term t \<subseteq> \<F>\<^sub>U"
  shows "\<exists>k'. (mt_cu' k t) \<cdot> (case_option (Var None) (mt_cu' k' \<circ> \<sigma>)) = mt_cu' k (t \<cdot> \<sigma>) \<and>
              (is_Var t \<or> k' = 0)"
using assms
proof (induction t arbitrary: k)
  case (Fun f ts)
  { fix i
    assume "i < length ts"
    then have funas: "(Ap, 2) \<notin> funas_term (ts ! i)"
      using Fun(2) by fastforce
    then have "mt_cu' 0 (ts ! i) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>))
         = mt_cu' 0 ((ts ! i) \<cdot> \<sigma>)"
      using push_mt_in_subst[OF funas] Fun(3) \<open>i < length ts\<close> by fastforce
  } note inner = this
  have not_Ap2: "\<not>(f = Ap \<and> length ts = 2)" using Fun(2) by force
  then show ?case
  proof (cases "check_first_non_Ap k (Fun f ts)")
    case check: True
    then obtain ts' where ts'_props: "ts' = map (\<lambda>t. t \<cdot> \<sigma>) ts" "length ts' = length ts"
      by fastforce
    then have unfold_mt: "max_top_cu' k (Fun f ts \<cdot> \<sigma>) = MFun f (map (max_top_cu' 0) ts')"
      using not_Ap2 check by auto
    then show ?thesis using not_Ap2 check inner unfolding unfold_mt using ts'_props
      by (auto simp: in_set_conv_nth[of _ ts])
  next
    case not_check: False
    then show ?thesis using not_Ap2 by (simp split: if_splits) blast
  qed
qed auto

lemma push_mt_in_subst_k_snd:
  assumes "r \<in> \<R> \<union> \<U>" "is_Fun (snd r)"
  shows "(mt_cu' k (snd r)) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)) =
          mt_cu' k ((snd r) \<cdot> \<sigma>)"
using push_mt_in_subst_k' \<U>r_props \<R>_props[of "snd r" r] assms by blast

lemma push_mt_in_subst_k_\<R>l:
  assumes "r \<in> \<R>"
  shows "(mt_cu' k (fst r)) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)) =
          mt_cu' k ((fst r) \<cdot> \<sigma>)"
proof -
  obtain k' where "(mt_cu' k (fst r)) \<cdot> (case_option (Var None) (mt_cu' k' \<circ> \<sigma>)) =
                    mt_cu' k ((fst r) \<cdot> \<sigma>) \<and> (is_Var (fst r) \<or> k' = 0)"
    using push_mt_in_subst_k'[OF \<R>_props[OF _ assms, of "fst r"]] by blast
  moreover have "is_Fun (fst r)" using wfR assms unfolding wf_trs_def
    by (metis is_Fun_Fun_conv prod.collapse)
  ultimately show ?thesis by fastforce
qed

lemma push_mt_in_subst_k_\<U>l:
  assumes "r \<in> \<U>"
  shows "(mt_cu' k (fst r)) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)) =
          mt_cu' k ((fst r) \<cdot> \<sigma>)"
proof -
  obtain f ts x n where term_def: "fst r = Fun Ap [(Fun f ts), x]" "is_Var x"
              "(f, n) \<in> \<F>" "length ts < n" "\<forall>t\<^sub>i \<in> set ts. is_Var t\<^sub>i"
    using \<U>_def assms by force
  have funas: "(Ap, 2) \<notin> funas_term (Fun f ts)" "funas_term (Fun f ts) \<subseteq> \<F>\<^sub>U"
    using term_def(2-) fresh unfolding \<F>_def \<F>\<^sub>U_def by fastforce+
  then have "(mt_cu' (Suc k) (Fun f ts)) \<cdot> (case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)) =
          mt_cu' (Suc k) (Fun f ts \<cdot> \<sigma>)"
    using push_mt_in_subst_k' by blast
  moreover have "mt_cu' 0 x \<cdot> case_option (Var None) (mt_cu' 0 \<circ> \<sigma>) =
                 mt_cu' 0 (x \<cdot> \<sigma>)"
    using term_def(2) by fastforce
  ultimately have core:
    "mctxt_term_conv (MFun Ap [max_top_cu' (Suc k) (map (\<lambda>t. t \<cdot> \<sigma>) [Fun f ts, x] ! 0),
                               max_top_cu' 0 (map (\<lambda>t. t \<cdot> \<sigma>) [Fun f ts, x] ! 1)]) =
     Fun Ap [mt_cu' (Suc k) (Fun f ts) \<cdot> case_option (Var None) (mt_cu' 0 \<circ> \<sigma>),
             mt_cu' 0 x \<cdot> case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)]" by fastforce
  have check: "check_first_non_Ap k (Fun Ap [Fun f ts, x]) =
               check_first_non_Ap k (Fun Ap [Fun f ts, x] \<cdot> \<sigma>)"
    using term_def(3-) arity_def fresh unfolding \<F>_def by force
  show ?thesis using check core unfolding term_def(1) by auto
qed

lemma mt_cu'k_\<R>':
  assumes "check_first_non_Ap k t" "(Ap, 2) \<notin> funas_term t" "t \<in> \<T>"
  shows "max_top_cu' k t = mctxt_of_term t"
using assms
proof (induction rule: max_top_cu'.induct)
  case (2 n f ts)
  have not_Ap2: "\<not> (f = Ap \<and> length ts = 2)" using 2(5) by simp
  moreover { fix i
    assume "i < length ts"
    then have in_\<T>: "(ts ! i) \<in> \<T>" using \<T>_subt_at[OF 2(6), of "[i]"] by simp
    have no_Aps: "(Ap, 2) \<notin> funas_term (ts ! i)"
      using 2(5) \<open>i < length ts\<close> by fastforce
    then have "max_top_cu' 0 (ts ! i) = mctxt_of_term (ts ! i)"
    proof (cases "is_Var (ts ! i)")
      case funs: False
      then obtain f' ts' where ts_i: "ts ! i = Fun f' ts'" by fast
      have check0: "check_first_non_Ap 0 (ts ! i)"
        using check_fails_Ap[OF _ in_\<T>[unfolded ts_i]] no_Aps
        unfolding ts_i by fastforce
      then show ?thesis using 2(3)[OF 2(4) not_Ap2 _ check0 no_Aps in_\<T>]
        \<open>i < length ts\<close> by simp
    qed auto
  }
  then show ?case using not_Ap2 2(4) in_set_idx[of _ ts] by (auto split: if_splits)
qed simp

lemma mt_cu'k_\<R>:
  assumes "check_first_non_Ap k t"
          "t = fst r \<or> t = snd r" "r \<in> \<R>"
  shows "max_top_cu' k t = mctxt_of_term t"
using \<R>_props[OF assms(2,3)] mt_cu'k_\<R>'[OF assms(1) _] \<T>_def by blast

lemma mt_cu'k_\<U>r:
  assumes "check_first_non_Ap k (snd r)" "r \<in> \<U>"
  shows "max_top_cu' k (snd r) = mctxt_of_term (snd r)"
using \<U>r_props[OF assms(2)] mt_cu'k_\<R>'[OF assms(1) _] \<T>_def by blast

lemma mt_cu'k_\<U>l:
  assumes "check_first_non_Ap k (fst r)" "r \<in> \<U>"
  shows "max_top_cu' k (fst r) = mctxt_of_term (fst r)"
proof -
  obtain f ts x n where term_def: "fst r = Fun Ap [(Fun f ts), x]" "is_Var x"
              "(f, n) \<in> \<F>" "length ts < n" "\<forall>t\<^sub>i \<in> set ts. is_Var t\<^sub>i"
    using \<U>_def assms(2) by force
  have no_Aps: "(Ap, 2) \<notin> funas_term (Fun f ts)"
    using term_def fresh unfolding \<F>_def by fastforce
  have in_\<T>: "Fun f ts \<in> \<T>" using term_def
    unfolding layer_system_sig.\<T>_def \<F>\<^sub>U_def \<F>_def is_Var_def by auto
  have inner_check: "check_first_non_Ap (Suc k) (Fun f ts)"
    using assms(1) term_def by simp
  show ?thesis using assms(1) mt_cu'k_\<R>'[OF inner_check no_Aps in_\<T>] term_def(1,2)
    by force
qed

lemma case_option_Some:
  shows "case_option n s \<circ> Some = s"
by fastforce

lemma check_remove_subst_lhs_\<R>:
  assumes "check_first_non_Ap k (t \<cdot> \<sigma>)" "t = fst r" "r \<in> \<R>"
  shows "check_first_non_Ap k t"
proof -
  have funas: "(Ap, 2) \<notin> funas_term t" "funas_term t \<subseteq> \<F>\<^sub>U"
    using \<R>_props[OF _ assms(3)] assms(2) by blast+
  obtain f ts where t_def: "t = Fun f ts"
    using assms(2,3) wfR unfolding wf_trs_def by (metis prod.collapse)
  with assms(1) funas show ?thesis by fastforce
qed

lemma check_remove_subst_lhs_\<U>:
  assumes "check_first_non_Ap k (t \<cdot> \<sigma>)" "t = fst r" "r \<in> \<U>"
  shows "check_first_non_Ap k t"
proof -
  obtain f ts x n where term_def: "t = Fun Ap [(Fun f ts), x]" "is_Var x"
              "(f, n) \<in> \<F>" "length ts < n" "\<forall>t\<^sub>i \<in> set ts. is_Var t\<^sub>i"
    using \<U>_def assms by force
  have funas: "(Ap, 2) \<notin> funas_term (Fun f ts)" "funas_term (Fun f ts) \<subseteq> \<F>\<^sub>U"
    using term_def(2-) fresh unfolding \<F>_def \<F>\<^sub>U_def by fastforce+
  obtain g ss where t_def: "t = Fun g ss"
    using assms(2,3) wfU unfolding wf_trs_def by (metis prod.collapse)
  with assms(1) funas term_def show ?thesis
  proof (induction rule: check_first_non_Ap.induct)
    case (2 n g' ss')
    then show ?case by auto
  qed blast
qed


text \<open>main lemma for condition C_1 in proof of layered\<close>
lemma lemma_C\<^sub>1:
  fixes p :: pos and s t :: "('f, 'v) term" and r :: "('f, 'v) term \<times> ('f, 'v) term" and \<sigma>
  assumes "s \<in> \<T>" and "t \<in> \<T>" and in_fun_poss: "p \<in> fun_poss_mctxt (max_top s)" and
          rstep_s_t: "(s, t) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<sigma>" and
          s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R> \<union> \<U>" and
          p_def: "p = hole_pos C" and "is_Fun s"
  shows "\<exists>\<tau>. (mctxt_term_conv (max_top s), mctxt_term_conv (max_top t)) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau> \<or>
             (mctxt_term_conv (max_top s), mctxt_term_conv MHole) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau>"
proof -
  let ?M = "max_top s" and ?L = "max_top t"
  obtain f ts where "s = Fun f ts" using \<open>is_Fun s\<close> by auto
  have max_top_curry_equiv: "max_top s = max_top_curry s" 
    using max_top_curry_correct[OF \<open>s \<in> \<T>\<close>] .
  have check0l: "check_first_non_Ap 0 (fst r \<cdot> \<sigma>)" using check_lhs[OF \<open>r \<in> \<R> \<union> \<U>\<close>] by simp
  note in_fp = in_fun_poss[unfolded p_def max_top_curry_equiv]
  have "\<exists>D k. mt_curry C\<langle>fst r \<cdot> \<sigma>\<rangle> = D\<langle>mt_cu' k (fst r \<cdot> \<sigma>)\<rangle> \<and> hole_pos C = hole_pos D \<and>
              max_top_cu' k (fst r \<cdot> \<sigma>) \<noteq> MHole \<and>
             (check_persists (fst r \<cdot> \<sigma>) (snd r \<cdot> \<sigma>) \<or> (C \<noteq> Hole \<and> k = 0) \<longrightarrow>
              mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle> = D\<langle>mt_cu' k (snd r \<cdot> \<sigma>)\<rangle>)"
  proof (cases C)
    case Hole
    then have "max_top_curry C\<langle>fst r \<cdot> \<sigma>\<rangle> = max_top_cu' 0 C\<langle>fst r \<cdot> \<sigma>\<rangle>"
          "max_top_cu' 0 (fst r \<cdot> \<sigma>) \<noteq> MHole"
      using max_top_curry_cu_equiv check_lhs[OF \<open>r \<in> \<R> \<union> \<U>\<close>, of \<sigma>] \<open>s = Fun f ts\<close>
       s_def_t_def(1) unfolding max_top_cu_equiv by simp+
    moreover
    { assume "check_persists (fst r \<cdot> \<sigma>) (snd r \<cdot> \<sigma>)"
      then have check0r: "check_first_non_Ap 0 (snd r \<cdot> \<sigma>)"
        using check0l missing_args_unfold le_trans by blast
      moreover have is_fun: "is_Fun (snd r \<cdot> \<sigma>)" using check0r by auto
      ultimately have "max_top_curry C\<langle>snd r \<cdot> \<sigma>\<rangle> = max_top_cu' 0 C\<langle>snd r \<cdot> \<sigma>\<rangle>"
        using max_top_curry_cu_equiv s_def_t_def(2) Hole by fastforce
    }
    ultimately show ?thesis using Hole
      by (metis intp_actxt.simps(1) hole_pos.simps(1))
  next
    case (More f ss1 C' ss2)
    show ?thesis using push_mt_in_ctxt[OF in_fp[unfolded s_def_t_def], of "snd r \<cdot> \<sigma>"] 
            \<open>s \<in> \<T>\<close> \<open>t \<in> \<T>\<close> unfolding s_def_t_def More by blast
  qed
  then obtain D k where part1:
      "mt_curry C\<langle>fst r \<cdot> \<sigma>\<rangle> = D\<langle>mt_cu' k (fst r \<cdot> \<sigma>)\<rangle>" "hole_pos C = hole_pos D"
      "max_top_cu' k (fst r \<cdot> \<sigma>) \<noteq> MHole"
      "check_persists (fst r \<cdot> \<sigma>) (snd r \<cdot> \<sigma>) \<or> (C \<noteq> Hole \<and> k = 0) \<longrightarrow>
       mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle> = D\<langle>mt_cu' k (snd r \<cdot> \<sigma>)\<rangle>"
    by blast
  from part1(3) have check_fst_\<sigma>: "check_first_non_Ap k (fst r \<cdot> \<sigma>)"
    using check_first_non_Ap.elims(2)[OF check_lhs[OF \<open>r \<in> (\<R> \<union> \<U>)\<close>]]
    by (metis max_top_cu'.simps(2))
  then have check_fst_r: "check_first_non_Ap k (fst r)"
    using check_remove_subst_lhs_\<R>[OF check_fst_\<sigma>] \<open>r \<in> (\<R> \<union> \<U>)\<close>
          check_remove_subst_lhs_\<U>[OF check_fst_\<sigma>] by blast
  let ?\<sigma>' = "case_option (Var None) (mt_cu' 0 \<circ> \<sigma>)"
  let ?\<tau>' = "mt_cu' 0 \<circ> \<sigma>"
  have part2: "mt_cu' k (fst r \<cdot> \<sigma>) = (mt_cu' k (fst r)) \<cdot> ?\<sigma>'"
    using push_mt_in_subst_k_\<R>l[of r k \<sigma>] push_mt_in_subst_k_\<U>l[of r k \<sigma>]
      \<open>r \<in> (\<R> \<union> \<U>)\<close> by (metis UnE)
  have part2_2: "mt_cu' k (fst r) = (fst r) \<cdot> (Var \<circ> Some)"
    using mt_cu'k_\<R>[of k "fst r" r] mt_cu'k_\<U>l[of k r]
          check_fst_r UnE[OF \<open>r \<in> (\<R> \<union> \<U>)\<close>] mctxt_term_conv_mctxt_of_term by metis
  have first_half: "mt_curry s = D\<langle>fst r \<cdot> ?\<tau>'\<rangle>"
    using s_def_t_def(1) part1 part2 part2_2 by (auto simp: var_subst_comp case_option_Some)
  consider (is_fun) "is_Fun (snd r) \<or> C \<noteq> Hole" | (is_var) "is_Var (snd r) \<and> C = Hole" by blast
  then show ?thesis
  proof cases
    case is_fun
    { assume "is_Var (snd r)"
      then have "r \<in> \<R>" using \<U>_def \<open>r \<in> (\<R> \<union> \<U>)\<close> by fastforce
      have "k = 0" using check_lhs_\<R>_k0[OF \<open>r \<in> \<R>\<close> check_fst_\<sigma>] .
    } note var_imp_k0 = this
    then have missing: "check_persists (fst r \<cdot> \<sigma>) (snd r \<cdot> \<sigma>) \<or> (C \<noteq> \<box> \<and> k = 0)"
      using is_fun rules_missing_persist[OF \<open>r \<in> (\<R> \<union> \<U>)\<close>] missing_args_unfold by metis
    have part3: "(mt_cu' k (snd r)) \<cdot> ?\<sigma>' = mt_cu' k (snd r \<cdot> \<sigma>)"
      using push_mt_in_subst_k_snd[OF \<open>r \<in> (\<R> \<union> \<U>)\<close>] is_fun var_imp_k0
      by (cases "is_Var (snd r)") force+
    have part3_2: "mt_cu' k (snd r) = (snd r) \<cdot> (Var \<circ> Some)"
    proof (cases "is_Var (snd r)")
      case True
      then show ?thesis using mctxt_term_conv_mctxt_of_term by auto
    next
      case False
      have check_snd_r: "check_first_non_Ap k (snd r)"
        using check_fst_r rules_missing_persist[OF \<open>r \<in> (\<R> \<union> \<U>)\<close> False, of Var]
              missing_args_unfold[of _ k] unfolding subst.cop_nil by metis
      then show ?thesis using mt_cu'k_\<R>[of k "snd r" r] mt_cu'k_\<U>r[of k r]
        check_snd_r UnE[OF \<open>r \<in> (\<R> \<union> \<U>)\<close>] mctxt_term_conv_mctxt_of_term by metis
    qed
    have part4: "mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle> = D\<langle>mt_cu' k (snd r \<cdot> \<sigma>)\<rangle>"
      using part1(4) missing by blast
    have second_half: "D\<langle>snd r \<cdot> ?\<tau>'\<rangle> = mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle>"
      using part3 part3_2 part4 by (auto simp: var_subst_comp case_option_Some) 
    then have "(mt_curry C\<langle>fst r \<cdot> \<sigma>\<rangle>, mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle>) 
                                   \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p ?\<tau>'"
      using first_half rstep_s_t \<open>r \<in> (\<R> \<union> \<U>)\<close> part1(2) p_def
      by (metis rstep_r_p_s'.rstep_r_p_s' s_def_t_def(1))
    then have W: "\<exists> \<tau>. max_top_curry C\<langle>snd r \<cdot> \<sigma>\<rangle> \<in> \<LL> \<and>
                  (mctxt_term_conv ?M, mt_curry C\<langle>snd r \<cdot> \<sigma>\<rangle>)
                    \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau>"
      using Un_iff s_def_t_def max_top_curry_equiv assms(2) by auto
    then obtain \<tau> where step_to_L: "(mctxt_term_conv ?M, mctxt_term_conv 
                  (max_top_curry C\<langle>snd r \<cdot> \<sigma>\<rangle>)) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau>" by auto
    then show ?thesis using max_top_curry_correct[OF \<open>t \<in> \<T>\<close>]
      unfolding s_def_t_def(2) max_top_curry_equiv by auto
  next
    case is_var
    then have "r \<in> \<R>" using \<U>_def \<open>r \<in> (\<R> \<union> \<U>)\<close> by fastforce
    have step: "(fst r \<cdot> (mt_cu' 0 \<circ> \<sigma>), snd r \<cdot> (mt_cu' 0 \<circ> \<sigma>))
                  \<in> rstep_r_p_s' (\<R> \<union> \<U>) r [] ?\<tau>'"
      using s_def_t_def(3)
      by (metis intp_actxt.simps(1) hole_pos.simps(1) rstep_r_p_s'.simps)
    have hole: "C = Hole" using is_var by simp
    have "D = Hole" using part1(2) hole p_def by (cases D) simp+
    have "p = []" using hole p_def by simp
    then show ?thesis
    proof (cases "is_Fun (snd r \<cdot> \<sigma>)")
      case is_fun_\<sigma>: True
      then obtain g ss where term_def: "snd r \<cdot> \<sigma> = Fun g ss" by blast
      then show ?thesis
      proof (cases "check_first_non_Ap 0 (snd r \<cdot> \<sigma>)")
        case check: True
        then have mt_t: "mctxt_term_conv (max_top t) = snd r \<cdot> (mt_cu' 0 \<circ> \<sigma>)"
          using is_var max_top_curry_correct[OF \<open>t \<in> \<T>\<close>] max_top_curry_cu_equiv[of g ss] term_def
          unfolding s_def_t_def(2) hole by force
        show ?thesis using step
          unfolding first_half max_top_curry_equiv \<open>D = Hole\<close> mt_t \<open>p = []\<close> by auto
      next
        case not_check: False
        then have "max_top_cu' 0 (snd r \<cdot> \<sigma>) = MHole" using term_def by auto
        then have mt_hole: "snd r \<cdot> (mt_cu' 0 \<circ> \<sigma>) = Var None" using is_var by auto
        then show ?thesis using step
          unfolding first_half \<open>D = Hole\<close> mt_hole max_top_curry_equiv \<open>p = []\<close> by auto
      qed
    next
      case is_var_\<sigma>: False
      then obtain x where mt_x: "max_top_cu' 0 (snd r \<cdot> \<sigma>) = MVar x" by auto
      then have mt_var: "snd r \<cdot> (mt_cu' 0 \<circ> \<sigma>) = Var (Some x)"
        using is_var is_var_\<sigma> by auto
      have "max_top (snd r \<cdot> \<sigma>) = MVar x" using is_var_\<sigma> mt_x by auto
      then show ?thesis using step is_var is_var_\<sigma> mt_var
        unfolding first_half \<open>D = Hole\<close> max_top_curry_equiv
                  s_def_t_def(2) hole \<open>p = []\<close> by auto
    qed
  qed
qed

interpretation layered "\<F>\<^sub>U" "\<LL>" "\<R> \<union> \<U>"
text \<open>done (Franziska)\<close>
proof (* trs *)
  show "wf_trs (\<R> \<union> \<U>)" using wfR wfU by (auto simp: wf_trs_def)
next (* \<R>_sig *)
  show "funas_trs (\<R> \<union> \<U>) \<subseteq> \<F>\<^sub>U" using sigR sigU unfolding \<F>\<^sub>U_def by auto
next (* C1 *)
  fix p :: pos and s t :: "('f, 'v) term" and r and \<sigma>
  let ?M = "max_top s" and ?L = "max_top t"
  assume assms: "s \<in> \<T>" "t \<in> \<T>" "p \<in> fun_poss_mctxt ?M" and
         rstep_s_t: "(s, t) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<sigma>"
  then obtain C where
    s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R> \<union> \<U>" and
    p_def: "p = hole_pos C"
    by auto
  show "\<exists>\<tau>. (mctxt_term_conv ?M, mctxt_term_conv ?L) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau> \<or>
            (mctxt_term_conv ?M, mctxt_term_conv MHole) \<in> rstep_r_p_s' (\<R> \<union> \<U>) r p \<tau>"
  proof -
    consider "is_Fun s" | "is_Var s" using \<open>s \<in> \<T>\<close> \<T>_def by (cases s) auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using lemma_C\<^sub>1 assms rstep_s_t s_def_t_def p_def by auto
    next
      case 2
      have wf_RU: "wf_trs (\<R> \<union> \<U>)" using wfR wfU unfolding wf_trs_def by blast
      show ?thesis
        using rstep_s_t NF_Var[OF wf_RU] rstep_eq_rstep'
              rstep'_iff_rstep_r_p_s' prod.collapse 2 unfolding is_Var_def by metis
    qed
  qed
next (* C2 *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume assms: "N \<in> \<LL>" "L \<in> \<LL>" "L \<le> N" "p \<in> hole_poss L"
  then show "mreplace_at L p (subm_at N p) \<in> \<LL>"
  proof (cases p)
    case Nil then show ?thesis using assms by simp
  next
    case (Cons i p')
    have p_poss_N: "p \<in> all_poss_mctxt N"
      using \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> all_poss_mctxt_conv all_poss_mctxt_mono[of L N]
      by auto
    then have subN_\<LL>\<^sub>1: "\<LL>\<^sub>1 (subm_at N p)" using \<open>N \<in> \<LL>\<close> Cons by simp
    have subL_\<LL>\<^sub>1: "\<LL>\<^sub>1 (subm_at L p)" using \<open>L \<in> \<LL>\<close> \<open>p \<in> hole_poss L\<close> Cons by auto
    then have missing: "\<forall>n. missing_args (subm_at L p) n \<ge> 1
                    \<longrightarrow> missing_args (subm_at N p) n \<ge> 1"
      using \<open>p \<in> hole_poss L\<close> by simp
    consider "\<LL>\<^sub>1 L" | "\<LL>\<^sub>2 L" using \<open>L \<in> \<LL>\<close> unfolding \<LL>_def by blast
    then show ?thesis
    proof cases
      case 1
      have "\<LL>\<^sub>1 (mreplace_at L p (subm_at N p))"
        using replace_\<LL>\<^sub>1[OF \<open>\<LL>\<^sub>1 L\<close> subL_\<LL>\<^sub>1 subN_\<LL>\<^sub>1 _ missing] \<open>p \<in> hole_poss L\<close>
              all_poss_mctxt_conv by blast
      then show ?thesis unfolding \<LL>_def by simp
    next
      case 2
      then obtain C C' where L_def: "L = MFun Ap [C, C']" "\<LL>\<^sub>1 C'" using \<LL>\<^sub>2.simps[of L] by blast
      have "subm_at L p = MHole" using \<open>p \<in> hole_poss L\<close> by simp
      then have "(\<exists>f Cs. subm_at N p = MFun f Cs) \<or>
             \<LL>\<^sub>2 (mreplace_at L p (subm_at L p)) = \<LL>\<^sub>2 (mreplace_at L p (subm_at N p))"
        using p_poss_N replace_var_holes2[of p L "subm_at L p" "subm_at N p"]
              \<open>p \<in> hole_poss L\<close> all_poss_mctxt_conv[of L] by (cases "subm_at N p") blast+
      moreover have "\<LL>\<^sub>2 (mreplace_at L p (subm_at L p))"
        using 2 \<open>p \<in> hole_poss L\<close> all_poss_mctxt_conv[of L] replace_at_subm_at by fastforce
      ultimately consider "\<exists>f Cs. subm_at N p = MFun f Cs" | "\<LL>\<^sub>2 (mreplace_at L p (subm_at N p))"
        by blast
      then show ?thesis using \<LL>_def
      proof cases
        case mfun: 1
        then obtain f' Cs' where sub_N_def: "subm_at N p = MFun f' Cs'" by blast
        then show ?thesis
        proof (cases "p = [0]")
          case True
          obtain f Cs where N_def: "N = MFun f Cs" using p_poss_N unfolding Cons
            by (metis 2(1) \<LL>\<^sub>1.simps assms(3) disjoint  less_eq_mctxtE2(2) list.distinct(1)
                subm_at.elims mctxt_order_bot.bot.extremum_uniqueI)
          then have f_props: "f = Ap \<and> length Cs = 2"
            using \<LL>\<^sub>2.cases[OF 2] less_eq_mctxt_MFunE2[OF \<open>L \<le> N\<close>[unfolded N_def]]
            by (metis length_Cons mctxt.distinct(5) mctxt.inject(2) numeral_2_eq_2 list.size(3))
          moreover have "\<LL>\<^sub>1 N" using N_def f_props sub_N_def \<open>N \<in> \<LL>\<close> \<LL>\<^sub>2.cases[of N] unfolding \<LL>_def True
            by (metis mctxt.simps(6,8) mem_Collect_eq nth_Cons_0 subm_at.simps(1,2)) 
          ultimately have "missing_args (subm_at N p) (Suc 0) \<ge> 1"
            using p_poss_N sub_N_def \<LL>\<^sub>1.simps[of "MFun f Cs"] unfolding N_def True by fastforce
          then have "\<LL>\<^sub>1 (MFun Ap [subm_at N p, C'])"
            using subN_\<LL>\<^sub>1 \<LL>\<^sub>1.simps[of "MFun Ap [subm_at N p, C']"] L_def(2) f_props by blast
          then show ?thesis using \<LL>_def \<open>p \<in> hole_poss L\<close> f_props 2 \<open>L \<le> N\<close>
            unfolding True N_def L_def(1) by force
        next
          case False
          show ?thesis using replace_\<LL>\<^sub>2[OF \<open>\<LL>\<^sub>2 L\<close> subL_\<LL>\<^sub>1 subN_\<LL>\<^sub>1 _ missing] False 
            \<open>p \<in> hole_poss L\<close> all_poss_mctxt_conv by blast
        qed
      qed auto
    qed
  qed
qed

abbreviation \<T>\<^sub>\<LL> where "\<T>\<^sub>\<LL> \<equiv> { t . mctxt_of_term t \<in> \<LL> }"
abbreviation \<T>\<^sub>\<LL>\<^sub>1 where "\<T>\<^sub>\<LL>\<^sub>1 \<equiv> { t . \<LL>\<^sub>1 (mctxt_of_term t) }"
abbreviation PP\<^sub>\<R> where "PP\<^sub>\<R> \<equiv> rstep (\<R> \<union> \<U>)"

fun try_step :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "try_step (Var x) t = undefined"
| "try_step (Fun f ts) t = (if f \<noteq> Ap \<and> arity f > length ts
     then Fun f (ts @ [t]) else Fun Ap [Fun f ts, t])"

fun NF_\<U> :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "NF_\<U> (Var x) = Var x"
| "NF_\<U> (Fun f ts) = (if f = Ap \<and> length ts = 2 \<and> is_Fun (ts ! 0)
     then try_step (NF_\<U> (ts ! 0)) (NF_\<U> (ts ! 1))
     else Fun f (map NF_\<U> ts))"

lemma NF_\<U>_consistent:
  shows "is_Fun t = is_Fun (NF_\<U> t)"
proof (induction t)
  case (Fun f ts)
  then have "length ts = 2 \<and> is_Fun (ts ! 0) \<longrightarrow> is_Fun (NF_\<U> (ts ! 0))" by auto
  then show ?case by (auto split: if_splits)
qed simp

lemma fun_args_in_NF:
  assumes "\<forall>x \<in> set ts. x \<in> NF_trs R" "\<forall>t'. (Fun f ts, t') \<notin> rrstep R"
  shows "Fun f ts \<in> NF_trs R"
using assms
  by (meson Fun_supt NF_I NF_subterm rstep_args_NF_imp_rrstep)

lemma try_step_correct:
  assumes "try_step (Fun f ts) t = t'" "(Fun f ts) \<in> NF_trs \<U>" "t \<in> NF_trs \<U>"
          "(Fun f ts) \<in> \<T>" "t \<in> \<T>"
  shows "(Fun Ap [Fun f ts, t], t') \<in> (rstep \<U>)\<^sup>* \<and> t' \<in> NF_trs \<U> \<and> t' \<in> \<T>"
using assms
proof (induction "Fun f ts" t rule: try_step.induct)
  case (2 t) then show ?case
  proof (cases "f \<noteq> Ap \<and> arity f > length ts")
    case True
    then have t'_def: "t' = Fun f (ts @ [t])" using 2(1) by auto
    then have "t' \<in> \<T>" using True 2(4,5) \<T>_def \<F>\<^sub>U_def unfolding arity_def by fastforce
    obtain x :: 'v where inf: "infinite (UNIV - (vars_term t' \<union> { x }))" "x \<notin> vars_term t'"
      using infinite_UNIV
      by (metis UNIV_eq_I Un_commute finite_Diff2 finite_insert finite_vars_term insert_is_Un)
    obtain ts' :: "'v list" where ts'_props:
        "(\<forall>t\<^sub>i\<in>set ts'. is_Var (Var t\<^sub>i))" "length ts' = length ts" "distinct (ts' @ [x])"
        "set ts' \<inter> vars_term t' = {}"
      using infinite_imp_many_elems[OF inf(1), of "length ts"] by auto
    let ?vars = "map Var ts'"
    have vars_props: "(\<forall>t\<^sub>i\<in>set ?vars. is_Var t\<^sub>i)" "length ?vars = length ts"
                     "distinct (?vars @ [Var x])"
      using ts'_props distinct_map_Var by auto
    moreover obtain n where arity_f: "(f, n) \<in> \<F>" "n > length ts"
      using True 2(4) unfolding layer_system_sig.\<T>_def \<F>\<^sub>U_def \<F>_def arity_def by fastforce
    ultimately obtain r where r_def:
      "r = (Fun Ap [Fun f ?vars, Var x], Fun f (?vars @ [Var x])) \<and> r \<in> \<U>"
        using \<U>_def by fastforce
    let ?\<sigma> = "subst_of (zip (x # ts') (t # ts))"
    have dom1: "subst_domain (subst x t) = { x }"
      using subst_domain_def \<open>x \<notin> vars_term t'\<close> unfolding t'_def by force
    have ts'_ts_distinct: "set ts' \<inter>  (\<Union>x\<in>set ts. vars_term x) = {}"
      using ts'_props(4) t'_def by auto
    { fix i
      assume "i < length ts'"
      then have "subst_of (zip ts' ts) (ts' ! i) = ts ! i"
        using ts'_props(2,3) ts'_ts_distinct
        proof (induction ts' ts arbitrary: i rule: zip_induct)
          case (Cons_Cons a' ts' a ts) then show ?case
          proof (cases i)
            case 0
            have "subst_domain (subst_of (zip ts' ts)) \<subseteq> set ts'"
              using subst_domain_subst_of[of "zip ts' ts"] map_fst_zip[of ts' ts] Cons_Cons(3)
              by fastforce
            then have "subst_of (zip ts' ts) a' = Var a'"
              using Cons_Cons(3,4) notin_subst_domain_imp_Var[of a'] by auto
            then show ?thesis using Cons_Cons(2-) unfolding 0
              by (auto simp: subst_compose_def)
            term  "(subst_of (zip ts' ts) a') \<cdot> subst a' a"
          next
            case (Suc n)
            then have "subst_of (zip ts' ts) (ts' ! n) = ts ! n"
              using Cons_Cons(1)[of n] Cons_Cons(2-) by auto
            then show ?thesis using Cons_Cons(2-) unfolding Suc
              by (simp add: subst_compose_def)
          qed
        qed auto
    } note maps = this
    have dom2: "subst_domain (subst_of (zip ts' ts)) \<subseteq> set ts'"
      using subst_domain_subst_of[of "zip ts' ts"] map_fst_zip[of ts' ts] ts'_props(2)
      by fastforce
    then have "(Var x) \<cdot> (subst_of (zip ts' ts)) = (Var x)"
      using vars_props notin_subst_domain_imp_Var[of x "subst_of (zip ts' ts)"] by auto
    moreover have "map (\<lambda>x. x \<cdot> (subst_of (zip ts' ts))) ?vars = ts"
      using maps vars_props(2) by (simp add: map_nth_eq_conv)
    then have "map (\<lambda>x. x \<cdot> ?\<sigma>) ?vars = ts"
      using vars_props(2) ts'_props(3) notin_subst_domain_imp_Var[of "ts' ! _" "subst x t"]
        \<open>x \<notin> vars_term t'\<close> unfolding dom1 t'_def
      by (auto simp: map_nth_eq_conv)
    moreover have "(\<lambda>x. x \<cdot> \<sigma> \<cdot> \<tau>) \<circ> Var = (\<lambda>t. t \<cdot> \<tau>) \<circ> ((\<lambda>t. t \<cdot> \<sigma>) \<circ> Var)"
      for \<sigma> \<tau> :: "('f, 'v) subst" by auto
    ultimately have "(Fun Ap [Fun f ts, t], t') \<in> rstep_r_p_s \<U> r [] ?\<sigma>"
      using r_def vars_props unfolding t'_def rstep_r_p_s_def by force
    then have reach:"(Fun Ap [Fun f ts, t], t') \<in> (rstep \<U>)\<^sup>*"
      using rrstep_imp_rstep rstep_r_p_s_imp_rstep[of _ _ \<U> r "[]" ?\<sigma>] by fastforce
    { fix i
      assume "i < length (ts @ [t])"
      then have "(ts @ [t]) ! i \<in> NF_trs \<U>" using 2(3) NF_subterm[OF 2(2), of "ts ! i"]
        by (cases "i = length ts") (auto simp: append_Cons_nth_left)
    } note args_NF = this
    { assume "\<exists>u. (t', u) \<in> rstep \<U>"
      then obtain u where step: "(t', u) \<in> rstep \<U>" by blast
      have "(t', u) \<in> rrstep \<U>"
        using rstep_args_NF_imp_rrstep[OF step] args_NF supt_Fun_imp_arg_supteq[of f "ts @ [t]"]
              in_set_idx[of _ "ts @ [t]"] NF_subterm[of "(ts @ [t]) ! _" \<U>]
        unfolding t'_def by metis
      then obtain l r \<sigma> where rule_subst: "(l, r) \<in> \<U> \<and> t' = l\<cdot>\<sigma> \<and> u = r\<cdot>\<sigma>"
        unfolding rrstep_def' by fast
      then obtain f' ts' x where "l = Fun Ap [Fun f' ts', x]" "r = Fun f' (ts' @ [x])"
        using \<U>_def by force
      then have False using rule_subst True unfolding t'_def by simp
    }
    then have "t' \<in> NF_trs \<U>" by auto
    then show ?thesis using reach \<open>t' \<in> \<T>\<close> by blast
  next
    case False
    then have t'_def: "t' = Fun Ap [Fun f ts, t]" using 2 by force
    then have "t' \<in> \<T>" using 2(4,5) \<T>_def \<F>\<^sub>U_def by auto
    moreover {
      assume "\<exists>u. (t', u) \<in> rstep \<U>"
      then obtain u where step: "(t', u) \<in> rstep \<U>" by blast
      have "(t', u) \<in> rrstep \<U>"
        using rstep_args_NF_imp_rrstep[OF step] 2(1-3) supt_Fun_imp_arg_supteq[of Ap "[Fun f ts, t]"]
              in_set_idx[of "[Fun f ts, t] ! _" "[Fun f ts, t]"] NF_subterm[of _ \<U>]
        unfolding t'_def by (metis in_set_simps(1,2))
      then obtain l r \<sigma> where rule_subst: "(l, r) \<in> \<U> \<and> t' = l\<cdot>\<sigma> \<and> u = r\<cdot>\<sigma>"
        unfolding rrstep_def' by fast
      then obtain f' ts' x n where "l = Fun Ap [Fun f' ts', x]" "r = Fun f' (ts' @ [x])"
                                   "(f', n) \<in> \<F>" "length ts' < n"
        using \<U>_def by force
      then have False using rule_subst False fresh unfolding t'_def \<F>_def arity_def by simp
    }
    ultimately show ?thesis unfolding t'_def by blast
  qed
qed

lemma try_step_persists_r:
  shows "\<exists>D. try_step (Fun f ts) t = D\<langle>t\<rangle> \<and> (\<forall>s. try_step (Fun f ts) s = D\<langle>s\<rangle>)"
proof -
  let ?D = "More Ap [Fun f ts] \<box> []"
  have "?D\<langle>t\<rangle> = Fun Ap [Fun f ts, t] \<and> (\<forall>s. ?D\<langle>s\<rangle> = Fun Ap [Fun f ts, s])" by simp
  then have "\<exists>D. D\<langle>t\<rangle> = Fun Ap [Fun f ts, t] \<and> (\<forall>s. D\<langle>s\<rangle> = Fun Ap [Fun f ts, s])" by blast
  moreover have "\<exists>D. D\<langle>t\<rangle> = Fun f (ts @ [t]) \<and> (\<forall>s. D\<langle>s\<rangle> = Fun f (ts @ [s]))"
    by (metis intp_actxt.simps(1,2))
  ultimately show ?thesis by auto
qed

lemma NF_\<U>_persists:
  assumes "\<forall>C' f ss2. C = C' \<circ>\<^sub>c (More f [] \<box> ss2) \<longrightarrow> f \<noteq> Ap"
  shows "\<exists>D. NF_\<U> C\<langle>t\<rangle> = D\<langle>NF_\<U> t\<rangle> \<and>
            (\<forall>s. NF_\<U> C\<langle>s\<rangle> = D\<langle>NF_\<U> s\<rangle>)"
proof (cases C rule: ctxt_exhaust_rev)
  case (More D f ss1 ss2)
    let ?D' = "\<lambda>x. More f (map NF_\<U> ss1) \<box> (map NF_\<U> ss2 @ x)"
    have "\<exists>g tt1 tt2. NF_\<U> (Fun f (ss1 @ t # ss2)) = (More g tt1 \<box> tt2)\<langle>NF_\<U> t\<rangle> \<and>
         (\<forall>s. NF_\<U> (Fun f (ss1 @ s # ss2)) = (More g tt1 \<box> tt2)\<langle>NF_\<U> s\<rangle>)"
    proof (cases ss1)
      case Nil
      then have "f \<noteq> Ap" using More assms by blast
      then show ?thesis using Nil by auto
    next
      case (Cons a ls) then show ?thesis
      proof (cases "f = Ap \<and> length (ss1 @ t # ss2) = 2 \<and> is_Fun ((ss1 @ t # ss2) ! 0)")
        case True
        then obtain g ss where NF_a: "NF_\<U> a = Fun g ss" using NF_\<U>_consistent[of a] Cons by auto
        show ?thesis using True NF_a unfolding Cons
          by auto (metis append_Cons append_Nil)+
      next
        case False
        then show ?thesis unfolding Cons
          by (simp split: if_splits) (metis append_Cons)+
      qed
    qed
    then show ?thesis unfolding More Nil
    proof (induction D)
      case Hole_D: Hole then show ?case
        by (metis actxt_compose.simps(1) intp_actxt.simps(1,2))
    next
      case More_D: (More f' ss1' D' ss2')
      then obtain E' where inner: "NF_\<U> (D' \<circ>\<^sub>c More f ss1 \<box> ss2)\<langle>t\<rangle> = E'\<langle>NF_\<U> t\<rangle> \<and>
                              (\<forall>s. NF_\<U> (D' \<circ>\<^sub>c More f ss1 \<box> ss2)\<langle>s\<rangle> = E'\<langle>NF_\<U> s\<rangle>)"
        by blast
      then obtain g tt1 F tt2 where E'_def: "E' = More g tt1 F tt2"
        by (cases E') (auto, metis NF_\<U>.simps(1) NF_\<U>_consistent
          ctxt_apply_eq_False intp_actxt.simps(2) is_VarE is_VarI)
      let ?ts = "\<lambda>t. ss1' @ D'\<langle>Fun f (ss1 @ t # ss2)\<rangle> # ss2'"
      have is_Fun_persists: "is_Fun (?ts t ! 0) = is_Fun (?ts s ! 0)" for s
        by (cases ss1', cases D') auto
      show ?case
      proof (cases "f' = Ap \<and> length (?ts t) = 2 \<and> is_Fun (?ts t ! 0)")
        case step: True
        then consider "ss1' = []" | "\<exists>a. ss1' = [a]"
          by simp (metis length_0_conv length_Suc_conv one_is_add)
        then have "\<exists>D. try_step (NF_\<U> ((ss1' @ D'\<langle>Fun f (ss1 @ t # ss2)\<rangle> # ss2') ! 0))
           (NF_\<U> ((ss1' @ D'\<langle>Fun f (ss1 @ t # ss2)\<rangle> # ss2') ! Suc 0)) =
          D\<langle>NF_\<U> t\<rangle> \<and> (\<forall>s. try_step (NF_\<U> ((ss1' @ D'\<langle>Fun f (ss1 @ s # ss2)\<rangle> # ss2') ! 0))
           (NF_\<U> ((ss1' @ D'\<langle>Fun f (ss1 @ s # ss2)\<rangle> # ss2') ! Suc 0)) =
          D\<langle>NF_\<U> s\<rangle>)"
        proof cases
          case 1
          then show ?thesis using inner is_Fun_persists E'_def
            by (auto split: if_splits) (metis intp_actxt.simps(2),
               (metis (no_types) append.left_neutral intp_actxt.simps(2))+)
        next
          case 2
          then obtain a where ss1'_def: "ss1' = [a]" by blast
          then have a1: "is_Fun (NF_\<U> a)" using step NF_\<U>_consistent[of a] by auto
          then obtain g' ss where NF_fun: "NF_\<U> a = Fun g' ss" by blast
          then obtain E'' where try_1: "try_step (Fun g' ss) (Fun g (tt1 @ F\<langle>NF_\<U> t\<rangle> # tt2)) =
              E''\<langle>Fun g (tt1 @ F\<langle>NF_\<U> t\<rangle> # tt2)\<rangle> \<and> (\<forall>s. try_step (Fun g' ss) s = E''\<langle>s\<rangle>)"
            using try_step_persists_r[of g' ss "Fun g (tt1 @ F\<langle>NF_\<U> _\<rangle> # tt2)"]
              by blast
          let ?D = "E'' \<circ>\<^sub>c E'"
          have try_2: "try_step (NF_\<U> a) (Fun g (tt1 @ F\<langle>NF_\<U> t\<rangle> # tt2)) = ?D\<langle>NF_\<U> t\<rangle> \<and>
               (\<forall>s. try_step (NF_\<U> a) (Fun g (tt1 @ F\<langle>NF_\<U> s\<rangle> # tt2)) = ?D\<langle>NF_\<U> s\<rangle>)"
            using try_1 unfolding E'_def NF_fun by simp
          show ?thesis using inner E'_def try_2 NF_fun unfolding ss1'_def
            by simp (metis NF_fun try_1 try_2)
        qed
        then show ?thesis using step is_Fun_persists by auto
      next
        case no_step: False
        then show ?thesis using inner is_Fun_persists
          by (auto split: if_splits) (metis intp_actxt.simps(2))+
      qed
    qed
qed (metis ctxt.cop_nil)

lemma NF_\<U>_correct:
  assumes "NF_\<U> t = t'" "t \<in> \<T>"
  shows "(t, t') \<in> (rstep \<U>)\<^sup>* \<and> t' \<in> NF_trs \<U> \<and> t' \<in> \<T>"
using assms
proof (induction t arbitrary: t' rule: NF_\<U>.induct)
  case (1 x)
  then show ?case using NF_I no_Var_rstep[OF wfU, of x] by fastforce
next
  case (2 f ts) then show ?case
  proof (cases "f = Ap \<and> length ts = 2 \<and> is_Fun (ts ! 0)")
    case use_try_step: True
    then have "ts ! 0 \<in> \<T>" "ts ! 1 \<in> \<T>" using \<T>_subt_at[OF 2(5), of "[_]"] by simp+
    then obtain g ss where NF_ts0: "NF_\<U> (ts ! 0) = Fun g ss"
      using NF_\<U>_consistent use_try_step by blast
    then have NF_ts_props: "(ts ! 0, Fun g ss) \<in> (rstep \<U>)\<^sup>*" "(ts ! 1, NF_\<U> (ts ! 1)) \<in> (rstep \<U>)\<^sup>*"
                        "Fun g ss \<in> NF_trs \<U>" "NF_\<U> (ts ! 1) \<in> NF_trs \<U>"
                        "Fun g ss \<in> \<T>" "NF_\<U> (ts ! 1) \<in> \<T>"
      using 2(1)[OF use_try_step NF_ts0 \<open>ts ! 0 \<in> \<T>\<close>] 2(2)[OF use_try_step _ \<open>ts ! 1 \<in> \<T>\<close>]
      by blast+
    { fix i
        assume "i < length [ts ! 0, ts ! 1]"
        then have "([ts ! 0, ts ! 1] ! i, [Fun g ss, NF_\<U> (ts ! 1)] ! i) \<in> (rstep \<U>)\<^sup>*"
          using NF_ts_props(1,2) less_2_cases[of i] by force
    }
    then have inner_steps: "\<forall>i<length [ts ! 0, ts ! 1].
       ([ts ! 0, ts ! 1] ! i, [Fun g ss, NF_\<U> (ts ! 1)] ! i) \<in> (rstep \<U>)\<^sup>*" by blast
    then have first_part: "(Fun Ap [ts ! 0, ts ! 1], Fun Ap [Fun g ss, NF_\<U> (ts ! 1)]) \<in> (rstep \<U>)\<^sup>*"
      using use_try_step args_rsteps_imp_rsteps[OF _ inner_steps, of Ap]
      by fastforce
    moreover have "(Fun Ap [Fun g ss, NF_\<U> (ts ! 1)], t') \<in> (rstep \<U>)\<^sup>* \<and> t' \<in> NF_trs \<U> \<and> t' \<in> \<T>"
      using try_step_correct[OF _ NF_ts_props(3-)] use_try_step NF_ts0
      unfolding 2(4)[symmetric] by force
    moreover have "Fun f ts = Fun Ap [ts ! 0, ts ! 1]"
      using use_try_step by simp (metis Cons_nth_drop_Suc Suc_leI drop_all lessI nth_drop_0
                                  numeral_2_eq_2 one_add_one zero_less_two)
    ultimately show ?thesis by fastforce
  next
    case False
    then have t'_def: "t' = Fun f (map NF_\<U> ts)"
      using False unfolding 2(4)[symmetric] by force
    have "\<forall>x \<in> set ts. x \<in> \<T>" using \<T>_subt_at[OF 2(5), of "[_]"] in_set_idx[of _ ts] by auto
    then have "\<forall>u\<lhd>t'. u \<in> NF_trs \<U>" using 2(3)[OF False, of _ "NF_\<U> _"]
      unfolding t'_def by fastforce
    then have "\<exists>t''. (t', t'') \<in> rstep \<U> \<longrightarrow> (t', t'') \<in> rrstep \<U>"
      by (simp add: rstep_args_NF_imp_rrstep)
    let ?ts = "map NF_\<U> ts"
    { fix x s :: "('f, 'v) term"
      assume assms: "\<exists>t''. (Fun f ?ts, t'') \<in> rrstep \<U>"
      then obtain t'' where "(Fun f ?ts, t'') \<in> rrstep \<U>" by blast
      then obtain r \<sigma> where to_t'': "(Fun f ?ts, t'') \<in> rstep_r_p_s \<U> r [] \<sigma>"
        unfolding rrstep_def by fast
      then obtain f' ts' y where r_def: "r = (Fun Ap [Fun f' ts', y], Fun f' (ts' @ [y]))"
        using \<U>_def by (auto simp: rstep_r_p_s_eq_rstep_r_p_s')
      have "Fun Ap [Fun f' ts', y] \<cdot> \<sigma> = Fun f ?ts"
        using to_t'' unfolding rstep_r_p_s_def r_def by simp
      then have False using False NF_\<U>_consistent[of "ts ! 0"] by force
    } note no_rrstep = this
    moreover have args_props: 
      "x \<in> set ts \<longrightarrow> (x, NF_\<U> x) \<in> (rstep \<U>)\<^sup>* \<and> NF_\<U> x \<in> NF_trs \<U> \<and> NF_\<U> x \<in> \<T>" for x
      using 2(3)[OF False, of _ "NF_\<U> _"] \<open>\<forall>x \<in> set ts. x \<in> \<T>\<close> by blast
    ultimately have "Fun f (map NF_\<U> ts) \<in> NF_trs \<U>"
      using fun_args_in_NF[of "map NF_\<U> ts" \<U> f] by fastforce
    moreover have "(Fun f ts, Fun f (map NF_\<U> ts)) \<in> (rstep \<U>)\<^sup>*"
      using args_props args_rsteps_imp_rsteps[of ts ?ts \<U> f] by simp
    moreover have "Fun f (map NF_\<U> ts) \<in> \<T>"
      using args_props 2(5) \<T>_def mem_Collect_eq by auto
    ultimately show ?thesis unfolding t'_def by blast
  qed
qed

lemma NF_\<U>_Cu_subst:
  assumes "funas_term t \<subseteq> \<F>"
  shows "NF_\<U> (Cu t \<cdot> \<sigma>) = t \<cdot> (NF_\<U> \<circ> \<sigma>)"
using assms
proof (induction t)
  case (Fun f ts)
  have arity_f: "arity f \<ge> length ts" using Fun(2) \<F>_def arity_def by force
  show ?case
  proof (cases "f = Ap")
    case isAp: True
    then show ?thesis using Fun(2) fresh unfolding \<F>_def by fastforce
  next
    case notAp: False
    have "x \<in> set ts \<Longrightarrow> NF_\<U> (Cu x \<cdot> \<sigma>) = x \<cdot> (NF_\<U> \<circ> \<sigma>)" for x
      using Fun by fastforce
    then show ?thesis using arity_f
    proof (induction "length ts" arbitrary: ts)
      case (Suc n)
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
      have Cu_unfold: "Cu (Fun f ts) = Fun Ap [Cu (Fun f ts'), Cu a]"
        using notAp unfolding ts_def by simp
      have args: "NF_\<U> (Cu (Fun f ts') \<cdot> \<sigma>) = Fun f ts' \<cdot> (NF_\<U> \<circ> \<sigma>)"
                 "NF_\<U> (Cu a \<cdot> \<sigma>) = a \<cdot> (NF_\<U> \<circ> \<sigma>)"
        using Suc(1)[of ts'] Suc(2-) unfolding ts_def by force+
      have "is_Fun (Cu (Fun f ts') \<cdot> \<sigma>)" by (cases ts') simp+ 
      then have NF_\<U>_unfold: "NF_\<U> (Cu (Fun f ts) \<cdot> \<sigma>) =
                          try_step (Fun f ts' \<cdot> (NF_\<U> \<circ> \<sigma>)) (a \<cdot> (NF_\<U> \<circ> \<sigma>))"
        using args notAp unfolding Cu_unfold by simp
      have "arity f > length ts'" using Suc(4) ts_def by simp
      then have "try_step (Fun f ts' \<cdot> (NF_\<U> \<circ> \<sigma>)) (a \<cdot> (NF_\<U> \<circ> \<sigma>)) = Fun f ts \<cdot> (NF_\<U> \<circ> \<sigma>)"
        using notAp unfolding ts_def by simp
      then show ?case unfolding NF_\<U>_unfold by argo
    qed simp
  qed
qed simp

lemma NF_\<U>_Cu:
  assumes "funas_term t \<subseteq> \<F>"
  shows "NF_\<U> (Cu t) = t"
using NF_\<U>_Cu_subst[OF assms, of Var]
  by (simp add: term_subst_eq)

lemma \<T>_closed_under_PP\<^sub>\<R>:
  assumes "t \<in> \<T>" "(t, t') \<in> PP\<^sub>\<R>\<^sup>*"
  shows "t' \<in> \<T>"
using rsteps_preserve_funas_terms[OF \<R>_sig _ assms(2)] assms(1)[unfolded \<T>_def] \<T>_def
  by (simp add: trs)

lemma vars_term_partition:
 assumes "\<forall>t\<^sub>i\<in>set ts. is_Var t\<^sub>i" "distinct ts"
 shows "is_partition (map vars_term ts)"
using assms
proof (induction ts)
  case (Cons a ts)
  then have part_ts: "is_partition (map vars_term ts)" by force
  then show ?case using Cons(2-) is_partition_Cons by fastforce
qed (auto simp: is_partition_def)

lemma is_partition_merge:
  assumes "is_partition (ls @ [a])"
  shows "is_partition [\<Union>x\<in>set ls. x, a]"
using assms by (induction ls) (auto simp: is_partition_Cons)

lemma linear_\<U>: "linear_trs \<U>"
proof -
  { fix r
    assume "r \<in> \<U>"
    then obtain f ts t where r_def: "r = (Fun Ap [Fun f ts, t], Fun f (ts @ [t]))"
        "is_Var t" "\<forall>t\<^sub>i\<in>set ts. is_Var t\<^sub>i" "distinct (ts @ [t])"
      using \<U>_def by (auto simp: rstep_r_p_s_eq_rstep_r_p_s')
    { fix t :: "('f, 'v) term"
      assume "is_Var t"
      then have "linear_term t" by fastforce
    } note var_linear = this
    have partition1: "is_partition (map vars_term ts)"
      using r_def(3,4) vars_term_partition[of "ts"] by simp
    have partition2: "is_partition (map vars_term (ts @ [t]))"
      using r_def vars_term_partition[of "ts @ [t]"] by simp
    then have "linear_term (Fun f (ts @ [t]))"
      using r_def(2,3) var_linear by simp
    moreover have "linear_term (Fun Ap [Fun f ts, t])"
      using r_def(2,3) var_linear partition1 partition2
        is_partition_merge[of "map vars_term ts" "vars_term t"] by auto
    ultimately have "linear_term (fst r) \<and> linear_term (snd r)"
      using r_def(1) by auto
  }
  then show ?thesis unfolding linear_trs_def by force
qed

lemma trivial_cps_\<U>:
  assumes st_step: "(s, t) \<in> rstep_r_p_s \<U> (l, r) p \<sigma>" and
          su_step: "(s, u) \<in> rstep_r_p_s \<U> (l', r') p' \<sigma>'" and
          p'_def: "p' = p @ q" and
          fp: "q \<in> fun_poss l"
  shows "u = t"
proof -
  obtain f ts x n where rule1_def: "l = Fun Ap [Fun f ts, x]" "r = Fun f (ts @ [x])"
      "(f, n) \<in> \<F>" "is_Var x" "\<forall>t\<^sub>i\<in>set ts. is_Var t\<^sub>i" "distinct (ts @ [x])"
    using \<U>_def st_step by (auto simp: rstep_r_p_s_eq_rstep_r_p_s')
  have "f \<noteq> Ap" using fresh rule1_def(3) unfolding \<F>_def by fastforce
  obtain g ss where l_q: "l |_ q = Fun g ss" using fp fun_poss_fun_conv by blast
  moreover obtain C where "C\<langle>l \<cdot> \<sigma>\<rangle> = s" "hole_pos C = p"
    using hole_pos_ctxt_of_pos_term[of p s]
      Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]]
    unfolding fst_conv by meson
  ultimately obtain ss' where s_p': "s |_ p' = Fun g ss'" 
    using fun_poss_imp_poss[OF fp] unfolding p'_def by auto
  obtain f' ts' x' where rule2_def: "l' = Fun Ap [Fun f' ts', x']" "r' = Fun f' (ts' @ [x'])"
    using \<U>_def su_step by (auto simp: rstep_r_p_s_eq_rstep_r_p_s')
  then show ?thesis
  proof (cases q)
    case Nil
    then have "g = Ap" using l_q rule1_def(1) by simp
    have "p' = p" using Nil p'_def by simp
    have "l \<cdot> \<sigma> = l' \<cdot> \<sigma>'" using  ctxt_eq[of _ "l \<cdot> \<sigma>" "l' \<cdot> \<sigma>'"]
        Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]]
        Product_Type.Collect_case_prodD[OF su_step[unfolded rstep_r_p_s_def]]
      unfolding \<open>p' = p\<close> fst_conv by metis
    then show ?thesis using Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]]
        Product_Type.Collect_case_prodD[OF su_step[unfolded rstep_r_p_s_def]]
      unfolding \<open>p' = p\<close> rule1_def(1,2) rule2_def(1,2) by auto (metis (no_types, lifting))
  next
    case (Cons i q')
    then have "i = 0" using rule1_def fp less_2_cases[of i] by force
    moreover have "q' = []" using rule1_def fp unfolding Cons \<open>i = 0\<close>
      by auto (fastforce dest: nth_mem)
    ultimately have "q = [0]" unfolding Cons by blast
    then have "g = f" using rule1_def(1) l_q by auto
    have "l' \<cdot> \<sigma>' = Fun f ss'"
      using s_p' Product_Type.Collect_case_prodD[OF su_step[unfolded rstep_r_p_s_def]]
        subt_at_ctxt_of_pos_term[of "p @ [0]" s "l' \<cdot> \<sigma>'"]
      unfolding \<open>g = f\<close> \<open>q = [0]\<close> p'_def fst_conv by metis
    then show ?thesis using rule2_def(1) \<open>f \<noteq> Ap\<close> by simp
  qed
qed

lemma \<U>_commutes:
  assumes "(s, t) \<in> rstep \<U>" "(s, u) \<in> rstep \<U>"
  shows "\<exists>v. (t, v) \<in> (rstep \<U>)\<^sup>= \<and> (u, v) \<in> (rstep \<U>)\<^sup>="
proof -
  obtain l r p \<sigma> where st_step: "(s, t) \<in> rstep_r_p_s \<U> (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of s t \<U>] assms(1) by blast
  obtain l' r' p' \<sigma>' where su_step: "(s, u) \<in> rstep_r_p_s \<U> (l', r') p' \<sigma>'"
    using rstep_iff_rstep_r_p_s[of s u \<U>] assms(2) by blast+
  consider "p \<bottom> p'" | "p \<le>\<^sub>p p'" | "p' \<le>\<^sub>p p"
    using parallel_pos[of p p'] by blast
  then show ?thesis
  proof cases
    case parallel: 1
    then show ?thesis using parallel_steps[OF st_step su_step]
      by (blast dest: rstep_r_p_s_imp_rstep[of _ _ \<U>]) 
  next
    case p'_below_p: 2
    then obtain q where p'_def: "p' = p @ q" using less_eq_pos_def by auto
    then show ?thesis
    proof (cases "q \<in> fun_poss l")
      case fp: True
      have "u = t" using trivial_cps_\<U>[OF st_step su_step p'_def fp] .
      then show ?thesis by blast
    next
      case vp: False then show ?thesis
        using linear_variable_overlap_commute[OF st_step su_step p'_def _ linear_\<U>] by blast 
    qed
  next
    case p_below_p': 3
    then obtain q where p_def: "p = p' @ q" using less_eq_pos_def by auto
    then show ?thesis
    proof (cases "q \<in> fun_poss l'")
    case fp: True
      then have "u = t" using trivial_cps_\<U>[OF su_step st_step p_def fp] by simp
      then show ?thesis by blast
    next
      case vp: False then show ?thesis
        using linear_variable_overlap_commute[OF su_step st_step p_def _ linear_\<U>] by blast
    qed
  qed
qed

lemma diamond_\<U>':
  shows "\<diamond> ((rstep \<U>)\<^sup>=)"
using \<U>_commutes by (auto simp: diamond_def)

lemma CR_\<U>:
  shows "CR (rstep \<U>)"
using diamond_imp_CR'[OF diamond_\<U>', of "rstep \<U>"] by blast

lemma NF_\<U>_unique:
  assumes "t \<in> NF_trs \<U>" "t' \<in> NF_trs \<U>" "(s, t) \<in> (rstep \<U>)\<^sup>*" "(s, t') \<in> (rstep \<U>)\<^sup>*"
  shows "t = t'"
using assms CR_divergence_imp_join[OF CR_\<U> assms(3,4)] join_NF_imp_eq[of t t'] by auto

lemma NF_\<U>_in_subst:
  assumes "funas_term t \<subseteq> \<F>"
  shows "NF_\<U> (t \<cdot> \<sigma>) = t \<cdot> (NF_\<U> \<circ> \<sigma>)"
using assms
proof (induction t)
  case (Fun f ts)
  { fix x
    assume "x \<in> set ts"
    then have "NF_\<U> (x \<cdot> \<sigma>) = x \<cdot> (NF_\<U> \<circ> \<sigma>)" using Fun by fastforce
  } note inner = this
  then obtain ts' where ts'_props: "Fun f ts \<cdot> \<sigma> = Fun f ts'" "length ts' = length ts"
    by simp
  then show ?case
  proof (cases "f = Ap \<and> length ts' = 2 \<and> is_Fun (ts' ! 0)")
    case True
    then show ?thesis using Fun(2) fresh unfolding \<F>_def by fastforce
  next
    case False
    then show ?thesis using ts'_props inner
      by (auto simp: term_subst_eq_conv)
  qed
qed simp

lemma NF_\<U>_\<R>_step_persists:
  assumes "(s, t) \<in> rstep \<R>" "NF_\<U> s = s'" "NF_\<U> t = t'" "s \<in> \<T>" "\<LL>\<^sub>1 (mctxt_of_term s)"
  shows "(s', t') \<in> rstep \<R>"
proof -
  obtain C l r \<sigma> where s_def: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t_def: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and in_\<R>: "(l, r) \<in> \<R>"
    using assms(1) by auto
  have "l \<cdot> \<sigma> \<in> \<T>" using \<T>_subt_at[OF assms(4), of "hole_pos C"] unfolding s_def by simp
  then have "r \<cdot> \<sigma> \<in> \<T>" using \<T>_closed_under_PP\<^sub>\<R>[of "l \<cdot> \<sigma>" "r \<cdot> \<sigma>"] in_\<R> by auto
  have funas: "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>" using in_\<R> sigR
    unfolding funas_trs_def funas_rule_def \<F>_def by fastforce+
  then have NFs: "NF_\<U> (l \<cdot> \<sigma>) = l \<cdot> (NF_\<U> \<circ> \<sigma>)" "NF_\<U> (r \<cdot> \<sigma>) = r \<cdot> (NF_\<U> \<circ> \<sigma>)"
    using NF_\<U>_in_subst funas by blast+
  then have step: "(NF_\<U> (l \<cdot> \<sigma>), NF_\<U> (r \<cdot> \<sigma>)) \<in> rstep \<R>" using in_\<R> by auto
  obtain f ts where l_def: "l = Fun f ts" using in_\<R> wfR unfolding wf_trs_def
    by fastforce
  then have "f \<noteq> Ap" "arity f = length ts" using in_\<R> sigR fresh
    unfolding arity_def funas_trs_def funas_rule_def by fastforce+
  moreover obtain ts' where l\<sigma>_def: "l \<cdot> \<sigma> = Fun f ts'" "length ts' = length ts"
    using l_def by auto
  ultimately have check_l\<sigma>: "\<not> check_first_non_Ap 1 (l \<cdot> \<sigma>)" by auto
  { fix C' f' ss1 ss2
    assume "C = C' \<circ>\<^sub>c More f' [] \<box> ss2"
    then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (Fun f' ([] @ l \<cdot> \<sigma> # ss2)))"
      using assms(5) subm_at_layers[of "mctxt_of_term s" "hole_pos C'"] unfolding s_def \<LL>_def
      by simp (metis hole_pos_poss list.simps(9) mctxt_of_term.simps(2)
         subm_at.simps(1) subm_at_mctxt_of_term subt_at_hole_pos)
    have "f' \<noteq> Ap" using \<LL>\<^sub>1.cases[OF in_\<LL>\<^sub>1] check_l\<sigma> fresh
      unfolding missing_args_unfold[symmetric] \<F>\<^sub>U_def by simp ((cases "f' = Ap"), fastforce)
  }
  then have no_Ap_above: "\<forall>C' f ss2. C = C' \<circ>\<^sub>c More f [] \<box> ss2 \<longrightarrow> f \<noteq> Ap"
    by blast
  obtain D where "NF_\<U> s = D\<langle>NF_\<U> (l \<cdot> \<sigma>)\<rangle> \<and> NF_\<U> t = D\<langle>NF_\<U> (r \<cdot> \<sigma>)\<rangle>"
    using NF_\<U>_persists[OF no_Ap_above]
    unfolding s_def t_def by blast
  then show ?thesis using step unfolding assms(2,3)[symmetric] NFs s_def t_def
    unfolding intp_actxt.simps by force
qed

lemma uncurried_NF:
  assumes "(s, t) \<in> PP\<^sub>\<R>" "s \<in> \<T>" "t \<in> \<T>" "\<LL>\<^sub>1 (mctxt_of_term s)"
  shows "(NF_\<U> s, NF_\<U> t) \<in> (rstep \<R>)\<^sup>="
proof -
  have NFs_props: "(s, NF_\<U> s) \<in> (rstep \<U>)\<^sup>* \<and> NF_\<U> s \<in> NF_trs \<U> \<and> NF_\<U> s \<in> \<T>"
    using NF_\<U>_correct[OF _ assms(2)] by blast
  have NFt_props: "(t, NF_\<U> t) \<in> (rstep \<U>)\<^sup>* \<and> NF_\<U> t \<in> NF_trs \<U> \<and> NF_\<U> t \<in> \<T>"
    using NF_\<U>_correct[OF _ assms(3)] by blast
  consider "(s, t) \<in> rstep \<U>" | "(s, t) \<in> rstep \<R>" using assms(1) by fast
  then show ?thesis
  proof cases
    case \<U>_step : 1
    then have "(s, NF_\<U> t) \<in> (rstep \<U>)\<^sup>* \<and> NF_\<U> t \<in> NF_trs \<U>" using NFt_props by fastforce
    then have "NF_\<U> s = NF_\<U> t" using NFs_props NF_\<U>_unique[of "NF_\<U> s" "NF_\<U> t" s] by blast
    then show ?thesis by auto
  next
    case \<R>_step: 2
    then show ?thesis using NF_\<U>_\<R>_step_persists[OF \<R>_step _ _ assms(2,4)] by blast
  qed
qed


lemma rstep_r_p_s_Var_Some: "(s, t) \<in> rstep_r_p_s R (l, r) p \<sigma> \<Longrightarrow>
  (mctxt_term_conv (mctxt_of_term s), mctxt_term_conv (mctxt_of_term t))
 \<in> rstep_r_p_s' R (l,r) p (\<sigma> \<circ>\<^sub>s (Var \<circ> Some))"
by (auto intro: rstep_r_p_s'_stable simp: rstep_r_p_s_eq_rstep_r_p_s')

lemma \<LL>\<^sub>1_closed_under_PP\<^sub>\<R>:
  assumes "\<LL>\<^sub>1 (mctxt_of_term s)" "(s, t) \<in> PP\<^sub>\<R>"
  shows "\<LL>\<^sub>1 (mctxt_of_term t)"
proof -
  let ?s = "mctxt_of_term (Fun Ap [Var undefined, s])"
  let ?t = "mctxt_of_term (Fun Ap [Var undefined, t])"
  obtain l r p \<sigma> where st_step: "(s, t) \<in> rstep_r_p_s (\<R> \<union> \<U>) (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of s t "\<R> \<union> \<U>"] assms(2) by blast
  have step: "(Fun Ap [Var undefined, s], Fun Ap [Var undefined, t])
               \<in> rstep_r_p_s (\<R> \<union> \<U>) (l, r) (Cons 1 p) \<sigma>"
    unfolding rstep_r_p_s_def
    using Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]]
      by (auto simp: Let_def)
  then have "(mctxt_term_conv ?s, mctxt_term_conv ?t)
          \<in> rstep_r_p_s' (\<R> \<union> \<U>) (l, r) (Cons 1 p) (\<sigma> \<circ>\<^sub>s (Var \<circ> Some))"
    using rstep_r_p_s_Var_Some by fast
  then have "(?s, ?t) \<in> mrstep (\<R> \<union> \<U>)"
    using rstep'_iff_rstep_r_p_s' by fast
  moreover have "?s \<in> \<LL>" using assms(1) \<LL>_def by auto
  ultimately have "?t \<in> \<LL>"
    using \<LL>_closed_under_\<R>[of ?s ?t] assms rstep'_iff_rstep_r_p_s' by fast
  then show ?thesis using sub_layers by fastforce
qed

lemma uncurried_NF':
  assumes "(s, t) \<in> PP\<^sub>\<R>^^n" "s \<in> \<T>" "\<LL>\<^sub>1 (mctxt_of_term s)"
  shows "(NF_\<U> s, NF_\<U> t) \<in> (rstep \<R>)\<^sup>*"
using assms
proof (induction n arbitrary: s)
  case (Suc n)
  obtain t' where split: "(s, t') \<in> PP\<^sub>\<R>" "(t', t) \<in> PP\<^sub>\<R>^^n"
    using relpow_Suc_D2[OF Suc(2)] by blast
  then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term t')" using \<LL>\<^sub>1_closed_under_PP\<^sub>\<R>[OF Suc(4)] by blast
  have "t' \<in> \<T>" using split(1) \<T>_closed_under_PP\<^sub>\<R>[OF Suc(3), of t'] by blast
  then show ?case using Suc(1)[OF split(2) _ in_\<LL>\<^sub>1]  uncurried_NF[OF split(1) Suc(3) _ Suc(4)] 
    by fastforce
qed simp

lemma no_rrstep:
  assumes s_def: "s = Fun Ap [Var v, t1]" and
          st_step: "(s, t) \<in> rstep_r_p_s (\<R> \<union> \<U>) r [] \<sigma>"
  shows False
proof (cases "r \<in> \<R>")
  case in_\<R>: True
  then obtain f ts where l_def: "fst r = Fun f ts"
    using wfR fst_conv unfolding wf_trs_def by (metis old.prod.exhaust)
  then obtain ts' where l\<sigma>_def:
      "fst r \<cdot> \<sigma> = Fun f ts'" "length ts' = length ts" by simp
  then have "(f, length ts') \<in> funas_term (fst r)" using l_def by auto
  then show ?thesis using in_\<R> st_step sigR fresh l\<sigma>_def
    unfolding rstep_r_p_s_def s_def funas_trs_def funas_rule_def by fastforce
next
  case in_\<U>: False
  then have "r \<in> \<U>" using st_step unfolding rstep_r_p_s_def by force
  then obtain f ts t1 where l_def: "fst r = Fun Ap [Fun f ts, t1]"
    using \<U>_def by fastforce
  then obtain ts' t1' where l\<sigma>_def:
      "fst r \<cdot> \<sigma> = Fun Ap [Fun f ts', t1']" "length ts' = length ts" by simp
  then show ?thesis using st_step unfolding rstep_r_p_s_def s_def by force
qed

lemma step_below1:
  assumes "(s, t) \<in> rstep_r_p_s R r (Cons 1 p') \<sigma>" "s = Fun Ap [x, s1]"
  shows "(s |_ [1], t |_ [1]) \<in> rstep_r_p_s R r p' \<sigma> \<and> t = Fun Ap [x, t |_ [1]]"
proof -
  let ?C = "ctxt_of_pos_term p' s1"
  obtain C where step: "C = ctxt_of_pos_term (Cons 1 p') s" "Cons 1 p' \<in> poss s"
                 "C\<langle>fst r \<cdot> \<sigma>\<rangle> = s \<and> C\<langle>snd r \<cdot> \<sigma>\<rangle> = t" "r \<in> R"
    using Product_Type.Collect_case_prodD[OF assms(1)[unfolded rstep_r_p_s_def]]
    unfolding rstep_r_p_s_def assms(2) by force
  then have "?C = ctxt_of_pos_term p' (s |_ [1]) \<and> p' \<in> poss (s |_ [1]) \<and>
         ?C\<langle>fst r \<cdot> \<sigma>\<rangle> = (s |_ [1]) \<and> ?C\<langle>snd r \<cdot> \<sigma>\<rangle> = (t |_ [1])"
    unfolding assms(2) by simp
  moreover have "t = Fun Ap [x, t |_ [1]]" using step unfolding assms(2) by auto
  ultimately show ?thesis using \<open>r \<in> R\<close> unfolding rstep_r_p_s_def by force
qed

lemma \<T>\<^sub>\<LL>_\<T>: "\<T>\<^sub>\<LL> \<subseteq> \<T>"
using \<T>_def \<LL>_sig funas_mctxt_mctxt_of_term unfolding \<C>_def by blast

lemma CR_on_\<T>\<^sub>\<LL>\<^sub>1_suffices:
 assumes "CR_on PP\<^sub>\<R> \<T>\<^sub>\<LL>\<^sub>1"
 shows "CR_on PP\<^sub>\<R> \<T>\<^sub>\<LL>"
proof -
  {
    fix s
    assume "s \<in> \<T>\<^sub>\<LL>"
    then have "s \<in> \<T>" using \<T>\<^sub>\<LL>_\<T> by blast
    then have "NF_\<U> s \<in> \<T>" using NF_\<U>_correct by blast
    have in_\<LL>: "(mctxt_of_term s) \<in> \<LL>" using \<open>s \<in> \<T>\<^sub>\<LL>\<close> by simp
    then consider (in_\<LL>\<^sub>1) "\<LL>\<^sub>1 (mctxt_of_term s)" | (in_\<LL>\<^sub>2) "\<LL>\<^sub>2 (mctxt_of_term s)"
      using \<LL>_def by blast
    then have "CR_on PP\<^sub>\<R> {s}"
    proof cases
      case in_\<LL>\<^sub>1
      then show ?thesis using assms unfolding CR_on_def by simp
    next
      case in_\<LL>\<^sub>2
      {
        fix s t assume in_\<LL>\<^sub>2: "\<LL>\<^sub>2 (mctxt_of_term s)" "(s, t) \<in> PP\<^sub>\<R>"
        then obtain r p \<sigma> where st_step: "(s, t) \<in> rstep_r_p_s (\<R> \<union> \<U>) r p \<sigma>"
          using rstep_iff_rstep_r_p_s[of s t "\<R> \<union> \<U>"] by blast
        have "p \<in> poss s" "r \<in> \<R> \<union> \<U>"
          using Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]]
          unfolding fst_conv by meson+
        obtain x C where "mctxt_of_term s = MFun Ap [x, C]" "x = MHole \<or> (\<exists>v. x = MVar v)"
          using in_\<LL>\<^sub>2 unfolding \<LL>\<^sub>2.simps by blast
        then obtain v t1 where s_def: "s = Fun Ap [Var v, t1]"
          using term_of_mctxt_mctxt_of_term_id[of s] by auto
        then have "\<LL>\<^sub>1 (mctxt_of_term (s |_ [1])) \<and> (s |_ [1], t |_ [1]) \<in> PP\<^sub>\<R> \<and>
               (\<exists>v s1 t1. s = Fun Ap [Var v, s1] \<and> t = Fun Ap [Var v, t1])"
        proof (cases p)
          case Nil
          then show ?thesis using s_def no_rrstep[OF _ st_step[unfolded Nil]] by blast  
        next
          case (Cons i p')
          consider "i = 0" | "i = 1" using s_def \<open>p \<in> poss s\<close> unfolding Cons by fastforce
          then show ?thesis
          proof cases
            case 1
            have "(fst r) \<cdot> \<sigma> = Var v"
              using s_def st_step unfolding rstep_r_p_s_def Cons 1 by force
            then show ?thesis using check_lhs[OF \<open>r \<in> \<R> \<union> \<U>\<close>, of \<sigma>] by simp
          next
            case 2
            have "[1] \<in> poss s" using \<open>p \<in> poss s\<close> unfolding Cons 2 by simp
            then have "\<LL>\<^sub>1 (mctxt_of_term (s |_ [1]))"
              using in_\<LL>\<^sub>2 \<LL>_def subm_at_layers[of "mctxt_of_term s" "[1]"]
              unfolding all_poss_mctxt_mctxt_of_term subm_at_mctxt_of_term[OF \<open>[1] \<in> poss s\<close>]
              by blast
            then show ?thesis using st_step \<open>[1] \<in> poss s\<close>
                step_below1[OF st_step[unfolded Cons 2] s_def]
              unfolding Cons 2 s_def by (auto simp: rstep_r_p_s_imp_rstep)
          qed
        qed
      } note step_below_1 = this
      have join_closed_ctxt: "(s, t) \<in> (rstep R)\<^sup>\<down> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>\<down>"
        for s t :: "('f, 'v) term" and R C using rsteps_closed_ctxt by auto
      {
        fix t u assume peak: "(s, t) \<in> PP\<^sub>\<R>\<^sup>*"
        then have "(s |_ [1], t |_ [1]) \<in> PP\<^sub>\<R>\<^sup>* \<and> \<LL>\<^sub>1 (mctxt_of_term (s |_ [1])) \<and>
               (\<exists>v s1 t1. s = Fun Ap [Var v, s1] \<and> t = Fun Ap [Var v, t1])"
          using in_\<LL>\<^sub>2
        proof (induction rule: converse_rtrancl_induct)
          case base
          obtain x C v where mctxt_t_def:
              "mctxt_of_term t = MFun Ap [x, C]" "\<LL>\<^sub>1 C" "x = MHole \<or> x = MVar v"
            using \<LL>\<^sub>2.cases[OF base] by metis
          then have "t = Fun Ap (map term_of_mctxt [x, C])"
              by (metis (full_types) term_of_mctxt.simps(2) term_of_mctxt_mctxt_of_term_id)
          then show ?case using mctxt_t_def by auto
        next
          case (step s s')
          obtain v s1 s1' where sub_in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (s |_ [1]))" and 
                         step_below1: "(s |_ [1], s' |_ [1]) \<in> PP\<^sub>\<R>" and
                         s_def: "s = Fun Ap [Var v, s1]" and
                         s'_def: "s' = Fun Ap [Var v, s1']"
            using step_below_1[OF step(4,1)] by fast+
          have "\<LL>\<^sub>1 (mctxt_of_term (s' |_ [1]))"
            using \<LL>\<^sub>1_closed_under_PP\<^sub>\<R>[OF sub_in_\<LL>\<^sub>1 step_below1] by blast
          then have s'_in_\<LL>\<^sub>2: "\<LL>\<^sub>2 (mctxt_of_term s')" unfolding s'_def by auto
          show ?case using sub_in_\<LL>\<^sub>1 step(3)[OF s'_in_\<LL>\<^sub>2] step_below1 s_def s'_def by auto
        qed
      } note main = this
      { fix t u assume st: "(s, t) \<in> PP\<^sub>\<R>\<^sup>*" and su: "(s, u) \<in> PP\<^sub>\<R>\<^sup>*"
        then obtain v s1 t1 u1 where sub_in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (s |_ [1]))" and
            st1: "(s |_ [1], t |_ [1]) \<in> PP\<^sub>\<R>\<^sup>*" and
            su1: "(s |_ [1], u |_ [1]) \<in> PP\<^sub>\<R>\<^sup>*" and
            term_defs: "s = Fun Ap [Var v, s1] \<and> t = Fun Ap [Var v, t1] \<and> u = Fun Ap [Var v, u1]"
          using main[OF st] main[OF su] by blast
        then have join: "(t |_ [1], u |_ [1]) \<in> PP\<^sub>\<R>\<^sup>\<down>" using assms by blast
        have "(t, u) \<in> PP\<^sub>\<R>\<^sup>\<down>"
          using term_defs join_closed_ctxt[OF join, of "More Ap [_] Hole []"] by simp
      }
      then show ?thesis unfolding CR_on_def by simp
    qed
  }
  then show ?thesis unfolding CR_on_def by simp
qed

theorem CR_on_\<LL>:
  assumes "CR_on (rstep \<R>) \<T>"
  shows "CR_on PP\<^sub>\<R> \<T>\<^sub>\<LL>"
proof -
  have "\<T>\<^sub>\<LL>\<^sub>1 \<subseteq> \<T>"
    using \<T>_def \<LL>_sig \<LL>_def funas_mctxt_mctxt_of_term unfolding \<C>_def by blast
  {
    fix s
    assume "s \<in> \<T>\<^sub>\<LL>\<^sub>1"
    then have "s \<in> \<T>" using \<open>\<T>\<^sub>\<LL>\<^sub>1 \<subseteq> \<T>\<close> by blast
    then have "NF_\<U> s \<in> \<T>" using NF_\<U>_correct by blast
    have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term s)" using \<open>s \<in> \<T>\<^sub>\<LL>\<^sub>1\<close>  by simp
    {
      fix t u assume "(s, t) \<in> PP\<^sub>\<R>\<^sup>*" and "(s, u) \<in> PP\<^sub>\<R>\<^sup>*"
      then have "t \<in> \<T>" "u \<in> \<T>" using \<T>_closed_under_PP\<^sub>\<R> \<open>s \<in> \<T>\<close> by blast+
      from \<open>(s, t) \<in> PP\<^sub>\<R>\<^sup>*\<close> obtain m where "(s, t) \<in> PP\<^sub>\<R>^^m" ..
      then have left: "(NF_\<U> s, NF_\<U> t) \<in> (rstep \<R>)\<^sup>*"
        using uncurried_NF'[OF _ \<open>s \<in> \<T>\<close> in_\<LL>\<^sub>1] by blast
      from \<open>(s, u) \<in> PP\<^sub>\<R>\<^sup>*\<close> obtain n where "(s, u) \<in> PP\<^sub>\<R>^^n" ..
      then have "(NF_\<U> s, NF_\<U> u) \<in> (rstep \<R>)\<^sup>*"
        using uncurried_NF'[OF _ \<open>s \<in> \<T>\<close> in_\<LL>\<^sub>1] by simp
      then have "(NF_\<U> t, NF_\<U> u) \<in> (rstep \<R>)\<^sup>\<down>"
        using left assms \<open>NF_\<U> s \<in> \<T>\<close> by blast
      then obtain v where d_props:
        "(NF_\<U> t, v) \<in> (rstep \<R>)\<^sup>*" "(NF_\<U> u, v) \<in> (rstep \<R>)\<^sup>*" 
        by blast
      moreover have "(t, NF_\<U> t) \<in> (rstep \<U>)\<^sup>*" "(u, NF_\<U> u) \<in> (rstep \<U>)\<^sup>*"
        using NF_\<U>_correct \<open>t \<in> \<T>\<close> \<open>u \<in> \<T>\<close> by blast+
      ultimately have "(t, v) \<in> PP\<^sub>\<R>\<^sup>*" "(u, v) \<in> PP\<^sub>\<R>\<^sup>*"
        using rtrancl_trans[of t "NF_\<U> t" PP\<^sub>\<R> v] rtrancl_trans[of u "NF_\<U> u" PP\<^sub>\<R> v]
        rstep_union[of \<R> \<U>] in_rtrancl_UnI[of _ "rstep \<R>" "rstep \<U>"] by metis+
      then have "(t, u) \<in> PP\<^sub>\<R>\<^sup>\<down>" by blast
    }
    then have "CR_on PP\<^sub>\<R> {s}" using CR_on_def by fastforce
  }
  then have "CR_on PP\<^sub>\<R> \<T>\<^sub>\<LL>\<^sub>1" unfolding CR_on_def by simp
  then show ?thesis using CR_on_\<T>\<^sub>\<LL>\<^sub>1_suffices by auto
qed

lemma CR_by_reduction:
  assumes cr: "CR S" and
          sigR': "\<And>x y. x \<in> A \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> y \<in> A" and
          prop1: "\<And>x y. (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> S\<^sup>\<leftrightarrow>\<^sup>*" and
          prop2: "\<And>x y'. x \<in> A \<Longrightarrow> (f x, y') \<in> S\<^sup>* \<Longrightarrow> (x, g y') \<in> R\<^sup>*"
  shows "CR_on R A"
proof -
  { fix a
    assume "a \<in> A"
    { fix b c
      assume peak: "(a, b) \<in> R\<^sup>*" "(a, c) \<in> R\<^sup>*"
      then have "(b, c) \<in> R\<^sup>\<down>"
      proof (cases "a = b")
        case False
        then have "b \<in> A" using rtrancl_induct[OF peak(1), of "\<lambda>x. x \<in> A"] \<open>a \<in> A\<close> sigR' by blast
        then show ?thesis
        proof (cases "a = c")
          case True
          then show ?thesis using peak by blast
        next
          case ac: False
          then have "c \<in> A"  using rtrancl_induct[OF peak(2), of "\<lambda>x. x \<in> A"] \<open>a \<in> A\<close> sigR' by blast
          have ab_conv: "(f a, f b) \<in> S\<^sup>\<leftrightarrow>\<^sup>*"
            using prop1 rtrancl_induct[OF \<open>(a, b) \<in> R\<^sup>*\<close>, of "\<lambda>x. (f a, f x) \<in> S\<^sup>\<leftrightarrow>\<^sup>*"]
            by simp (metis conversion_def rtrancl_trans)+
          have "(f a, f c) \<in> S\<^sup>\<leftrightarrow>\<^sup>*"
            using prop1 rtrancl_induct[OF \<open>(a, c) \<in> R\<^sup>*\<close>, of "\<lambda>x. (f a, f x) \<in> S\<^sup>\<leftrightarrow>\<^sup>*"]
            by simp (metis conversion_def rtrancl_trans)+
          then have "(f b, f c) \<in> S\<^sup>\<leftrightarrow>\<^sup>*" using conversion_trans[of S] ab_conv
            unfolding conversion_inv[of _ "f b"] by force
          then obtain d where join: "(f b, d) \<in> S\<^sup>* \<and> (f c, d) \<in> S\<^sup>*"
            using assms(1) unfolding CR_iff_conversion_imp_join by blast
          then have "(b, g d) \<in> R\<^sup>* \<and> (c, g d) \<in> R\<^sup>*"
            using prop2[OF \<open>b \<in> A\<close>, of d] prop2[OF \<open>c \<in> A\<close>, of d] by argo
          then show ?thesis by blast
        qed
      qed (auto simp: peak)
      then have "(b, c) \<in> R\<^sup>\<down>" by blast
    }
    then have "CR_on R {a}" using CR_on_def by fastforce
  }
  then show ?thesis unfolding CR_on_def by simp
qed

abbreviation \<T>\<^sub>C\<^sub>u where "\<T>\<^sub>C\<^sub>u \<equiv> { t . funas_term t \<subseteq> \<F>\<^sub>C\<^sub>u }"

lemma f_prop: "(x, y) \<in> rstep (Cu\<^sub>R \<R>) \<Longrightarrow> (x, y) \<in> PP\<^sub>\<R>\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  assume "(x, y) \<in> (rstep (Cu\<^sub>R \<R>))"
  then obtain l r p \<sigma> where step: "(x, y) \<in> rstep_r_p_s (Cu\<^sub>R \<R>) (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of x y "Cu\<^sub>R \<R>"] by blast
  obtain C where "x = C\<langle>l \<cdot> \<sigma>\<rangle>" "y = C\<langle>r \<cdot> \<sigma>\<rangle>" "p = hole_pos C" "(l, r) \<in> Cu\<^sub>R \<R>"
    using hole_pos_ctxt_of_pos_term[of p x]
      Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]]
    unfolding fst_conv snd_conv by metis
  obtain l' r' where l_def: "l = Cu l'" and r_def: "r = Cu r'" and in_\<R>: "(l', r') \<in> \<R>"
    using \<open>(l, r) \<in> Cu\<^sub>R \<R>\<close> Cu\<^sub>R_def by auto
  have funas: "funas_term l' \<subseteq> \<F>" "funas_term r' \<subseteq> \<F>"
    using in_\<R> sigR \<F>_def unfolding funas_trs_def funas_rule_def by force+
  have "l \<in> \<T>" "r \<in> \<T>" using \<open>(l, r) \<in> Cu\<^sub>R \<R>\<close> funas_Cu\<^sub>R
    unfolding layer_system_sig.\<T>_def \<F>\<^sub>U_def \<F>\<^sub>C\<^sub>u_def funas_trs_def funas_rule_def by force+
  then have "(l, l') \<in> (rstep \<U>)\<^sup>*" "(r, r') \<in> (rstep \<U>)\<^sup>*"
    using NF_\<U>_correct[OF NF_\<U>_Cu[OF funas(1)]] NF_\<U>_correct[OF NF_\<U>_Cu[OF funas(2)]]
    unfolding l_def r_def by blast+
  then have "(x, C\<langle>l' \<cdot> \<sigma>\<rangle>) \<in> rstep ((rstep \<U>)\<^sup>*) \<and> (y, C\<langle>r' \<cdot> \<sigma>\<rangle>) \<in> rstep ((rstep \<U>)\<^sup>*)"
    unfolding \<open>x = C\<langle>l \<cdot> \<sigma>\<rangle>\<close> \<open>y = C\<langle>r \<cdot> \<sigma>\<rangle>\<close> by (metis (no_types) rstepI)
  then have "(x, C\<langle>l' \<cdot> \<sigma>\<rangle>) \<in> PP\<^sub>\<R>\<^sup>\<leftrightarrow>\<^sup>* \<and> (C\<langle>r' \<cdot> \<sigma>\<rangle>, y) \<in> PP\<^sub>\<R>\<^sup>\<leftrightarrow>\<^sup>*"
    by (simp add: in_rtrancl_UnI rstep_union conversionI' conversion_inv)
  moreover have "(C\<langle>l' \<cdot> \<sigma>\<rangle>, C\<langle>r' \<cdot> \<sigma>\<rangle>) \<in> PP\<^sub>\<R>\<^sup>\<leftrightarrow>\<^sup>*" using in_\<R> by blast
  ultimately show ?thesis using conversion_trans[of PP\<^sub>\<R>] unfolding trans_def by meson
qed

lemma \<U>_step_Cu_persists:
  assumes "(t, t') \<in> rstep \<U>"
  shows "Cu t' = Cu t"
using assms
proof (induction t arbitrary: t')
  case (Fun f ts)
  then obtain l r p \<sigma> where step: "(Fun f ts, t') \<in> rstep_r_p_s \<U> (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of "Fun f ts" t' \<U>] by blast
  then obtain C where C_props: "Fun f ts = C\<langle>l \<cdot> \<sigma>\<rangle>" "t' = C\<langle>r \<cdot> \<sigma>\<rangle>" "p = hole_pos C"
                and p_in_poss: "p \<in> poss (Fun f ts)"
    using hole_pos_ctxt_of_pos_term[of p]
      Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]]
    unfolding fst_conv snd_conv by metis
  then show ?case
  proof (cases p)
    case Nil
    then have lhs_def: "Fun f ts = l \<cdot> \<sigma>" and rhs_def: "t' = r \<cdot> \<sigma>" and in_\<U>: "(l, r) \<in> \<U>" 
      using Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]] by auto
    then obtain f' ts' t m i where rule_def: 
        "l = Fun Ap [Fun f' ts', t]" "r = Fun f' (ts' @ [t])"
        "(f', m) \<in> \<F>" "length ts' = i" "i < m"
      using assms \<U>_def by force
    moreover have "f' \<noteq> Ap" using \<open>(f', m) \<in> \<F>\<close> fresh unfolding \<F>_def by fastforce
    ultimately show ?thesis unfolding lhs_def rhs_def by simp
  next
    case (Cons i p')
    then have "i < length ts" using p_in_poss by simp
    have inner: "(ts ! i, t' |_ [i]) \<in> rstep_r_p_s \<U> (l, r) p' \<sigma>"
      using rstep_i_pos_imp_rstep_arg_i_pos[OF step[unfolded Cons]] .
    obtain x where t'_def: "t' = Fun f ((take i ts) @ x # (drop (Suc i) ts))"
      using C_props id_take_nth_drop[OF \<open>i < length ts\<close>] unfolding Cons by (cases C) auto
    have x_def: "x = t' |_ [i]" using nth_append_take[of i ts x] \<open>i < length ts\<close>
      unfolding t'_def subt_at.simps by simp
    then have Cu_i: "Cu x = Cu (ts ! i)"
      using Fun(1)[of "ts ! i"] \<open>i < length ts\<close> rstep_r_p_s_imp_rstep[OF inner] by force
    show ?thesis
    proof (cases "f = Ap")
      case isAp: True
      show ?thesis using Cu_i id_take_nth_drop[OF \<open>i < length ts\<close>]
        unfolding Cons t'_def isAp by simp (metis (no_types) list.simps(9) map_append)
    next
      case notAp: False
      obtain ss1 y ss2 where short: "take i ts = ss1" "ts ! i = y" "drop (Suc i) ts = ss2" and
                            ts_def: "ts = ss1 @ y # ss2"
        using id_take_nth_drop[OF \<open>i < length ts\<close>] by blast
      have Cu_xy: "Cu x = Cu y" using Cu_i unfolding \<open>ts ! i = y\<close> .
      show ?thesis unfolding t'_def short using ts_def unfolding ts_def
      proof (induction "length ss2" arbitrary: ss2)
        case (Suc n)
        then obtain ss2' a where ss2_def: "ss2 = ss2' @ [a]"
          by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
        have inner: "Cu (Fun f (ss1 @ x # ss2')) = Cu (Fun f (ss1 @ y # ss2'))"
          using Suc unfolding ss2_def by simp
        have Cu_unfold: "Cu (Fun f (ss1 @ t # ss2)) = Fun Ap [Cu (Fun f (ss1 @ t # ss2')), Cu a]" for t
          unfolding ss2_def append_Cons[symmetric] append.assoc[symmetric] Cu_last2[OF notAp] by simp
        then show ?case using inner by simp
      qed (simp add: Cu_xy notAp)
    qed
  qed
qed (simp add: NF_Var[OF wfU])

lemma Cu_in_ctxt:
  shows "\<exists>C'. Cu C\<langle>l \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and> Cu C\<langle>r \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (r \<cdot> \<sigma>)\<rangle>"
proof (induction C)
  case Hole
  then show ?case by simp (metis ctxt.cop_nil)
next
  case (More f ss1 D ss2)
  then obtain D' where inner: "Cu D\<langle>l \<cdot> \<sigma>\<rangle> = D'\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and> Cu D\<langle>r \<cdot> \<sigma>\<rangle> = D'\<langle>Cu (r \<cdot> \<sigma>)\<rangle>" by blast
  then show ?case
  proof (cases "f = Ap")
    case isAp: True
    have "ss1 @ D\<langle>t \<cdot> \<sigma>\<rangle> # ss2 \<noteq> []" for t
      by blast
    then have Cu_unfold: "Cu (More f ss1 D ss2)\<langle>t \<cdot> \<sigma>\<rangle> =
                     Fun Ap (map Cu (ss1 @ D\<langle>t \<cdot> \<sigma>\<rangle> # ss2))" for t
      unfolding isAp unfolding intp_actxt.simps
      by (metis Cu.simps(3) length_greater_0_conv nth_drop_0)
    show ?thesis using inner unfolding Cu_unfold
      by simp (meson intp_actxt.simps(2))
  next
    case notAp: False
    show ?thesis
    proof (induction "length ss2" arbitrary: ss2)
      case 0
      let ?C = "More Ap [Cu (Fun f ss1)] D' []"
      have "Cu (More f ss1 D ss2)\<langle>l \<cdot> \<sigma>\<rangle> = ?C\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and>
            Cu (More f ss1 D ss2)\<langle>r \<cdot> \<sigma>\<rangle> = ?C\<langle>Cu (r \<cdot> \<sigma>)\<rangle>"
        using 0 notAp inner by simp
      then show ?case by blast
    next
      case (Suc n)
      then obtain ss2' a where ss2_def: "ss2 = ss2' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI) 
      let ?ts = "\<lambda>t. ss1 @ D\<langle>t \<cdot> \<sigma>\<rangle> # ss2'"
      have Cu_unfold: "Cu (Fun f (ss1 @ D\<langle>t \<cdot> \<sigma>\<rangle> # ss2)) = Fun Ap [Cu (Fun f (?ts t)), Cu a]" for t
         unfolding ss2_def append_Cons[symmetric] append.assoc[symmetric] Cu_last2[OF notAp] by simp
      obtain C' where C'_def: "Cu (More f ss1 D ss2')\<langle>l \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and>
                               Cu (More f ss1 D ss2')\<langle>r \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (r \<cdot> \<sigma>)\<rangle>"
        using Suc(1)[of ss2'] Suc(2) unfolding ss2_def by auto
      let ?C = "More Ap [] C' [Cu a]"
      have "Cu (More f ss1 D ss2)\<langle>l \<cdot> \<sigma>\<rangle> = ?C\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and>
            Cu (More f ss1 D ss2)\<langle>r \<cdot> \<sigma>\<rangle> = ?C\<langle>Cu (r \<cdot> \<sigma>)\<rangle>"
        using C'_def unfolding intp_actxt.simps Cu_unfold by simp
      then show ?case by blast
    qed
  qed
qed

lemma Cu_in_subst:
  assumes "funas_term t \<subseteq> \<F>"
  shows "Cu (t \<cdot> \<sigma>) = (Cu t) \<cdot> (Cu \<circ> \<sigma>)"
using assms
proof (induction t)
  case (Fun f ts)
  { fix x
    assume "x \<in> set ts"
    then have "Cu (x \<cdot> \<sigma>) = (Cu x) \<cdot> (Cu \<circ> \<sigma>)" using Fun by fastforce
  } note inner = this
  show ?case
  proof (cases "f = Ap")
    case isAp: True
    then show ?thesis using Fun(2) fresh unfolding \<F>_def by fastforce
  next
    case notAp: False
    show ?thesis using inner
    proof (induction "length ts" arbitrary: ts)
      case (Suc n)
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI) 
      have subst_unfold: "Fun f ts \<cdot> \<sigma> = Fun f (map (\<lambda>x. x \<cdot> \<sigma>) ts)" for ts by simp
      have "Cu (Fun f ts) = Fun Ap [Cu (Fun f ts'), Cu a]"
        using notAp unfolding ts_def by simp
      moreover have "Cu (Fun f ts \<cdot> \<sigma>) = Fun Ap [Cu (Fun f (map (\<lambda>x. x \<cdot> \<sigma>) ts')), Cu (a \<cdot> \<sigma>)]"
        using notAp unfolding ts_def subst_unfold by simp
      moreover have "Cu (Fun f ts' \<cdot> \<sigma>) = Cu (Fun f ts') \<cdot> (Cu \<circ> \<sigma>)" "Cu (a \<cdot> \<sigma>) = Cu a \<cdot> (Cu \<circ> \<sigma>)"
        using Suc(1)[of ts'] Suc(2,3) unfolding ts_def by force+
      ultimately show ?case using notAp 
        unfolding ts_def by simp
    qed simp
  qed
qed simp

lemma g_prop1: "(x, y') \<in> PP\<^sub>\<R> \<Longrightarrow> (Cu x, Cu y') \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*"
proof -
  assume "(x, y') \<in> PP\<^sub>\<R>"
  then consider (\<R>_step) "(x, y') \<in> rstep \<R>" | (\<U>_step) "(x, y') \<in> rstep \<U>" by fast
  then show ?thesis
  proof cases
    case \<R>_step
    then obtain l r p \<sigma> where step: "(x, y') \<in> rstep_r_p_s \<R> (l, r) p \<sigma>"
      using rstep_iff_rstep_r_p_s[of x y' \<R>] by blast
    obtain C where x_def: "x = C\<langle>l \<cdot> \<sigma>\<rangle>" and y'_def: "y' = C\<langle>r \<cdot> \<sigma>\<rangle>" and in_\<R>: "(l, r) \<in> \<R>"
      using hole_pos_ctxt_of_pos_term[of p x]
        Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]]
      unfolding fst_conv snd_conv by metis
    let ?\<sigma> = "Cu \<circ> \<sigma>"
    have funas: "funas_term l \<subseteq> \<F>" "funas_term r \<subseteq> \<F>" using in_\<R> sigR
      unfolding funas_trs_def funas_rule_def \<F>_def by fastforce+
    obtain C' where "Cu C\<langle>l \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (l \<cdot> \<sigma>)\<rangle> \<and> Cu C\<langle>r \<cdot> \<sigma>\<rangle> = C'\<langle>Cu (r \<cdot> \<sigma>)\<rangle>"
      using Cu_in_ctxt by blast
    then have "Cu C\<langle>l \<cdot> \<sigma>\<rangle> = C'\<langle>(Cu l) \<cdot> ?\<sigma>\<rangle>" "Cu C\<langle>r \<cdot> \<sigma>\<rangle> = C'\<langle>(Cu r) \<cdot> ?\<sigma>\<rangle>"
      using Cu_in_subst[of _ \<sigma>] funas by force+
    then show ?thesis using Cu\<^sub>R_def in_\<R> unfolding x_def y'_def by auto
  next
    case \<U>_step
    show ?thesis using \<U>_step_Cu_persists[OF \<U>_step] by simp
  qed
qed

lemma \<T>\<^sub>C\<^sub>u_Cu_eq: "t \<in> \<T>\<^sub>C\<^sub>u \<Longrightarrow> Cu t = t"
proof (induction t)
  case (Fun f ts) then show ?case
  proof (cases "f = Ap")
    case isAp: True
    { fix x
      assume "x \<in> set ts"
      then have "Cu x = x" using Fun \<F>\<^sub>C\<^sub>u_def by auto
    }
    moreover have "Cu (Fun Ap ts) = Fun Ap (map Cu ts)"
      using Fun(2) Suc_length_conv[of 1 ts] fresh unfolding isAp \<F>\<^sub>C\<^sub>u_def by force
    ultimately show ?thesis unfolding isAp by (simp add: map_idI)
  qed (auto simp: \<F>\<^sub>C\<^sub>u_def)
qed simp

lemma \<T>\<^sub>C\<^sub>u_Cu\<^sub>R_persists: "\<And>x y. x \<in> \<T>\<^sub>C\<^sub>u \<Longrightarrow> (x, y) \<in> rstep (Cu\<^sub>R \<R>) \<Longrightarrow> y \<in> \<T>\<^sub>C\<^sub>u"
  using rstep_preserves_funas_terms[OF funas_Cu\<^sub>R _ _ wf_Cu] unfolding \<T>_def by blast

lemma g_prop:
  assumes "x \<in> \<T>\<^sub>C\<^sub>u" "(x, y') \<in> PP\<^sub>\<R>\<^sup>*"
  shows "(x, Cu y') \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*"
proof -
  have "(Cu x, Cu y') \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*"
    using g_prop1 assms(2) rtrancl_map[of PP\<^sub>\<R> Cu "(rstep (Cu\<^sub>R \<R>))\<^sup>*" x y']
    unfolding rtrancl_idemp by blast
  then show ?thesis using \<T>\<^sub>C\<^sub>u_Cu_eq[OF assms(1)] by argo
qed

theorem main_result_complete:
  assumes "CR (rstep \<R>)"
  shows "CR (rstep (Cu\<^sub>R \<R>))"
proof -
  have wf_RU: "wf_trs (\<R> \<union> \<U>)" using wfR wfU unfolding wf_trs_def by blast
  have "CR_on (rstep \<R>) \<T>" using assms unfolding CR_defs by simp
  then have "CR_on PP\<^sub>\<R> \<T>\<^sub>\<LL>" using CR_on_\<LL> by simp
  then have CR: "CR_on PP\<^sub>\<R> \<T>" by (rule CR)
  then have "CR PP\<^sub>\<R>" using CR_on_imp_CR[OF wf_RU \<R>_sig] unfolding \<T>_def by blast
  have "CR_on (rstep (Cu\<^sub>R \<R>)) \<T>\<^sub>C\<^sub>u"
    using CR_by_reduction[OF \<open>CR PP\<^sub>\<R>\<close>, of \<T>\<^sub>C\<^sub>u "rstep (Cu\<^sub>R \<R>)" id Cu] \<T>\<^sub>C\<^sub>u_Cu\<^sub>R_persists
    f_prop g_prop unfolding id_apply by presburger
  then show ?thesis using CR_on_imp_CR[OF wf_Cu funas_Cu\<^sub>R] unfolding \<T>_def by blast
qed

end

end
