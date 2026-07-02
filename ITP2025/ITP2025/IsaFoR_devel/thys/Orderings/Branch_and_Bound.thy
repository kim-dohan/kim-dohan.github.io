theory Branch_and_Bound
  imports
    Linear_Inequalities.Mixed_Integer_Solutions
    Simplex.Simplex_Incremental
    Farkas.Matrix_Farkas
    "List-Index.List_Index"
    "Certification_Monads.Check_Monad"
begin

hide_const (open) Farkas.rel_of
hide_const (open) Missing_Lemmas.max_list

(* reenable Var without prefix *)
abbreviation Var where "Var \<equiv> Abstract_Linear_Poly.Var"
abbreviation max_var where "max_var \<equiv> Abstract_Linear_Poly.max_var"
abbreviation vars_list where "vars_list \<equiv> Abstract_Linear_Poly.vars_list"

fun satisfies_mixed_constraints (infixl "\<Turnstile>\<^sub>m\<^sub>c\<^sub>s" 100) where
"v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (cs, I) = (v \<Turnstile>\<^sub>c\<^sub>s cs \<and> (\<forall> i \<in> I. v i \<in> \<int>))"

(* For the moment, the type of branch_and_bound is sufficient to solve
  mixed-integer linear problems, but it should be updated afterwards by:
  - Returning an unsat core when the problem is infeasible instead of just
    returning `None`
Also, maybe the argument types could be changed to be more efficient, but it
is not the priority now.
*)

text \<open>We define the following measure on the arguments of the branch-and-bound
algorithm to prove its termination.
The idea is that at each recursive call ("branch operation"), if the branch
is performed on the variable x, then the quantity ub x - lb x strictly
decreases while the other ones are left unchanged.
Finally, if the sum of the ub x - lb x is nonpositive, then the problem
has an unique solution with integral values for the elements of Is, or is
infeasible.\<close>
fun bb_measure where
"bb_measure (Is, lb, ub) = nat (sum_list (map (\<lambda> x. ub x - lb x) Is))"

definition bounds_to_constraints where
  "bounds_to_constraints Is lb ub =
     map (\<lambda> x. GEQ (Var x) (of_int (lb x))) Is @
     map (\<lambda> x. LEQ (Var x) (of_int (ub x))) Is"

lemma bounds_to_constraints_sat:
  "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub) \<longleftrightarrow>
   (\<forall> i \<in> set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i))"
proof -
  {
    fix i
    assume v: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    assume "i \<in> set Is"
    hence "GEQ (Var i) (of_int (lb i)) \<in> set (bounds_to_constraints Is lb ub)"
      and "LEQ (Var i) (of_int (ub i)) \<in> set (bounds_to_constraints Is lb ub)"
      unfolding bounds_to_constraints_def by auto
    hence "v \<Turnstile>\<^sub>c GEQ (Var i) (of_int (lb i)) \<and>
           v \<Turnstile>\<^sub>c LEQ (Var i) (of_int (ub i))" using v by blast
    hence  "of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i)"
      using valuate_Var[of i v] by auto
  }
  moreover
  {
    fix c
    assume bnd: "(\<forall> i \<in> set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i))"
    assume "c \<in> set (bounds_to_constraints Is lb ub)"
    then obtain i where i: "i \<in> set Is"
                  and "c = GEQ (Var i) (of_int (lb i)) \<or>
                       c = LEQ (Var i) (of_int (ub i))"
      unfolding bounds_to_constraints_def by auto
    hence "v \<Turnstile>\<^sub>c c" using i bnd valuate_Var[of i v] by fastforce
  }
  ultimately show ?thesis by blast
qed

lemma bounds_to_constraints_cong:
  assumes "\<And>x. x \<in> set Is \<Longrightarrow> lb x = lb' x" "\<And>x. x \<in> set Is \<Longrightarrow> ub x = ub' x"
  shows "bounds_to_constraints Is lb ub = bounds_to_constraints Is lb' ub'"
  unfolding bounds_to_constraints_def
  using assms by auto

lemma sat_impl_sum_diff_bounds_nonneg:
  assumes sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
  and J: "set J \<subseteq> set Is"
  shows "(\<Sum>x\<leftarrow>J. ub x - lb x) \<ge> 0"
proof (rule sum_list_nonneg)
  fix y assume "y \<in> set (map (\<lambda>x. ub x - lb x) J)"
  then obtain x where x: "x \<in> set J" and y: "y = ub x - lb x" by auto
  from sat have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    using simplex(3) by fastforce
  hence "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints J lb ub)"
    unfolding bounds_to_constraints_def using J by auto
  hence "of_int (lb x) \<le> \<langle>v\<rangle> x \<and> \<langle>v\<rangle> x \<le> of_int (ub x)"
    using bounds_to_constraints_sat x by blast
  hence "ub x - lb x \<ge> 0" by linarith
  thus "y \<ge> 0" using y by blast
qed

lemma find_Some_set:
  assumes "find P xs = Some x"
  shows "x \<in> set xs \<and> P x"
proof -
  from assms obtain i where "x = xs ! i" and "i < length xs" and "P (xs ! i)"
    using find_Some_iff[of P xs x] by blast
  thus ?thesis by auto
qed

lemma int_le_floor_iff:
  assumes "x \<in> \<int>"
  shows "x \<le> y \<longleftrightarrow> x \<le> of_int \<lfloor>y\<rfloor>"
proof
  assume "x \<le> y"
  thus "x \<le> of_int \<lfloor>y\<rfloor>"
    using le_floor_iff[of "\<lfloor>x\<rfloor>" "y"] floor_of_int_eq[OF assms] by auto
next
  assume "x \<le> of_int \<lfloor>y\<rfloor>"
  thus "x \<le> y"
    using le_floor_iff[of "\<lfloor>x\<rfloor>" "of_int \<lfloor>y\<rfloor>"] floor_of_int_eq[OF assms]
    by linarith
qed

lemma int_ge_ceiling_iff:
  assumes "x \<in> \<int>"
  shows "x \<ge> y \<longleftrightarrow> x \<ge> of_int \<lceil>y\<rceil>"
  unfolding ceiling_def
  using int_le_floor_iff[of "-x" "-y"] assms by fastforce


lemma nonnint_sat_pos_measure:
  assumes sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
  assumes find: "find (\<lambda>y. \<langle>v\<rangle> y \<notin> \<int>) Is = Some x"
  shows "0 < (\<Sum>x\<leftarrow>Is. ub x - lb x)"
proof -
  have x: "x \<in> set Is" and "\<langle>v\<rangle> x \<notin> \<int>" using find_Some_set[OF find] by auto
  from sat simplex(3) have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    by auto
  hence "of_int (lb x) \<le> \<langle>v\<rangle> x \<and> \<langle>v\<rangle> x \<le> of_int (ub x)"
    using bounds_to_constraints_sat x by blast
  (* I wonder why the automatic provers perform badly with `rat_of_int`.
     I have to add an intermediary step, and I also have to tell
     explicitely `metis` to use `Ints_of_int`. Even if I add explicitely this
     lemma, metis is the only prover that manages to use it. *)
  hence "rat_of_int (lb x) \<ge> rat_of_int (ub x) \<Longrightarrow> rat_of_int (lb x) = \<langle>v\<rangle> x"
    by linarith
  hence "\<not> (rat_of_int (lb x) \<ge> rat_of_int (ub x))"
    using `\<langle>v\<rangle> x \<notin> \<int>` Ints_of_int by metis

  hence "0 < ub x - lb x" by linarith
  moreover have "0 \<le> (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    using set_remove1_subset
    by (rule sat_impl_sum_diff_bounds_nonneg[OF sat])
  ultimately have "0 < (ub x - lb x) + (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    by linarith
  also have "\<dots> = (\<Sum>i\<leftarrow>Is. ub i - lb i)"
    using sum_list_map_remove1[OF x, of "\<lambda> i. ub i - lb i"] by auto
  finally show ?thesis by blast
qed

text \<open>The core of a branch-and-bound solver for mixed-integer linear problems.
It takes as arguments a constraint list, the list of integral variables, and
functions mapping integral variables to lower and upper-bounds\<close>
(* Below is a new implementation of bnb with incremental simplex, using the
   refinement approach. *)
definition atom_to_qdnsconstr :: "rat atom \<Rightarrow> QDelta ns_constraint" where
  "atom_to_qdnsconstr atm =
    (case atm of
      (Leq x qdcnst) \<Rightarrow> (LEQ_ns (Var x) (QDelta qdcnst 0))
    | (Geq x qdcnst) \<Rightarrow> (GEQ_ns (Var x) (QDelta qdcnst 0)))"

definition atom_to_qdatom where
  "atom_to_qdatom atm = (case atm of
    (Leq vr c) \<Rightarrow> (Leq vr (QDelta c 0)) |
    (Geq vr c) \<Rightarrow> (Geq vr (QDelta c 0)))"

definition update_iatom_in_state' ::
  "nat simplex_state \<Rightarrow> (nat, rat) i_atom \<Rightarrow> nat simplex_state" where
  "update_iatom_in_state' s iatm =
    (case s of Simplex_State (cs, (asi, tv, ui), l3s) \<Rightarrow>
      let cs' = cs[(fst iatm) := atom_to_qdnsconstr (snd iatm)];
        asi' = Mapping.update (fst iatm) [(fst iatm, atom_to_qdatom (snd iatm))] asi in
        Simplex_State (cs', (asi', tv, ui), l3s))"

definition i_bounds_to_constraints where
  "i_bounds_to_constraints Is lb ub =
     map (\<lambda> x. (fst (lb x), GEQ (Var x) (of_int (snd (lb x))))) Is @
     map (\<lambda> x. (fst (ub x), LEQ (Var x) (of_int (snd (ub x))))) Is"

fun enumerated where
  "enumerated n [] = True" |
  "enumerated n ((i, x)#xs) = (n = i \<and> enumerated (Suc n) xs)"

lemma enumerated_enumerate:
  "enumerated n xs = (xs = List.enumerate n (map snd xs))"
  by (induction n xs rule: enumerated.induct) (auto)

lemma enumerated_distinct: "enumerated n xs \<Longrightarrow> distinct (map fst xs)"
  unfolding enumerated_enumerate enumerate_eq_zip by (induction n xs rule: enumerated.induct) (auto)

lemma enumerated_sorted: "enumerated n xs \<Longrightarrow> sorted (map fst xs)"
  unfolding enumerated_enumerate using sorted_enumerate by metis

lemma enumerated: "map fst xs = [n..<n +length xs] \<longleftrightarrow> enumerated n xs"
  unfolding enumerated_enumerate by (metis enumerate_eq_zip length_map map_fst_enumerate zip_map_fst_snd)

lemma enumeratedE[elim]:
  assumes a: "enumerated n xs" and
    b: "distinct (map fst xs) \<Longrightarrow> sorted (map fst xs) \<Longrightarrow> P"
  shows "P"
  using assms enumerated_distinct enumerated_sorted by blast

lemma sorted_map_distinct_set_unique:
  assumes "sorted (map f xs)" "distinct (map f xs)" "sorted (map f ys)" "distinct (map f ys)"
    "set xs = set ys" "length xs = length ys"
  shows "xs = ys"
  using assms proof (induction rule: list_induct2[OF `length xs = length ys`])
  case 1
  then show ?case by (simp)
next
  case (2 x xs y ys)
  then have 1: "x = y"
    by (clarsimp) (metis eq_iff image_iff  insert_iff)
  moreover have "y \<notin> set ys"
    using 2 by fastforce
  ultimately have "set xs = set ys"
    using 2 by fastforce
  then show ?case
    using 1 2 by auto
qed

lemma enumerated_set_unique:
  assumes "enumerated n xs" "enumerated n ys" "set xs = set ys" "length xs = length ys"
  shows "xs = ys"
  using assms by (auto intro: sorted_map_distinct_set_unique)

lemma enumerated_update:
  assumes "xs' = xs[i := (i + n, y)]" "enumerated n xs"
  shows "enumerated n xs'"
proof (cases "i < length xs")
  case True
  then show ?thesis
    using assms
    unfolding enumerated_enumerate enumerate_eq_zip
  proof (induction xs' arbitrary: xs i n y)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs')
    have "fst (xs ! i) = i + n"
      by (metis Cons.prems(1) Cons.prems(3) add.commute add_diff_cancel_left' length_map length_upt less_diff_conv map_fst_zip nth_map nth_upt)
    then show ?case
      using Cons apply(auto)
        (* TODO: rewrite proof *)
      using add_diff_cancel_left' fst_conv length_map length_upt list_update_id map_fst_zip map_update update_zip
      by smt
  qed
next
  case False
  then show ?thesis
    using assms by auto
qed

lemma enumerated_Cons: "enumerated n (x # xs) \<Longrightarrow> enumerated (Suc n) xs"
  by (cases x) auto

lemma enumerated_append: "enumerated n (xs @ ys) \<Longrightarrow> enumerated n xs"
  by (induction n xs rule: enumerated.induct) (auto)

(* TODO: clean me up *)
lemma enumerated_nth: "enumerated n xs \<Longrightarrow> (n + i, y) \<in> set xs \<Longrightarrow> xs ! i = (n + i, y)"
proof (induction n xs arbitrary: i y rule: enumerated.induct)
  case (2 n i x xs j y)
  thus ?case apply (cases i, auto)
   apply (metis One_nat_def Suc_less_eq Suc_pred enumerated_enumerate in_set_enumerate_eq le_imp_less_Suc nth_Cons_pos prod.sel(1))
    by (metis One_nat_def Suc_pred add.right_neutral add_Suc_right enumerated_enumerate in_set_enumerate_eq lessI linorder_not_less neq0_conv nth_Cons' prod.sel(1))
qed auto

(* TODO: clean me up *)
lemma enumerated_nth': "enumerated n xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i = (n + i, snd (xs ! i))"
proof (induction n xs arbitrary: i rule: enumerated.induct)
  case (2 n i x xs j)
  thus ?case apply (cases i, auto)
   apply (metis length_nth_simps(4) not0_implies_Suc not_less_eq nth_Cons_0 snd_conv)
    using less_Suc_eq_0_disj by auto
qed auto

(* The invariant is probably needs a few more assumptions
TODO: find better name  *)
definition state_invariant where
  "state_invariant cs Is lb ub s =
    (let bs = i_bounds_to_constraints Is lb ub @ cs in
      enumerated 0 bs \<and>
      invariant_simplex bs (fst ` set bs) s)"

definition checked_bnc where
  "checked_bnc cs Is lb ub s =
    (let bs = i_bounds_to_constraints Is lb ub @ cs in
      enumerated 0 bs \<and>
      checked_simplex bs (fst ` set bs) s)"

lemma checked_invariant_bnc: "checked_bnc cs Is lb ub s \<Longrightarrow> state_invariant cs Is lb ub s"
  unfolding checked_bnc_def state_invariant_def using checked_invariant_simplex by (auto simp add: Let_def)

lemma state_invariant_simplex:
  assumes inv: "state_invariant cs Is lb ub s"
  and sat: "check_simplex s = (s',None)"
  and "solution_simplex s' = v"
shows "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub @ cs))"
proof -
  let ?bs = "i_bounds_to_constraints Is lb ub @ cs"
  have "checked_simplex ?bs (fst ` set ?bs) s'" using sat inv check_simplex_ok
    unfolding state_invariant_def by (auto simp add: Let_def)
  then have "((fst ` set ?bs), v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ?bs" using solution_simplex assms(3) by blast
  then have "v \<Turnstile>\<^sub>c\<^sub>s set (map snd ?bs)" by force
  then show ?thesis unfolding i_bounds_to_constraints_def bounds_to_constraints_def by simp
qed

lemma state_invariant_simplex_Unsat:
  assumes inv: "state_invariant cs Is lb ub s"
  and sat: "check_simplex s = (s',Some I)"
shows "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub @ cs))"
proof -
  let ?bs = "i_bounds_to_constraints Is lb ub @ cs"
  have "set I \<subseteq> set (map fst ?bs) \<and> minimal_unsat_core (set I) ?bs"
    using assms unfolding state_invariant_def
    using check_simplex_unsat[OF _ sat]
    by (auto simp add: image_Un Let_def)
  then show ?thesis
    unfolding minimal_unsat_core_def by force
qed

lemma sat_impl_sum_diff_bounds_nonneg':
  assumes sat: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
  and J: "set J \<subseteq> set Is"
  shows "(\<Sum>x\<leftarrow>J. ub x - lb x) \<ge> 0"
proof (rule sum_list_nonneg)
  fix y assume "y \<in> set (map (\<lambda>x. ub x - lb x) J)"
  then obtain x where x: "x \<in> set J" and y: "y = ub x - lb x" by auto
  have "of_int (lb x) \<le> v x \<and> v x \<le> of_int (ub x)"
    using assms bounds_to_constraints_sat x by blast
  hence "ub x - lb x \<ge> 0" by linarith
  thus "y \<ge> 0" using y by blast
qed

lemma nonnint_sat_pos_measure':
  assumes sat: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
  assumes find: "find (\<lambda>y. v y \<notin> \<int>) Is = Some x"
  shows "0 < (\<Sum>x\<leftarrow>Is. ub x - lb x)"
proof -
  have x: "x \<in> set Is" and "v x \<notin> \<int>" using find_Some_set[OF find] by auto
  then have "of_int (lb x) \<le> v x \<and> v x \<le> of_int (ub x)"
    using assms bounds_to_constraints_sat x by blast
  then have "rat_of_int (lb x) \<ge> rat_of_int (ub x) \<Longrightarrow> rat_of_int (lb x) = v x"
    by linarith
  then have "\<not> (rat_of_int (lb x) \<ge> rat_of_int (ub x))"
    using `v x \<notin> \<int>` Ints_of_int by metis
  then have "0 < ub x - lb x" by linarith
  moreover have "0 \<le> (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    using set_remove1_subset sat_impl_sum_diff_bounds_nonneg'[OF sat] by metis
  ultimately have "0 < (ub x - lb x) + (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    by linarith
  also have "\<dots> = (\<Sum>i\<leftarrow>Is. ub i - lb i)"
    using sum_list_map_remove1[OF x, of "\<lambda> i. ub i - lb i"] by auto
  finally show ?thesis by blast
qed

definition del_atom_from_state'' :: "nat simplex_state \<Rightarrow> (nat, rat) i_atom \<Rightarrow> nat simplex_state"
  where
  "del_atom_from_state'' s iatm = (case s of
    Simplex_State (l1, l2, State t bl bu v c uc) \<Rightarrow>
      (let bu' = Mapping.delete (atom_var (snd iatm)) bu;
        bl' = Mapping.delete (atom_var (snd iatm)) bl in
        Simplex_State (l1, l2, State t bl' bu' v c uc)))"

fun sum_to_option where
  "sum_to_option (Inr x) = Some x" |
  "sum_to_option (Inl _) = None"

definition bnb_update_state'' ::
   "(nat \<times> constraint) list \<Rightarrow> var list \<Rightarrow> (var \<Rightarrow> (nat \<times> int)) \<Rightarrow> (var \<Rightarrow> (nat \<times> int))
     \<Rightarrow> nat simplex_state \<Rightarrow> (nat, rat) i_atom \<Rightarrow> nat simplex_state option" where
  "bnb_update_state'' cs Is lb ub s iatm =
      (let idx_list = (map fst (i_bounds_to_constraints Is lb ub @ cs)) in
        (case (assert_all_simplex (remove1 (fst iatm) idx_list) (del_atom_from_state'' s iatm)) of
          Sat s' \<Rightarrow> sum_to_option (assert_simplex (fst iatm) (update_iatom_in_state' s' iatm)) |
          Unsat uc \<Rightarrow> None))"

definition suitable_upd_atom where
  "suitable_upd_atom iatm ics =
    (let tons = to_ns ics;
      i = (find_index (\<lambda>x. fst x = fst iatm \<and> poly (snd x) = Var (atom_var (snd iatm))) tons) in
      (if i \<ge> length tons then False else True))"

lemma mapping_del[simp]:
  "Mapping.lookup (Mapping.delete v m1) x = (if x = v then None else Mapping.lookup m1 x)"
  by (transfer, auto)

lemma mapping_del2[simp]:
  "Mapping.lookup m1 x = None \<Longrightarrow> Mapping.lookup (Mapping.delete v m1) x = None"
  by (transfer, auto)

lemma normalize_ns_constraint_vars_eq:
  "vars (poly (normalize_ns_constraint nc)) = vars (poly nc)"
  by (smt inverse_inverse_eq inverse_zero normalize_ns_constraint.elims poly.simps(1) poly.simps(2)
      vars_scaleRat ns_constraint.split)

lemma firstfresh_ge_start:
  "Poly_Mapping (preprocess' t v) p = Some vr \<Longrightarrow> vr \<ge> v"
  by (induct t) (auto simp: Let_def fresh_var_monoinc split: option.splits if_splits)

lemma single_var_poly_is_monom:
  "vars p = {vr} \<Longrightarrow> is_monom p"
proof -
  assume "vars p = {vr}"
  then have "vars_list p = [vr]"
    by (metis all_not_in_conv distinct.simps(2) insert_eq_iff list.set_intros(1) list.simps(15)
        list_encode.cases set_empty2 singletonD distinct_vars_list set_vars_list)
  then show ?thesis using is_monom_def by simp
qed

lemma preprocess'_iatom_from_insconstr:
  assumes "as = Atoms (preprocess' ntons start)"
  shows "\<forall>a. a \<in> set as \<longrightarrow>
    (\<exists>vr nc. (snd a) = qdelta_constraint_to_atom nc vr \<and> (fst a, nc) \<in> set ntons)"
  and "\<forall>a. (a \<in> set as \<and> atom_var (snd a) < start) \<longrightarrow>
    (\<exists>vr nc. vars (poly nc) = {atom_var (snd a)} \<and> (snd a) = qdelta_constraint_to_atom nc vr
      \<and> (fst a, nc) \<in> set ntons)"
proof -
  show "\<forall>a. a \<in> set as \<longrightarrow>
    (\<exists>vr nc. (snd a) = qdelta_constraint_to_atom nc vr \<and> (fst a, nc) \<in> set ntons)"
  unfolding assms
  proof (induct ntons start rule: preprocess'.induct)
    case (2 i h t v)
    then show ?case
    proof (intro allI impI, goal_cases)
      case (1 a)
      then show ?case
      proof (cases "a \<in> set (Atoms (preprocess' t v))")
        case True
        then show ?thesis using 1 by fastforce
      next
        case new: False
        then have "fst a = i" using 1(2) by(auto simp: Let_def split: if_splits option.splits)
        then show ?thesis
        proof (cases "is_monom (poly h)")
          case True
          then show ?thesis using new 1(2) by (auto simp: Let_def)
        next
          case False
          then show ?thesis using new 1(2) by (auto simp: Let_def split: option.splits if_splits)
        qed
      qed
    qed
  qed auto

  show "\<forall>a. (a \<in> set as \<and> atom_var (snd a) < start) \<longrightarrow>
    (\<exists>vr nc. vars (poly nc) = {atom_var (snd a)} \<and> (snd a) = qdelta_constraint_to_atom nc vr
      \<and> (fst a, nc) \<in> set ntons)"
  unfolding assms
  proof (induct ntons start rule: preprocess'.induct)
    case (2 i h t v)
    then show ?case
    proof (intro allI impI, goal_cases)
      case (1 a)
      show ?case
      proof (cases "a \<in> set (Atoms (preprocess' t v))")
        case True
        then show ?thesis using 1 by fastforce
      next
        case a_nin_prepr_t: False
        then have a_is_hd: "a = hd (Atoms (preprocess' ((i, h) # t) v))"
          using 1 by (auto simp: Let_def split: option.splits if_splits)
        have hnz: "poly h \<noteq> 0"
          using a_nin_prepr_t 1 by (auto simp: Let_def split: option.splits if_splits)
        define ff where "ff = (FirstFreshVariable (preprocess' t v))"
        have ff_gt_iatm: "ff > atom_var (snd a)"
          by (metis 1(2) ff_def fresh_var_monoinc less_trans linorder_neqE_nat not_le)
        show ?thesis
        proof(cases "is_monom (poly h)")
          case h_monom: True
          then have a: "a = (i, qdelta_constraint_to_atom h ff)"
            using 1 ff_def a_nin_prepr_t
            by (auto simp: Let_def split: option.splits if_splits)
          then have snd_a: "snd a = qdelta_constraint_to_atom h ff" by simp
          show ?thesis
          proof(cases "vars (poly (snd (i,h))) = {atom_var (snd a)}")
            case h_eq_iatm: True
            have "\<forall>vr'. atom_var (qdelta_constraint_to_atom h vr') = monom_var (poly h)"
              by (metis qdelta_constraint_to_atom.simps poly.simps monom_to_atom.simps
                  atom_var.simps lec_of_nsc.cases h_monom)
            then have "vars (poly h) = {atom_var (snd a)}"
              using 1 is_monom_vars_monom_var h_monom h_eq_iatm by auto
            then show ?thesis using 1 single_var_poly_is_monom a_nin_prepr_t
              by (auto simp: Let_def split: option.splits if_splits)
          next
            case h_monom_neq_iatm: False
            obtain ov where "vars (poly h) = {ov}" and ov: "ov \<noteq> atom_var (snd a)"
              using h_monom_neq_iatm is_monom_vars_monom_var h_monom by simp
            then have "monom_var (poly h) = ov" using h_monom monom_var_in_vars by blast
            then have "atom_var (snd a) = ov"
              by (cases "poly h", metis h_monom atom_var.simps lec_of_nsc.cases snd_a
                  monom_to_atom.simps poly.simps qdelta_constraint_to_atom.simps)
            then have False using 1 ov by simp
            then show ?thesis by simp
          qed
        next
          case h_not_monom: False
          then show ?thesis
          proof (cases "Poly_Mapping (preprocess' t v) (poly h) = None")
            case True
            have "atom_var (qdelta_constraint_to_atom h ff) = ff" using h_not_monom ff_def
              by (metis atom_var.simps qdelta_constraint_to_atom.simps lec_of_nsc.cases poly.simps)
            then have "snd a \<noteq> qdelta_constraint_to_atom h ff" using ff_gt_iatm 1(2) by fastforce
            then have "a \<noteq> hd (Atoms (preprocess' ((i, h) # t) v))" using hnz h_not_monom ff_def
              by (auto simp: Let_def True split: option.splits if_splits)
            then have False using a_is_hd by blast
            then show ?thesis by simp
          next
            case False
            then obtain vr where vr: "Poly_Mapping (preprocess' t v) (poly h) = Some vr" by auto
            then have "vr \<ge> v" using firstfresh_ge_start by auto
            then have vrav: "vr > atom_var (snd a)" using 1 by linarith
            have "atom_var (qdelta_constraint_to_atom h vr) = vr" using h_not_monom
              by (metis atom_var.simps qdelta_constraint_to_atom.simps lec_of_nsc.cases poly.simps)
            then have "snd a \<noteq> (qdelta_constraint_to_atom h vr)" using vrav 1(2) by fastforce
            then have "a \<noteq> hd (Atoms (preprocess' ((i, h) # t) v))" using hnz h_not_monom vr
              by (auto simp: Let_def split: option.splits if_splits)
            then have False using a_is_hd by blast
            then show ?thesis by simp
          qed
        qed
      qed
    qed
  qed auto
qed

lemma bnb_update_del:
  assumes "state_invariant cs Is lb ub s"
    "cs' = i_bounds_to_constraints Is lb ub @ cs"
    "suitable_upd_atom iatm cs'"
    "s' = del_atom_from_state'' s iatm"
  shows "\<exists> J. set J \<subseteq> (set (remove1 (fst iatm) (map fst cs')))
    \<and> invariant_simplex cs' (set J) s'"
proof -
  define tons where "tons = to_ns cs'"
  define idxs where "idxs = set (map fst tons)"
  let ?eq_iatm_poly = "(\<lambda>x. vars (poly (snd x)) = {atom_var (snd iatm)})"
  have polyvar: "poly (snd x) = Var (atom_var (snd iatm)) \<Longrightarrow> ?eq_iatm_poly x "
    for x :: "nat \<times> QDelta ns_constraint" by simp
  have idxs: "idxs = set (map fst (to_ns cs'))" using tons_def idxs_def by simp
  define del_idxs where
    "del_idxs = set (map fst (filter ?eq_iatm_poly tons))"
  define J where "J = filter (\<lambda>i. i \<notin> del_idxs) (map fst tons)"
  have seteq: "set (map fst cs') = set (map fst tons)"
    using tons_def by (metis SolveExec'Default.to_ns_indices set_map)
  have "fst iatm \<in> del_idxs"
    using tons_def del_idxs_def assms(3) polyvar nth_find_index suitable_upd_atom_def
    by (smt image_eqI mem_Collect_eq not_less nth_mem set_filter set_map)
  then have J: "set J \<subseteq> (set (remove1 (fst iatm) (map fst cs')))"
    using seteq J_def filter_is_subset filter_remove1 remove1_filter_not filter_set by metis

  obtain ncs asitv l3s where 1: "s = Simplex_State (ncs, asitv, l3s)"
    using check_simplex.cases by blast
  obtain ncs' asitv' l3s' where 2: "s' = Simplex_State (ncs', asitv', l3s')"
    using check_simplex.cases by blast
  have "ncs' = ncs" and "asitv = asitv'" using assms(4) 1 2
    unfolding del_atom_from_state''_def by (auto split: atom.splits state.splits)
  moreover obtain asi tv ui where asitv: "asitv = (asi, tv, ui)"
    using Product_Type.prod_cases3 by blast
  ultimately have s'id: "s' = Simplex_State (ncs, (asi, tv, ui), l3s')" using 2 by simp
  have inv_nsc: "invariant_nsc tons idxs ((asi,tv,ui),l3s)"
    by (metis assms(1) state_invariant_def seteq assms(2) invariant_simplex.simps tons_def idxs_def
        1 Incremental_Simplex.invariant_cs.simps asitv image_set)

  obtain tt as tv' ui' where prepr: "preprocess tons = (tt,as,tv',ui')"
    using Product_Type.prod_cases4 by blast
  define as_s where "as_s = set as \<inter> (idxs \<times> UNIV)"
  define as_s' where "as_s' = set as \<inter> (set J \<times> UNIV)"

  have Jidx: "set J = idxs - del_idxs" using del_idxs_def idxs_def J_def by auto
  have Jidx2: "del_idxs = idxs - (set J)" using del_idxs_def idxs_def J_def by auto

  (* The following says that non-strict indexed constraints from (to_ns cs') that have the same
    index, also have the same linear polynomial. *)
  have tons_idx: "i < length tons \<Longrightarrow> poly (snd (tons ! i)) = x
    \<Longrightarrow> (\<forall>j < length tons. fst (tons ! j) = fst (tons ! i) \<longrightarrow> poly (snd (tons ! j)) = x)" for x i
  proof -
    assume x: "poly (snd (tons ! i)) = x"
    assume "i < length tons"
    then obtain cs_i where tonsi: "tons ! i \<in> set ((map i_constraint_to_qdelta_constraint cs') ! cs_i)"
      and cs_i_len: "cs_i < length cs'"
      using tons_def to_ns_def nth_concat_split nth_mem by (metis length_map)

    have cs'k: "(i_constraint_to_qdelta_constraint (cs' ! k))
        = map (Pair (fst (cs' ! k))) (constraint_to_qdelta_constraint (snd (cs' ! k)))" for k
      by (metis i_constraint_to_qdelta_constraint.simps prod.collapse)

    have fel: "\<forall>el \<in> set (i_constraint_to_qdelta_constraint (cs' ! k)).
      fst el = fst (cs' ! k)" for k
      using find_index_in_set i_constraint_to_qdelta_constraint_def cs'k by simp
    have fel2: "el \<in> set (i_constraint_to_qdelta_constraint (cs' ! k)) \<Longrightarrow>
      (\<forall>el2 \<in> set (i_constraint_to_qdelta_constraint (cs' ! k)). poly (snd el) = poly (snd el2))" for el k
    proof -
      assume el: "el \<in> set (i_constraint_to_qdelta_constraint (cs' ! k))"
      then have sndel: "snd el \<in> set (constraint_to_qdelta_constraint (snd (cs' ! k)))"
        using cs'k by auto
      {
        fix el2
        assume "el2 \<in> set (i_constraint_to_qdelta_constraint (cs' ! k))"
        then have "snd el2 \<in> set (constraint_to_qdelta_constraint (snd (cs' ! k)))" using cs'k by auto
        moreover have "\<forall>el1 el2.
          {el1, el2} \<subseteq> set (constraint_to_qdelta_constraint nc) \<longrightarrow> poly el1 = poly el2" for nc
          by (cases nc, auto)
        ultimately have "poly (snd el2) = poly (snd el)" using sndel by blast
      }
      then show ?thesis by simp
    qed

    {
      fix j
      assume "j < length tons" moreover
      assume "fst (tons ! j) = fst (tons ! i)" moreover
      obtain cs_j where tonsj: "tons ! j \<in> set ((map i_constraint_to_qdelta_constraint cs') ! cs_j)"
        and cs_j_len: "cs_j < length cs'"
        using tons_def to_ns_def nth_concat_split nth_mem calculation by (metis length_map)
      then have "fst (tons ! j) = fst (cs' ! cs_i)" using fel calculation cs_i_len tonsi by auto
      moreover have "distinct (map fst cs')"
          using assms(1,2) unfolding state_invariant_def by (meson enumerated_distinct)
      ultimately have "poly (snd (tons ! j)) = poly (snd (tons ! i))"
        using fel2 tonsi tonsj cs_j_len cs_i_len
        by (metis (no_types, lifting) distinct_conv_nth fel length_map map_nth_eq_conv)
    }
    then show ?thesis using x by blast
  qed

  have tons_del: "\<forall>i < length tons. (fst (tons ! i) \<in> del_idxs \<longrightarrow> ?eq_iatm_poly (tons ! i))"
  proof -
    {
      fix i
      assume ilen: "i < length tons"
      assume "fst (tons ! i) \<in> del_idxs"
      then obtain c where "c \<in> set (filter ?eq_iatm_poly tons)"
        and "fst c = fst (tons ! i)" using del_idxs_def by auto
      then have "?eq_iatm_poly (tons ! i)" using tons_idx ilen
        by (metis (mono_tags) in_set_conv_nth mem_Collect_eq set_filter)
      then have "(fst (tons ! i) \<in> del_idxs \<longrightarrow> ?eq_iatm_poly (tons ! i))"
        by simp
    }
    then show ?thesis by auto
  qed

  define ntons where "ntons = (map (map_prod id normalize_ns_constraint) tons)"
  define prstart where "prstart = start_fresh_variable ntons"
  have avstart: "atom_var (snd iatm) < prstart"
  proof -
    obtain i where "fst (tons ! i) \<in> del_idxs" and ilen: "i < length tons"
      by (metis DiffE Jidx2 \<open>fst iatm \<in> del_idxs\<close> idxs_def imageE in_set_conv_nth set_map)
    then have "vars (poly (snd (ntons ! i))) = {atom_var (snd iatm)}" using ntons_def tons_del
      by (simp add: ilen normalize_ns_constraint_vars_eq)
    then have "atom_var (snd iatm) \<in> vars_constraints (Simplex.flat_list ntons)"
      using ilen nth_mem ntons_def by auto
    then show ?thesis unfolding prstart_def using start_fresh_variable_fresh by auto
  qed
  have "preprocess tons = (case preprocess_part_1 (map (map_prod id normalize_ns_constraint) tons) of
    (t,as,ui) \<Rightarrow> case preprocess_part_2 as t of (t,tv) \<Rightarrow> (t,as,tv,ui))" using preprocess_def by auto
  moreover obtain tp asp uip where
    "preprocess_part_1 (map (map_prod id normalize_ns_constraint) tons) = (tp, asp, uip)"
    using prod_cases3 by blast
  moreover then obtain tpp and tvpp :: "(nat, QDelta) mapping \<Rightarrow> (nat, QDelta) mapping" where
    "preprocess_part_2 asp tp = (tpp , tvpp)" by fastforce
  ultimately moreover have "asp = as" using prepr by auto
  ultimately have asat: "as = Atoms (preprocess' ntons prstart)" using ntons_def prstart_def
    by (metis (no_types, lifting) Pair_inject preprocess_part_1_def)

  have as_s': "\<forall>a \<in> set as. atom_var (snd a) = atom_var (snd iatm) \<longleftrightarrow> fst a \<in> del_idxs"
  proof -
    {
      fix a
      assume a: "a \<in> set as"
      {
        assume "atom_var (snd a) = atom_var (snd iatm)"
        then obtain nc where p1: "vars (poly nc) = {atom_var (snd iatm)}"
          and "(fst a, nc) \<in> set ntons"
          by (metis preprocess'_iatom_from_insconstr[OF asat] a avstart)
        then obtain inc where "(fst a, nc) = (map_prod id normalize_ns_constraint) inc" and
          "inc \<in> set tons" using ntons_def by auto
        moreover then have "fst inc \<in> del_idxs"
          using del_idxs_def snd_conv snd_map_prod p1 normalize_ns_constraint_vars_eq
          by (smt image_eqI mem_Collect_eq set_filter set_map)
        ultimately have "fst a \<in> del_idxs"
          by (metis fst_conv id_apply map_prod_simp prod.collapse)
      } moreover
      {
        assume fsta: "fst a \<in> del_idxs"
        then obtain vr nc where "(fst a, nc) \<in> set ntons"
          and anc: "snd a = qdelta_constraint_to_atom nc vr"
          using preprocess'_iatom_from_insconstr[OF asat] a by blast
        then obtain inc where ncinc: "(fst a, nc) = (map_prod id normalize_ns_constraint) inc" and
          incs: "inc \<in> set tons" using ntons_def by auto
        then have ncinc2: "nc = normalize_ns_constraint (snd inc)" by (metis snd_conv snd_map_prod)
        have "fst inc \<in> del_idxs" by (metis fsta ncinc fst_conv fst_map_prod id_apply)
        then have iatm: "?eq_iatm_poly inc" using tons_del in_set_conv_nth incs by metis
        have ism: "is_monom (poly nc)" using ncinc2 iatm single_var_poly_is_monom
          by (metis single_var_poly_is_monom normalize_ns_constraint_vars_eq)
        then have "monom_var (poly nc) = atom_var (snd iatm)" using iatm
          using monom_var_in_vars ncinc2 normalize_ns_constraint_vars_eq by auto
        then have "atom_var (snd a) = atom_var (snd iatm)"
          by (cases "poly nc", metis anc ism atom_var.simps lec_of_nsc.cases monom_to_atom.simps
              poly.simps qdelta_constraint_to_atom.simps)
      }
      ultimately have "atom_var (snd a) = atom_var (snd iatm) \<longleftrightarrow> fst a \<in> del_idxs" by auto
    }
    then show ?thesis by auto
  qed

  then have as_s'': "\<forall>a \<in> set as. atom_var (snd a) = atom_var (snd iatm) \<longleftrightarrow> a \<in> as_s - as_s'"
    using Jidx2 as_s_def as_s'_def Diff_Int_distrib Int_iff Sigma_Diff_distrib1 vimage_eq vimage_fst
    by auto

  have l3s_inv_s: "invariant_s tt as_s l3s" using inv_nsc prepr as_s_def by simp
  obtain t iub ilb v c uc where l3s_descrip: "l3s = (State t ilb iub v c uc)"
    using Simplex.state.exhaust by blast
  obtain t' iub' ilb' v' c' uc' where "l3s' = (State t' ilb' iub' v' c' uc')"
    using Simplex.state.exhaust by blast
  then have l3s'_descrip: "l3s' = (State t ilb' iub' v c uc)" using l3s_descrip assms(4) 1 2
    unfolding del_atom_from_state''_def by auto
  then have ilb': "ilb' = Mapping.delete (atom_var (snd iatm)) ilb"
    using assms(4) l3s_descrip 1 2 unfolding del_atom_from_state''_def by auto
  have iub': "iub' = Mapping.delete (atom_var (snd iatm)) iub" using assms(4) l3s_descrip
      l3s'_descrip 1 2 unfolding del_atom_from_state''_def by auto

  have bnds_eq_l: "\<B>\<^sub>l l3s' x \<noteq> None \<Longrightarrow> \<B>\<^sub>l l3s' x = \<B>\<^sub>l l3s x" for x
    by (metis l3s'_descrip ilb' boundsl_def comp_apply mapping_del option.simps(8) state.sel(2)
      l3s_descrip)

  have bnds_eq_u: "\<B>\<^sub>u l3s' x \<noteq> None \<Longrightarrow> \<B>\<^sub>u l3s' x = \<B>\<^sub>u l3s x" for x
    by (metis l3s'_descrip iub' boundsu_def comp_apply mapping_del option.simps(8) state.sel(3)
      l3s_descrip)

  (* Main part of this proof: showing that the layer 3 invariant is satisfied by the state
    produced by the deletion of a pair of bounds. *)
  have l3s'_inv_s: "invariant_s tt as_s' l3s'"
  proof -
    have "\<not> \<U> l3s'" using l3s'_descrip l3s_descrip l3s_inv_s unfolding invariant_s_def
      using Incremental_State_Ops_Simplex_Default.invariant_sD(1) l3s_inv_s state.sel(5) by blast

    moreover have "\<triangle> (\<T> l3s')"
      using l3s_descrip l3s'_descrip l3s_inv_s Incremental_State_Ops_Simplex_Default.invariant_sD(3)
      by fastforce

    moreover have "\<nabla> l3s'"
    proof -
      have "\<nabla> l3s" using l3s_inv_s Incremental_State_Ops_Simplex_Default.invariant_sD(4) by blast
      then show ?thesis using l3s_descrip l3s'_descrip by (simp add: tableau_valuated_def)
    qed

    moreover have "\<diamond> l3s'"
      using l3s_inv_s Incremental_State_Ops_Simplex_Default.invariant_sD(5) bnds_eq_l bnds_eq_u
        by (metis bounds_consistent_def)

    moreover have "(\<forall> v :: (nat \<Rightarrow> QDelta). v \<Turnstile>\<^sub>t \<T> l3s' \<longleftrightarrow> v \<Turnstile>\<^sub>t tt)"
      using l3s_descrip l3s'_descrip
        Incremental_State_Ops_Simplex_Default.invariant_sD(9)[OF l3s_inv_s] by simp

    moreover have "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s l3s'"
    proof -
      have "(\<forall> x \<in> (- lvars t). \<langle>v\<rangle> x \<ge>\<^sub>l\<^sub>b \<B>\<^sub>l l3s x \<and> \<langle>v\<rangle> x \<le>\<^sub>u\<^sub>b \<B>\<^sub>u l3s x)"
        using curr_val_satisfies_no_lhs_def satisfies_bounds_set_iff l3s_descrip l3s_inv_s
          Incremental_State_Ops_Simplex_Default.invariant_sD(2)
        by (metis state.sel(1) state.sel(4))
      then have "(\<forall> x \<in> (- lvars t). \<langle>v\<rangle> x \<ge>\<^sub>l\<^sub>b \<B>\<^sub>l l3s' x \<and> \<langle>v\<rangle> x \<le>\<^sub>u\<^sub>b \<B>\<^sub>u l3s' x)"
        using bnds_eq_l bnds_eq_u option.case_eq_if l3s_descrip l3s'_descrip ilb'
        unfolding ge_lbound_def gelb_def le_ubound_def leub_def by (metis (no_types, lifting))
      then show ?thesis
        using l3s'_descrip l3s_descrip l3s_inv_s Incremental_State_Ops_Simplex_Default.invariant_sD(2)
        by (metis curr_val_satisfies_no_lhs_def satisfies_bounds_set_iff state.sel(1) state.sel(4))
    qed

    moreover have indval': "index_valid as_s' l3s'"
    proof -
      have ind_val: "index_valid as_s l3s" using inv_nsc l3s_inv_s unfolding as_s_def
        using Incremental_State_Ops_Simplex_Default.invariant_sD(8) by blast
      {
        fix x b j
        assume lkp: "Mapping.lookup ilb' x = Some (j,b)"
        then have xneq: "x \<noteq> atom_var (snd iatm)" using ilb' by auto
        then have "Mapping.lookup ilb x = Some (j,b)" using l3s_descrip l3s'_descrip ilb' lkp by simp
        then have "(j, Geq x b) \<in> as_s" using ind_val by (simp add: index_valid_def l3s_descrip)
        moreover have "(j, Geq x b) \<in> set as"
          using index_valid_def l3s_descrip ind_val as_s_def calculation by blast
        ultimately have "(j, Geq x b) \<in> as_s'" using as_s'' xneq by auto
      }
      moreover
      {
        fix x b j
        assume lkp: "Mapping.lookup iub' x = Some (j,b)"
        then have xneq: "x \<noteq> atom_var (snd iatm)" using iub' by auto
        then have "Mapping.lookup iub x = Some (j,b)" using l3s_descrip l3s'_descrip iub' lkp by simp
        then have "(j, Leq x b) \<in> as_s" using ind_val by (simp add: index_valid_def l3s_descrip)
        moreover have "(j, Leq x b) \<in> set as"
          using index_valid_def l3s_descrip ind_val as_s_def calculation by blast
        ultimately have "(j, Leq x b) \<in> as_s'" using as_s'' xneq by auto
      }
      ultimately show ?thesis using l3s'_descrip unfolding index_valid_def by simp
    qed

    moreover have "Simplex.flat as_s' \<doteq> \<B> l3s'"
    proof -
      have doteq: "Simplex.flat as_s \<doteq> \<B> l3s"
        using l3s_descrip l3s_inv_s Incremental_State_Ops_Simplex_Default.invariant_sD(6) by auto
      let ?upd = "(if \<B>\<^sub>l l3s (atom_var (snd iatm)) = None then
          (if \<B>\<^sub>u l3s (atom_var (snd iatm)) = None then 0 else the (\<B>\<^sub>u l3s (atom_var (snd iatm))))
          else the (\<B>\<^sub>l l3s (atom_var (snd iatm))))"
      have "\<forall>v'. v' \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s') \<longrightarrow> v' \<Turnstile>\<^sub>b \<B> l3s'"
      proof (rule ccontr)
        assume "\<not> (\<forall>v'. v' \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s') \<longrightarrow> v' \<Turnstile>\<^sub>b \<B> l3s')"
        from this obtain v'
          where v'as: "v' \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s')" and nv'B: "\<not> (v' \<Turnstile>\<^sub>b \<B> l3s')" by auto
        then have "\<exists>x. (v' x <\<^sub>l\<^sub>b (\<B>\<^sub>l l3s') x \<or> v' x >\<^sub>u\<^sub>b (\<B>\<^sub>u l3s') x)"
          using neg_bounds_compare(3) neg_bounds_compare(7) satisfies_bounds_iff by blast
        from this obtain x where "(v' x <\<^sub>l\<^sub>b (\<B>\<^sub>l l3s') x \<or> v' x >\<^sub>u\<^sub>b (\<B>\<^sub>u l3s') x)" by auto
        moreover {
          assume "v' x <\<^sub>l\<^sub>b (\<B>\<^sub>l l3s') x"
          moreover then have "(\<B>\<^sub>l l3s') x \<noteq> None"
            by (smt bound_compare_defs(15) bound_compare_defs(5) bounds_compare_contradictory(7)
                option.case_eq_if)
          then obtain i b where "Mapping.lookup (\<B>\<^sub>i\<^sub>l l3s') x = Some (i, b)" using boundsl_def
            by (metis None_eq_map_option_iff comp_apply old.prod.exhaust option.exhaust)
          moreover then have "(\<B>\<^sub>l l3s') x = Some b" by (simp add: boundsl_def)
          moreover have "v' x < b" using calculation by (simp add: boundsl_def)
          have "\<not> (v' \<Turnstile>\<^sub>a (Geq x b))" using calculation by simp
          ultimately moreover have "(i, Geq x b) \<in> as_s'" using indval' by (simp add: index_valid_def)
          then have "Geq x b \<in> Simplex.flat as_s'" by force
          ultimately have "\<not> (v' \<Turnstile>\<^sub>a\<^sub>s Simplex.flat as_s')" by (meson satisfies_atom_set_def)
        } moreover
        {
          assume "v' x >\<^sub>u\<^sub>b (\<B>\<^sub>u l3s') x"
          moreover then have "(\<B>\<^sub>u l3s') x \<noteq> None"
            using bound_compare_defs(10) bound_compare_defs(2) option.case_eq_if by metis
          then obtain i b where "Mapping.lookup (\<B>\<^sub>i\<^sub>u l3s') x = Some (i, b)" using boundsu_def
            by (metis None_eq_map_option_iff comp_apply old.prod.exhaust option.exhaust)
          moreover then have "(\<B>\<^sub>u l3s') x = Some b" by (simp add: boundsu_def)
          moreover then have "v' x > b" using calculation by simp
          have "\<not> (v' \<Turnstile>\<^sub>a (Leq x b))" using calculation by simp
          ultimately moreover have "(i, Leq x b) \<in> as_s'" using indval' by (simp add: index_valid_def)
          then have "Leq x b \<in> Simplex.flat as_s'" by force
          ultimately have "\<not> (v' \<Turnstile>\<^sub>a\<^sub>s Simplex.flat as_s')" by (meson satisfies_atom_set_def)
        }
        ultimately show False using v'as by auto
      qed
      moreover
      {
        fix v'
        define v where  "v = v' ((atom_var (snd iatm)) := ?upd)"
        assume v'b: "v' \<Turnstile>\<^sub>b \<B> l3s'"
        then have "v \<Turnstile>\<^sub>b \<B> l3s"
        proof -
          {
            fix x
            have "v x \<ge>\<^sub>l\<^sub>b (\<B>\<^sub>l l3s) x \<and> v x \<le>\<^sub>u\<^sub>b (\<B>\<^sub>u l3s) x"
            proof (cases "x = (atom_var (snd iatm))")
              case True
              then show ?thesis using bound_compare_defs option.case_eq_if
                by (smt Incremental_State_Ops_Simplex_Default.invariant_sD(5)
                    bounds_consistent_leq_ub fun_upd_same l3s_inv_s option.expand option.sel
                    option.simps(3) v_def)
            next
              case False
              then have "v x \<ge>\<^sub>l\<^sub>b (\<B>\<^sub>l l3s') x \<and> v x \<le>\<^sub>u\<^sub>b (\<B>\<^sub>u l3s') x"
                using v'b ilb' iub' l3s'_descrip l3s_descrip satisfies_bounds_iff
                by (metis (no_types, lifting) fun_upd_other v_def)
              then show ?thesis using False
                by (simp add: boundsl_def boundsu_def ilb' iub' l3s'_descrip l3s_descrip)
            qed
          }
          then show ?thesis using satisfies_bounds_iff by blast
        qed
        then have "v \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s)" using doteq atoms_equiv_bounds.simps by blast
        then have vas: "v \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s')" using as_s'_def
          by (simp add: Jidx Sigma_Diff_distrib1 as_s_def satisfies_atom_set_def)
        then have "v' \<Turnstile>\<^sub>a\<^sub>s (Simplex.flat as_s')"
        proof -
          have xneq: "\<forall>x. x \<noteq> atom_var (snd iatm) \<longrightarrow> v' x = v x" using v_def by simp
          have "\<forall>a \<in> Simplex.flat as_s'. atom_var a \<noteq> atom_var (snd iatm)" using as_s'' as_s'_def by blast
          then have "\<forall>a \<in> Simplex.flat as_s'. v' \<Turnstile>\<^sub>a a \<longleftrightarrow> v \<Turnstile>\<^sub>a a" using xneq
            by (metis (full_types) atom_var.simps nsc_of_atom.cases satisfies_atom.simps
                satisfies_atom_set_def vas)
          then show ?thesis using vas by (simp add: satisfies_atom_set_def)
        qed
      }
      ultimately have "(\<forall> v. v \<Turnstile>\<^sub>a\<^sub>s Simplex.flat as_s' \<longleftrightarrow> v \<Turnstile>\<^sub>b \<B> l3s')" by auto
      then show ?thesis by (simp add: atoms_equiv_bounds_simps)
    qed

    moreover have "as_s' \<Turnstile>\<^sub>i \<B>\<I> l3s'"
    proof -
      have BIl: "(\<B>\<^sub>l l3s') x \<noteq> None \<Longrightarrow> (\<I>\<^sub>l l3s') x \<notin> del_idxs" for x
      proof -
        assume "(\<B>\<^sub>l l3s') x \<noteq> None"
        then obtain i b where "Mapping.lookup (\<B>\<^sub>i\<^sub>l l3s') x = Some (i, b)" using boundsl_def
          by (metis None_eq_map_option_iff comp_apply old.prod.exhaust option.exhaust)
        moreover then have "(\<I>\<^sub>l l3s') x = i" by (simp add: indexl_def)
        moreover have "(i, Geq x b) \<in> as_s'" using indval' calculation by (simp add: index_valid_def)
        ultimately have "(\<I>\<^sub>l l3s') x \<notin> del_idxs" using as_s'' IntE as_s' as_s'_def by auto
        then show ?thesis by simp
      qed

      have BIu: "(\<B>\<^sub>u l3s') x \<noteq> None \<Longrightarrow> (\<I>\<^sub>u l3s') x \<notin> del_idxs" for x
      proof -
        assume "(\<B>\<^sub>u l3s') x \<noteq> None"
        then obtain i b where "Mapping.lookup (\<B>\<^sub>i\<^sub>u l3s') x = Some (i, b)" using boundsu_def
          by (metis None_eq_map_option_iff comp_apply old.prod.exhaust option.exhaust)
        moreover then have "(\<I>\<^sub>u l3s') x = i" by (simp add: indexu_def)
        moreover have "(i, Leq x b) \<in> as_s'" using indval' calculation by (simp add: index_valid_def)
        ultimately have "(\<I>\<^sub>u l3s') x \<notin> del_idxs" using as_s'' IntE as_s' as_s'_def by auto
        then show ?thesis by simp
      qed

      {
        fix I v
        assume "(I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as_s'"
        then have "(I - del_idxs, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as_s" using Jidx as_s'_def as_s_def
          by (metis Int_Diff Diff_Int2 Diff_Int_distrib2
              Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.i_satisfies_atom_set_inter_right)
        then have "(I - del_idxs, v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> l3s" by (meson atoms_imply_bounds_index.elims(2)
           Incremental_State_Ops_Simplex_Default.invariant_sD(7) l3s_inv_s)
        then have Idib: "(I - del_idxs, v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> l3s'" using l3s'_descrip l3s_descrip ilb' iub'
          by (simp add: boundsl_def boundsu_def indexl_def indexu_def satisfies_bounds_index.simps)
        have "(I, v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> l3s'"
        proof -
          {
            fix x c
            have "((\<B>\<^sub>l l3s') x = Some c \<longrightarrow> (\<I>\<^sub>l l3s') x \<in> I \<longrightarrow> v x \<ge> c) \<and>
              ((\<B>\<^sub>u l3s') x = Some c \<longrightarrow> (\<I>\<^sub>u l3s') x \<in> I \<longrightarrow> v x \<le> c)"
              using BIl BIu Idib satisfies_bounds_index.simps by (simp add: satisfies_bounds_index.simps)
          }
          then show ?thesis by (simp add: satisfies_bounds_index.simps)
        qed
      }
      then show ?thesis using atoms_imply_bounds_index.simps by blast
    qed

    ultimately show ?thesis unfolding Incremental_State_Ops_Simplex_Default.invariant_s_def
      using Incremental_State_Ops_Simplex_Default.invariant_defs by blast
  qed

  have "invariant_nsc tons (set J) ((asi, tv, ui), l3s')"
  proof -
    have "Incremental_Atom_Ops_For_NS_Constraint_Ops.invariant_as_asi (set as) asi tv tv' ui ui'"
      using inv_nsc prepr s'id by simp
    moreover have "invariant_s tt (set as \<inter> ((set J) \<times> UNIV)) l3s' \<and> (set J) \<inter> set ui' = {}"
      using l3s'_inv_s as_s'_def prepr inv_nsc Jidx by auto
    ultimately show ?thesis using prepr by simp
  qed
  then have "invariant_simplex cs' (set J) s'" using tons_def
    by (metis "1" Incremental_Simplex.invariant_cs.simps assms(1) assms(2) invariant_simplex.simps
        state_invariant_def s'id)
  then show ?thesis using J by blast
qed

lemma bnb_update_assertall:
  assumes "state_invariant cs Is lb ub s"
    "cs' = i_bounds_to_constraints Is lb ub @ cs"
    "suitable_upd_atom iatm cs'"
    "atom_var (snd iatm) \<in> set Is"
    "assert_all_simplex (remove1 (fst iatm) (map fst cs')) (del_atom_from_state'' s iatm) = Sat s'"
  shows "invariant_simplex cs' (set (remove1 (fst iatm) (map fst cs'))) s'"
proof -
  define Ai where "Ai = (remove1 (fst iatm) (map fst cs'))"
  let ?s' = "del_atom_from_state'' s iatm"
  obtain J where "set J \<subseteq> (set Ai)" and "invariant_simplex cs' (set J) ?s'"
    using assms bnb_update_del unfolding Ai_def by blast
  then show ?thesis using Ai_def assert_all_simplex_ok assms(4) le_iff_sup assms by metis
qed


lemma bnb_update1:
  assumes
    "checked_bnc cs Is lb ub s"
    "cs' = i_bounds_to_constraints Is lb ub @ cs"
    "suitable_upd_atom iatm cs'"
    "idx_list = map fst cs'"
  shows "\<exists>s'. assert_all_simplex (remove1 (fst iatm) idx_list) (del_atom_from_state'' s iatm) = Sat s'
    \<and> invariant_simplex cs' (set (remove1 (fst iatm) idx_list)) s'"
proof -
  define d where "d = del_atom_from_state'' s iatm"
  have "state_invariant cs Is lb ub s"
    using assms checked_invariant_bnc by auto
  then obtain js where js: "set js \<subseteq> set (remove1 (fst iatm) (map fst cs'))" "invariant_simplex cs' (set js) d"
    using assms bnb_update_del unfolding d_def by blast
  have "set (remove1 (fst iatm) (map fst cs')) = fst ` set cs' - {fst iatm}"
    apply(subst set_remove1_eq)
    using assms enumerated_distinct[of 0 cs'] enumerated_sorted unfolding checked_bnc_def by (auto simp add: Let_def)
  have "\<exists>s'. assert_all_simplex (remove1 (fst iatm) idx_list) d = Sat s'"
  proof (rule ccontr)
    assume "\<nexists>s'. assert_all_simplex (remove1 (fst iatm) idx_list) d = Inr s'"
    then have "\<exists>ix. assert_all_simplex (remove1 (fst iatm) idx_list) d = Unsat ix"
      by (meson sumE)
    then obtain ix where ix: "assert_all_simplex (remove1 (fst iatm) idx_list) d = Unsat ix"
      by blast
    have "minimal_unsat_core (set ix) cs'"
      using assert_all_simplex_unsat js ix by blast
    moreover have "(fst  `set cs', solution_simplex s) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs'"
      by (intro solution_simplex) (use assms in \<open>auto simp add: checked_bnc_def Let_def\<close>)
    ultimately show False
      unfolding minimal_unsat_core_def by force
  qed
  then obtain s' where s': "assert_all_simplex (remove1 (fst iatm) idx_list) d = Sat s'"
    by blast
  then have "invariant_simplex cs' (set js \<union> set (remove1 (fst iatm) idx_list)) s'"
    using js by (auto intro: assert_all_simplex_ok)
  also have "set js \<union> set (remove1 (fst iatm) idx_list) = set (remove1 (fst iatm) idx_list)"
    using js assms by blast
  finally show ?thesis
    using s' by (auto simp add: d_def)
qed


lemma Var_eqI: "Var x = Var y \<Longrightarrow> x = y"
  using coeff_Var2 by force

lemma concat_map_list_update: "(\<forall>x \<in> set cs \<union> {x}. f x = [hd (f x)]) \<Longrightarrow>
   concat (map f (cs[i := x])) = (concat (map f cs))[i := hd (f x)]"
proof (induction cs arbitrary: i)
  case (Cons c cs)
  show ?case
  proof (cases "i = 0")
    case False
    have "concat (map f ((c # cs)[i := x])) = f c @ concat (map f (cs[i - 1 := x]))"
      using False by (auto split: nat.splits)
    also have "concat (map f (cs[i - 1 := x])) = (concat (map f cs))[i - 1 := hd (f x)]"
      using Cons by simp
    also have "f c @ \<dots> = hd (f c) # (concat (map f cs))[i - 1 := hd (f x)]"
      using Cons by auto
    also have "\<dots> = (hd (f c) # (concat (map f cs)))[i := hd (f x)]"
      using False by (auto split: nat.splits)
    also have "hd (f c) # (concat (map f cs)) = (f c) @ (concat (map f cs))"
      using Cons by simp
    finally show ?thesis
      using Cons False by (auto split: nat.splits)
  next
    case True
    have "(f c @ concat (map f cs)) = hd (f c) # concat (map f cs)"
      using Cons by auto
    then show ?thesis
      using Cons True by (auto) (metis append_Cons list_update_code(2))
  qed
qed (auto)

lemma concat_map: "(\<forall>x \<in> set cs. f x = [hd (f x)]) \<Longrightarrow>
   concat (map f cs) = (map (hd \<circ> f) cs)"
  by (induction cs) (auto)

lemma max_var_Var: "max_var (Var x) = x"
proof -
  have "Var x \<noteq> 0"
    by (metis empty_iff insertI1 vars_Var vars_zero)
  then show ?thesis
    unfolding Abstract_Linear_Poly.max_var_def by (simp)
qed

lemma start_fresh_variable_append: "start_fresh_variable (xs @ ys) =
    max (start_fresh_variable xs) (start_fresh_variable ys)"
  by (induction xs) auto

lemma start_fresh_variable_Max:
  shows "start_fresh_variable xs =
    (if xs = [] then 0 else Max (set (map (Branch_and_Bound.max_var \<circ> poly \<circ> snd) xs)) + 1)"
  by (induction xs) (auto)

locale preprocess'L
begin

fun p_mapping where
  "p_mapping [] x = (Map.empty, x)" |
  "p_mapping ((i,nc)#ncs) x =  (let (m', x')  = p_mapping ncs x; p = poly nc
                         in
                         if (is_monom p) then (m', x')
                         else if p = 0 then (m', x')
                         else (case m' p of Some v \<Rightarrow> (m', x')
                          | None \<Rightarrow> (m' (p \<mapsto> x'), x' + 1)))"

lemma p_mapping: "S = preprocess' ncs x \<Longrightarrow> p_mapping ncs x = (m, x') \<Longrightarrow>
   (Poly_Mapping S = m \<and> FirstFreshVariable S = x')"
proof (induction ncs x arbitrary: m x' S rule: p_mapping.induct)
  case (2 i nc ncs x)
  define p where "p = poly nc"
  obtain m' x'' where mx': "p_mapping ncs x = (m',x'')"
    using prod_cases by fastforce
  have m': "m' = Poly_Mapping (preprocess' ncs x)"
    using 2 mx' by blast
  have x'': "x'' = FirstFreshVariable (preprocess' ncs x)"
    using 2 mx' by blast
  consider (a) "is_monom p \<or> p = 0 \<or> (\<exists>v. m' p = Some v)" | (b) "\<not> is_monom p \<and> p \<noteq> 0 \<and> m' p = None"
    by fastforce
  then show ?case
  proof (cases)
    case a
    show ?thesis
      using 2 m' p_def x''  mx' a by (auto simp add: Let_def)
  next
    case b
    show ?thesis
      using 2 m' p_def x''  mx' b by (fastforce simp add: Let_def)
  qed
qed (auto)



lemma preprocess'_mapping_Some:
  "S = preprocess' ncs x \<Longrightarrow> m = Poly_Mapping S \<Longrightarrow> (i, nc) \<in> set ncs \<Longrightarrow>
       \<not> is_monom (Simplex.poly nc) \<Longrightarrow> Simplex.poly nc \<noteq> 0 \<Longrightarrow>
       (\<exists>v. m (poly nc) = Some v)"
  by(induction ncs x arbitrary: m S rule: preprocess'.induct)
    (auto simp add: Let_def split: if_splits option.splits)

fun
  atoms where
  "atoms m [] = []"
| "atoms m ((i,nc) # ncs) = (let p = poly nc; as' = atoms m ncs in
                         if (is_monom p) then ((i, qdelta_constraint_to_atom nc 0) # as')
                         else if p = 0 then as'
                         else (case m p of Some v \<Rightarrow> ((i,qdelta_constraint_to_atom nc v) # as') |
                                           None \<Rightarrow> as'))"

lemma atoms:
  assumes S: "S = preprocess' ncs x" and m: "m = Poly_Mapping S"   and
    "\<And>nc i. (i, nc) \<in> set ncs \<Longrightarrow> m' (poly nc) = m (poly nc)"
  shows "Atoms S = atoms m' ncs"
  using assms 
proof (induction ncs x arbitrary: m' m S rule: preprocess'.induct)
  case (2 i nc ncs x)
  define p where "p = poly nc"
  define m'' where "m'' = Poly_Mapping (preprocess' ncs x)"
  define x'' where "x'' = FirstFreshVariable (preprocess' ncs x)"
  consider (a) "is_monom p" | (b) "\<not> is_monom p \<and> p = 0" | (c) "\<not> is_monom p \<and> p \<noteq> 0 \<and> m'' p = None"
    | (d) "\<not> is_monom p \<and> p \<noteq> 0 \<and> (\<exists>v. m'' p = Some v)"
    by fastforce
  then show ?case
  proof (cases)
    case a
    then show ?thesis
      using 2 p_def by (cases nc) (fastforce split: atom.split simp add: Let_def)+
  next
    case b
    then show ?thesis
      using 2 p_def by (fastforce simp add: Let_def)
  next
    case c
    then have mp: "Some x''= m p"
      using 2 p_def m''_def x''_def by (auto simp add: Let_def)
    also have "m p = m' p"
      unfolding p_def using 2 by fastforce
    finally have mp: "m' p = Some x''"
      by simp
    then have "Atoms S = (i, qdelta_constraint_to_atom nc x'') # Atoms (preprocess' ncs x)"
      using c 2 p_def m''_def x''_def by (auto simp add: Let_def map_update split: option.split if_splits)
    also have "Atoms (preprocess' ncs x) = atoms m' ncs"
    proof -
      (* TODO: clean me*)
      have "m'' (poly nc') = m (poly nc')" if "(i', nc') \<in> set ncs" for i' nc'
        using option.simps(3) preprocess'_mapping_Some 2 that m''_def c
        apply (auto split: option.splits if_splits prod.splits simp add: Let_def)
        by (metis option.distinct(1) preprocess'L.preprocess'_mapping_Some)
      also have "m (poly nc') = m' (poly nc')" if "(i', nc') \<in> set ncs" for i' nc'
        using 2 that by fastforce
      finally show ?thesis
        using m''_def 2 by (intro 2(1)[of _ m'']) (auto)
    qed
    also have "(i, qdelta_constraint_to_atom nc x'') # \<dots> = atoms m' ((i, nc) # ncs)"
      using c p_def mp by (auto simp add: Let_def map_update split: option.split if_splits)
    finally show ?thesis
      by simp
  next
    case d
    then obtain v where v_def: "m'' p = Some v"
      by blast
    have mp: "m'' p = m p"
      using 2 d p_def m''_def by (auto simp add: Let_def)
    also have "m p = m' p"
      unfolding p_def using 2 by fastforce
    finally have mp: "m' p = Some v"
      using v_def by simp
    then have "Atoms S = (i, qdelta_constraint_to_atom nc v) # Atoms (preprocess' ncs x)"
      using d 2 p_def m''_def v_def x''_def by (auto simp add: Let_def map_update split: option.split if_splits)
    also have "Atoms (preprocess' ncs x) = atoms m' ncs"
    proof -
      have "m'' (poly nc') = m (poly nc')" if "(i', nc') \<in> set ncs" for i' nc'
        using option.simps(3) preprocess'_mapping_Some 2 that m''_def d
        apply (auto split: option.splits if_splits prod.splits simp add: Let_def)
        by (metis option.distinct(1) preprocess'L.preprocess'_mapping_Some)
      also have "m (poly nc') = m' (poly nc')" if "(i', nc') \<in> set ncs" for i' nc'
        using 2 that by fastforce
      finally show ?thesis
        using m''_def 2 by (intro 2(1)[of _ m'']) (auto)
    qed
    also have "(i, qdelta_constraint_to_atom nc v) # \<dots> = atoms m' ((i, nc) # ncs)"
      using d p_def mp by (auto simp add: Let_def map_update split: option.split if_splits)
    finally show ?thesis
      by simp
  qed
qed auto

lemma atoms_append: "atoms m (ncs @ mcs) = atoms m ncs @ atoms m mcs"
  by (induction m ncs rule: atoms.induct) (auto simp add: Let_def split: option.splits)

lemma atoms_map:
  assumes "\<And>i nc. (i, nc) \<in> set ncs \<Longrightarrow> is_monom (Simplex.poly nc)"
  shows "atoms m ncs = map (\<lambda>(i, nc). (i, qdelta_constraint_to_atom nc 0)) ncs"
  using assms
  by (induction m ncs rule: atoms.induct) (fastforce simp add: Let_def split: option.split)+

lemma atoms_index:
  assumes "i \<in> set (map fst (atoms m ncs))"
  shows "i \<in> set (map fst ncs)"
  using assms
  by (induction m ncs rule: atoms.induct) (auto simp add: Let_def split: if_splits option.splits)

fun
  alt  where
  "alt [] s = s"
| "alt ((i,h) # t) s = (let s' = alt t s; p = poly h; is_monom_h = is_monom p;
                         v' = FirstFreshVariable s';
                         t' = Tableau s';
                         a' = Atoms s';
                         m' = Poly_Mapping s';
                         u' = UnsatIndices s' in
                         if is_monom_h then IState v' t'
                           ((i,qdelta_constraint_to_atom h v') # a') m' u'
                         else if p = 0 then
                           if zero_satisfies h then s' else
                              IState v' t' a' m' (i # u')
                         else (case m' p of Some v \<Rightarrow>
                            IState v' t' ((i,qdelta_constraint_to_atom h v) # a') m' u'
                          | None \<Rightarrow> IState (v' + 1) (linear_poly_to_eq p v' # t')
                           ((i,qdelta_constraint_to_atom h v') # a') (m' (p \<mapsto> v')) u'))"

lemma alt:
  assumes "s = IState x [] [] Map.empty []"
  shows "preprocess' ncs x = alt ncs s"
  using assms by  (induction ncs x rule: preprocess'.induct) auto

lemma alt_append:
  assumes "s\<^sub>1 = alt ncs' s\<^sub>0" "s\<^sub>2 = alt ncs s\<^sub>1"
  shows "s\<^sub>2 = alt (ncs @ ncs') s\<^sub>0"
  using assms by (induction ncs s\<^sub>0 arbitrary: s\<^sub>1 s\<^sub>2 rule: alt.induct) auto

lemma UnsatIndices:
  assumes "ncs\<^sub>f = filter (\<lambda>(i, nc). Simplex.poly nc = 0) ncs"
  shows "UnsatIndices (preprocess' ncs x) = UnsatIndices (preprocess' ncs\<^sub>f x)"
  using assms
  by (induction ncs x arbitrary: ncs\<^sub>f rule: preprocess'.induct) (auto simp add: Let_def split: option.split)

lemma Tableau':
  assumes "ncs\<^sub>f = filter (\<lambda>(i, nc). \<not> is_monom (poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs"
  shows "Tableau (preprocess' ncs x) = Tableau (preprocess' ncs\<^sub>f x) \<and> FirstFreshVariable (preprocess' ncs x) = FirstFreshVariable (preprocess' ncs\<^sub>f x)
   \<and> Poly_Mapping (preprocess' ncs x) = Poly_Mapping (preprocess' ncs\<^sub>f x)"
  using assms
  by (induction ncs x arbitrary: ncs\<^sub>f rule: preprocess'.induct) (auto simp add:  Let_def split: option.split)

lemma Atoms':
  assumes "ncs\<^sub>f = filter (\<lambda>(i, nc). Simplex.poly nc \<noteq> 0) ncs"
  shows "Atoms (preprocess' ncs x) = Atoms (preprocess' ncs\<^sub>f x) \<and> FirstFreshVariable (preprocess' ncs x) = FirstFreshVariable (preprocess' ncs\<^sub>f x)
   \<and> Poly_Mapping (preprocess' ncs x) = Poly_Mapping (preprocess' ncs\<^sub>f x)"
  using assms
  by (induction ncs x arbitrary: ncs\<^sub>f rule: preprocess'.induct) (auto simp add:  Let_def split: option.split)

lemma Tableau:
  assumes "ncs\<^sub>f = filter (\<lambda>(i, nc). \<not> is_monom (poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs"
  shows "Tableau (preprocess' ncs x) = Tableau (preprocess' ncs\<^sub>f x)"
  using assms Tableau' by (auto)

lemma Poly_Mapping:
  assumes "ncs\<^sub>f = filter (\<lambda>(i, nc). \<not> is_monom (poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs"
  shows "Poly_Mapping (preprocess' ncs x) = Poly_Mapping (preprocess' ncs\<^sub>f x)"
  using assms Tableau' by (auto)

end

global_interpretation preprocess': preprocess'L .

lemma enumerated_diff:
  "enumerated n xs \<Longrightarrow> i < length xs \<Longrightarrow> set xs - {xs ! i} = set xs - {n + i} \<times> UNIV"
  apply(induction xs arbitrary: i n)
  apply(auto simp del: enumerated.simps)
     apply (metis enumerated_nth list.set_intros(1))
    apply (metis enumerated_nth insert_iff list.simps(15))
   apply (metis enumerated_enumerate length_enumerate length_nth_simps(2) nth_enumerate_eq prod.inject)
  by (metis Pair_inject enumerated_enumerate length_Cons length_enumerate nth_enumerate_eq)

(* TODO: clean me up *)
lemma filter_list_update:
  "\<not> P x \<Longrightarrow> \<not> P (xs ! i) \<Longrightarrow> filter P xs = filter P (xs[i := x])"
  apply(induction xs) apply(auto split: nat.splits)
  by (smt filter.simps(2) filter_append list_update_beyond list_update_id not_le_imp_less upd_conv_take_nth_drop)

lemma is_monom_Var: "is_monom (Var x)"
  unfolding is_monom_def by (transfer) simp

lemma Var_uneq_0: "(Var x) \<noteq> 0"
  by (transfer) (metis class_field.zero_not_one fun_var_def fun_zero_def)

lemma monom_coeff_Var: "monom_coeff (Var x) = 1"
  unfolding monom_coeff_def monom_var_def using coeff_Var1  max_var_Var by auto

lemma monom_var_Var: "monom_var (Var x) = x"
  unfolding monom_coeff_def monom_var_def using coeff_Var1  max_var_Var by auto

lemma distinct_map_not_inj: "f x = f y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> \<not> distinct (map f xs)"
  by (induction xs) (auto simp add: rev_image_eqI)

lemma
  assumes "checked_bnc acs Is lb ub s"
    "x \<in> set Is"
    "new = (if t then (fst (lb x), Geq x (rat_of_int y)) else (fst (ub x), Leq x (rat_of_int y)))"
    "lb' = (if t then lb(x := (fst (lb x), y)) else lb)"
    "ub' = (if t then ub else ub(x := (fst (ub x), y)))"
  shows
    bnb_update_state_invariant: "bnb_update_state'' acs Is lb' ub' s new = Some s' \<Longrightarrow>
                                 state_invariant acs Is lb' ub' s'" and
    bnb_update_state_Unsat: "bnb_update_state'' acs Is lb' ub' s new = None \<Longrightarrow>
                             \<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb' ub' @ acs))"
proof -
  define cs\<^sub>u where "cs\<^sub>u = map (\<lambda> x. (fst (ub x), LEQ (Var x) (of_int (snd (ub x))))) Is"
  define cs\<^sub>l where "cs\<^sub>l = map (\<lambda> x. (fst (lb x), GEQ (Var x) (of_int (snd (lb x))))) Is"
  define cs where "cs = i_bounds_to_constraints Is lb ub @ acs"
  have cs_app: "cs = (cs\<^sub>l @ cs\<^sub>u) @ acs"
    unfolding cs_def cs\<^sub>u_def cs\<^sub>l_def by (auto simp add: i_bounds_to_constraints_def)
  define cs' where "cs' = i_bounds_to_constraints Is lb' ub' @ acs"
  define ls where "ls = map fst cs"
  define i where "i = (if t then fst (lb x) else fst (ub x))"
  define ls\<^sub>2 where "ls\<^sub>2 = remove1 (fst new) ls"
  define c where "c = (if t then GEQ (Var x) (rat_of_int y) else LEQ (Var x) (rat_of_int y))"
  have enumerated_cs: "enumerated 0 cs"
    by (metis assms(1) checked_bnc_def cs_def)
  have fst_ub': "fst (ub' y) = fst (ub y)" for y
    unfolding assms by auto
  have fst_lb': "fst (lb' y) = fst (lb y)" for y
    unfolding assms by auto
  have enumerated_cs': "enumerated 0 cs'"
    using enumerated_cs unfolding enumerated[symmetric]
    unfolding cs'_def cs_def i_bounds_to_constraints_def fst_ub' fst_lb' by (auto simp add: comp_def)
  have length_cs': "length cs' = length cs"
    unfolding cs_def cs'_def i_bounds_to_constraints_def by auto
  have ls_cs': "ls = map fst cs'"
    using enumerated_cs enumerated_cs' length_cs' unfolding enumerated[symmetric] ls_def by simp
  have distinct_ls: "distinct ls"
    by (metis assms(1) checked_bnc_def cs_def enumerated_distinct ls_def)
  have ub_lb1: "fst (ub x) \<noteq> fst (ub y)" if "x \<noteq> y" "x \<in> set Is" "y \<in> set Is" for x y
    using that cs_def distinct_ls unfolding ls_def i_bounds_to_constraints_def
    by (auto simp add: distinct_map_not_inj)
  have ub_lb2: "fst (lb x) \<noteq> fst (lb y)" if "x \<noteq> y" "x \<in> set Is" "y \<in> set Is" for x y
    using that cs_def distinct_ls unfolding ls_def i_bounds_to_constraints_def
    by (auto simp add: distinct_map_not_inj)
  have ub_lb': "fst (ub x) \<noteq> fst (lb y)" if "x \<in> set Is" "y \<in> set Is" for x y
    using that cs_def distinct_ls unfolding ls_def i_bounds_to_constraints_def  by (auto)
  have i_acs: "i \<notin> fst ` set acs"
    using  cs_def distinct_ls unfolding ls_def i_bounds_to_constraints_def i_def
    using assms disjoint_iff_not_equal image_eqI by auto
  have i_ls: "i \<in> set ls"
    using  cs_def  unfolding ls_def i_bounds_to_constraints_def i_def
    using assms by auto
  have i_length_cs: "i < length cs"
    using i_ls enumerated_cs unfolding ls_def enumerated[symmetric] by simp
  have set_cs': "set cs' = set (cs[i := (i, c)])"
  proof -
    have 1: "set cs - {cs ! i} = set cs - {i} \<times> UNIV"
      using i_length_cs enumerated_cs by (subst enumerated_diff[of 0]) auto
    show ?thesis
      unfolding c_def
      apply(subst set_update_distinct)
        defer defer
        apply(subst 1) apply(simp add: assms(5) cs'_def cs_def)
        apply(auto simp add: i_def i_bounds_to_constraints_def assms)
                apply (metis assms(2) ub_lb2)
               apply (simp add: assms(2) ub_lb2)
      using assms(2) ub_lb'  apply fastforce
      using i_acs i_def image_iff apply fastforce
      using assms(2) ub_lb' apply blast
                apply (metis assms(2) ub_lb1)
               apply (simp add: assms(2) ub_lb1)
      using i_acs i_def image_iff apply fastforce
      using distinct_map enumerated_cs apply blast
      using i_def i_length_cs by auto[2]
  qed
  have cs': "cs' = cs[i := (i, c)]"
    using enumerated_cs'  enumerated_cs set_cs' length_cs'
    by (intro enumerated_set_unique[of 0]) (auto intro: enumerated_update)
  have enumerated_cs\<^sub>l\<^sub>u: "enumerated 0 (cs\<^sub>l @ cs\<^sub>u)"
    using enumerated_cs enumerated_append unfolding cs_def cs\<^sub>u_def cs\<^sub>l_def i_bounds_to_constraints_def
    by blast
  have i_length_Is: "i < length Is + length Is"
  proof -
    have "i \<in> set (map fst (i_bounds_to_constraints Is lb ub))"
      unfolding i_def i_bounds_to_constraints_def using assms by simp
    moreover have "enumerated 0 (i_bounds_to_constraints Is lb ub)"
      using enumerated_cs enumerated_append unfolding cs_def by auto
    ultimately have "i < length (map fst (i_bounds_to_constraints Is lb ub))"
      unfolding enumerated[symmetric] by auto
    then show ?thesis
      unfolding i_bounds_to_constraints_def by simp
  qed
  have cs'': "cs' = (cs\<^sub>l @ cs\<^sub>u)[i := (i, c)] @ acs"
    unfolding cs' cs_app cs\<^sub>l_def cs\<^sub>u_def using i_length_Is by (subst list_update_append1) auto
  have "to_ns cs' = to_ns ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @ to_ns acs"
    unfolding cs'' to_ns_def by (simp)
  also have "\<dots> = map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @ to_ns acs"
  proof -
    have "to_ns ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) =
      map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)])"
    proof -
      have "\<forall>d \<in> insert (i,c) (set (cs\<^sub>l @ cs\<^sub>u)).
            i_constraint_to_qdelta_constraint d = [hd (i_constraint_to_qdelta_constraint d)]"
        unfolding cs\<^sub>l_def cs\<^sub>u_def c_def by (auto)
      then show ?thesis
        using set_update_subset_insert unfolding to_ns_def by (subst concat_map) fast+
    qed
    then show ?thesis
      using assms by (auto simp add: map_update c_def atom_to_qdnsconstr_def)
  qed
  finally have to_ns_cs':
    "to_ns cs' = map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @ to_ns acs"
    by simp
  also have "(map (map_prod id normalize_ns_constraint) \<dots>) =
     (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)])) @
     map (map_prod id normalize_ns_constraint) (to_ns acs)"
  proof -
    have "(a, b) \<in> insert (i,c) (set (cs\<^sub>l @ cs\<^sub>u)) \<Longrightarrow>
           map_prod id normalize_ns_constraint (hd (map (Pair a) (constraint_to_qdelta_constraint b))) =
           hd (map (Pair a) (constraint_to_qdelta_constraint b))" for a b
      unfolding cs\<^sub>l_def cs\<^sub>u_def c_def by (auto simp add: max_var_Var coeff_Var1 normalize_ns_constraint.simps)
    then show ?thesis
      using set_update_subset_insert by (fastforce)
  qed
  finally have mmn_to_ns_cs':
    "map (map_prod id normalize_ns_constraint) (to_ns cs') =
     map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @
     map (map_prod id normalize_ns_constraint) (to_ns acs)"
    by blast
  have to_ns_cs: "to_ns cs = map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)) @ to_ns acs"
    unfolding to_ns_def cs_app unfolding cs\<^sub>l_def cs\<^sub>u_def by (auto simp add: concat_map)
  have ls\<^sub>2: "ls\<^sub>2 = remove1 i ls"
    unfolding ls\<^sub>2_def i_def using assms by auto
  note inv_simps =
    Incremental_Simplex.invariant_cs.simps  invariant_simplex.simps
    Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.invariant_nsc.simps
    Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.invariant_as_asi.simps
  have "\<exists>y \<in> set (to_ns cs).  fst y = i \<and> Simplex.poly (snd y) = Var x"
    unfolding cs_app cs\<^sub>l_def cs\<^sub>u_def apply(auto simp add: to_ns_def i_constraint_to_qdelta_constraint_def)
    apply(rule bexI[of _ "(i, (if t then GEQ_ns (Var x) (QDelta (rat_of_int (snd (lb x))) 0) else
         LEQ_ns (Var x) (QDelta (rat_of_int (snd (ub x))) 0)))"])
    using assms by (auto simp add: i_def)
  then have "suitable_upd_atom new cs"
    unfolding find_index_less_size_conv[symmetric]
    unfolding suitable_upd_atom_def by (auto simp add: assms i_def)
  then obtain s\<^sub>2 where s\<^sub>2:
    "assert_all_simplex ls\<^sub>2 (del_atom_from_state'' s new) = Inr s\<^sub>2"
    "invariant_simplex cs (set ls\<^sub>2) s\<^sub>2"
    using bnb_update1[OF assms(1) cs_def _ ls_def] unfolding ls\<^sub>2_def by blast
  obtain ncs\<^sub>2 as\<^sub>2 tv\<^sub>2 ui\<^sub>2 l3s\<^sub>2 where s\<^sub>2_def: "s\<^sub>2 = Simplex_State (ncs\<^sub>2, (as\<^sub>2, tv\<^sub>2, ui\<^sub>2), l3s\<^sub>2)"
    using solution_simplex.cases by blast
  obtain t\<^sub>3\<^sub>1 as\<^sub>3\<^sub>1 tv\<^sub>3\<^sub>1 ui\<^sub>3\<^sub>1 where preprocess: "preprocess (to_ns cs') = (t\<^sub>3\<^sub>1, as\<^sub>3\<^sub>1, tv\<^sub>3\<^sub>1, ui\<^sub>3\<^sub>1)"
    using prod_cases4 by blast
  obtain t\<^sub>2\<^sub>1 as\<^sub>2\<^sub>1 tv\<^sub>2\<^sub>1 ui\<^sub>2\<^sub>1 where preprocess_cs: "preprocess (to_ns cs) = (t\<^sub>2\<^sub>1, as\<^sub>2\<^sub>1, tv\<^sub>2\<^sub>1, ui\<^sub>2\<^sub>1)"
    using prod_cases4 by blast
  define s\<^sub>3 where "s\<^sub>3 = update_iatom_in_state' s\<^sub>2 new"
  obtain ncs\<^sub>3 as\<^sub>3 tv\<^sub>3 ui\<^sub>3 l3s\<^sub>3 where s\<^sub>3: "s\<^sub>3 = Simplex_State (ncs\<^sub>3, (as\<^sub>3, tv\<^sub>3, ui\<^sub>3), l3s\<^sub>3)"
    using solution_simplex.cases by blast
  define qda where "qda = atom_to_qdatom (snd new)"
  have as\<^sub>3: "as\<^sub>3 =  Mapping.update i [(i, qda)] as\<^sub>2"
    using s\<^sub>3 unfolding s\<^sub>2_def s\<^sub>3_def update_iatom_in_state'_def assms i_def qda_def by (auto)
  have cs'_to_ns: "to_ns cs' = (to_ns cs)[i := (i, atom_to_qdnsconstr (snd new))]"
    using assms i_length_Is  unfolding to_ns_cs to_ns_cs' by (subst (2) list_update_append1)
      (auto simp add: list_update_append1 map_update c_def atom_to_qdnsconstr_def cs\<^sub>l_def cs\<^sub>u_def)
  define ncs where "ncs = (map (map_prod id normalize_ns_constraint) (to_ns cs))"
  have ncs: "ncs = (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u))) @
     map (map_prod id normalize_ns_constraint) (to_ns acs)"
    unfolding ncs_def to_ns_cs using max_var_Var
    by (auto simp add: cs\<^sub>u_def cs\<^sub>l_def normalize_ns_constraint.simps)
  define ncs' where "ncs' =  ncs[i := (i, (if t then GEQ_ns (Var x) (QDelta (rat_of_int y) 0)
                                                else LEQ_ns (Var x) (QDelta (rat_of_int y) 0)))]"
  define sv where "sv = start_fresh_variable ncs"
  define sv' where "sv' = start_fresh_variable ncs'"
  have ncs': "(map (map_prod id normalize_ns_constraint) (to_ns cs')) = ncs'"
    unfolding ncs'_def i_def ncs_def cs'_to_ns by (subst map_update)
      (auto simp add: assms atom_to_qdnsconstr_def normalize_ns_constraint.simps max_var_Var)
  then have ncs'': "ncs' = map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @
                    map (map_prod id normalize_ns_constraint) (to_ns acs)"
    unfolding mmn_to_ns_cs' by auto
  have cs\<^sub>l\<^sub>u_x: "(cs\<^sub>l @ cs\<^sub>u) ! i = (i, (if t then GEQ (Var x) (of_int (snd (lb x))) else LEQ (Var x) (of_int (snd (ub x)))))"
    apply(subst enumerated_nth[of 0])
      apply (simp add: enumerated_cs\<^sub>l\<^sub>u)
     defer apply(simp)
    unfolding i_def cs\<^sub>l_def cs\<^sub>u_def using assms by auto
  have i_length_cs\<^sub>l\<^sub>u: "i < length (cs\<^sub>l @ cs\<^sub>u)"
    unfolding cs\<^sub>l_def cs\<^sub>u_def using i_length_Is by auto
  have sv_sv': "sv = sv'"
  proof -
    have 1: "(map (Branch_and_Bound.max_var \<circ> Simplex.poly \<circ> snd \<circ> hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u)) ! i = x"
      apply(subst nth_map)
      subgoal using i_length_cs\<^sub>l\<^sub>u by auto
      using max_var_Var by (subst cs\<^sub>l\<^sub>u_x) (auto simp add: cs\<^sub>l_def cs\<^sub>u_def cs\<^sub>l\<^sub>u_x)
    then have "(map (Branch_and_Bound.max_var \<circ> Simplex.poly \<circ> snd \<circ> hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))
    = (map (Branch_and_Bound.max_var \<circ> Simplex.poly \<circ> snd \<circ> hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]))"
      apply(subst map_update)
      apply(subst upd_conv_take_nth_drop) subgoal using i_length_cs\<^sub>l\<^sub>u by auto
      apply(subst id_take_nth_drop[of i ])
      subgoal using i_length_cs\<^sub>l\<^sub>u by auto
      using max_var_Var by (auto simp add: c_def cs\<^sub>l_def cs\<^sub>u_def)
    then have "start_fresh_variable (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))
    = start_fresh_variable (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]))"
      by (auto simp add: start_fresh_variable_Max comp_def)
    then show ?thesis
      unfolding sv_def sv'_def ncs'' ncs by (simp add: start_fresh_variable_append)
  qed
  define s\<^sub>3\<^sub>1\<^sub>1 where "s\<^sub>3\<^sub>1\<^sub>1 = preprocess' ncs' sv'"
  define s\<^sub>2\<^sub>1\<^sub>1 where "s\<^sub>2\<^sub>1\<^sub>1 = preprocess' ncs sv"
  define oa where "oa = snd (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u) ! i)"
  have i_oa: "(map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u) ! i) = (i, oa)"
  proof -
    have 1: "map fst (cs\<^sub>l @ cs\<^sub>u) = map (\<lambda>x. fst (hd (i_constraint_to_qdelta_constraint x))) (cs\<^sub>l @ cs\<^sub>u)"
      by (auto simp add: cs\<^sub>l_def cs\<^sub>u_def)
    have "enumerated 0 (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))"
      using enumerated_cs\<^sub>l\<^sub>u unfolding enumerated[symmetric] 1 by (auto simp add: comp_def)
    then show ?thesis
      using i_length_Is unfolding oa_def by (subst enumerated_nth') (auto simp add: cs\<^sub>l_def cs\<^sub>u_def)
  qed
  then have ncs_i_oa: "ncs ! i = (i, oa)"
    using i_length_Is  unfolding ncs by (subst nth_append) (auto simp add: cs\<^sub>u_def cs\<^sub>l_def)
  have oa: "is_monom (poly oa)" "poly oa \<noteq> 0"
  proof -
    have "(i, oa) \<in> set (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))"
      using i_length_Is unfolding i_oa[symmetric] by (intro nth_mem) (auto simp add: cs\<^sub>l_def cs\<^sub>u_def)
    moreover have "is_monom (poly p)" if "(j,p) \<in> set (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))" for j p
      using that is_monom_Var unfolding cs\<^sub>l_def cs\<^sub>u_def by auto
    moreover have "poly p \<noteq> 0" if "(j,p) \<in> set (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))" for j p
      using that Var_uneq_0  unfolding cs\<^sub>l_def cs\<^sub>u_def by (auto)
    ultimately show "is_monom (poly oa)" "poly oa \<noteq> 0"
      by blast+
  qed
  have u_s\<^sub>3\<^sub>1\<^sub>1: "UnsatIndices s\<^sub>3\<^sub>1\<^sub>1 = UnsatIndices s\<^sub>2\<^sub>1\<^sub>1"
  proof -
    have "UnsatIndices s\<^sub>2\<^sub>1\<^sub>1 = UnsatIndices (preprocess' (filter (\<lambda>(i, nc). Simplex.poly nc = 0) ncs) sv)"
      unfolding s\<^sub>2\<^sub>1\<^sub>1_def apply(subst preprocess'.UnsatIndices) by auto
    also have "(filter (\<lambda>(i, nc). Simplex.poly nc = 0) ncs) = (filter (\<lambda>(i, nc). Simplex.poly nc = 0) ncs')"
      using is_monom_Var oa Var_uneq_0  unfolding ncs'_def
      by (intro filter_list_update) (auto simp add: ncs_i_oa)
    also have "sv = sv'"
      using sv_sv' by simp
    also have "UnsatIndices (preprocess' (filter (\<lambda>(i, nc). Simplex.poly nc = 0) ncs') sv')
    = UnsatIndices s\<^sub>3\<^sub>1\<^sub>1"
      unfolding s\<^sub>3\<^sub>1\<^sub>1_def apply(subst preprocess'.UnsatIndices[symmetric]) by auto
    finally show ?thesis
      by simp
  qed  have t_s\<^sub>3\<^sub>1\<^sub>1: "Tableau s\<^sub>3\<^sub>1\<^sub>1 = Tableau s\<^sub>2\<^sub>1\<^sub>1"
  proof -
    have "Tableau s\<^sub>2\<^sub>1\<^sub>1 = Tableau (preprocess' (filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs) sv)"
      unfolding s\<^sub>2\<^sub>1\<^sub>1_def apply(subst preprocess'.Tableau) by auto
    also have "filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs
      = filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs'"
      using is_monom_Var oa Var_uneq_0  unfolding ncs'_def
      by (intro filter_list_update) (auto simp add: ncs_i_oa)
    also have "sv = sv'"
      using sv_sv' by simp
    also have "Tableau (preprocess' (filter (\<lambda>a. case a of (i, nc) \<Rightarrow> \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs') sv')
    = Tableau s\<^sub>3\<^sub>1\<^sub>1"
      unfolding s\<^sub>3\<^sub>1\<^sub>1_def apply(subst preprocess'.Tableau[symmetric]) by auto
    finally show ?thesis
      by simp
  qed
  obtain t\<^sub>3\<^sub>1\<^sub>1 and tv\<^sub>3\<^sub>1\<^sub>1 :: "(nat, QDelta) mapping \<Rightarrow> (nat, QDelta) mapping"
    where "preprocess_part_2 (Atoms s\<^sub>3\<^sub>1\<^sub>1) (Tableau s\<^sub>3\<^sub>1\<^sub>1) = (t\<^sub>3\<^sub>1\<^sub>1, tv\<^sub>3\<^sub>1\<^sub>1)"
    using prod_cases by fastforce
  define m where "m = Poly_Mapping (preprocess' ncs sv)"
  define f where
    "f = (\<lambda>(i::nat, nc). (i, qdelta_constraint_to_atom nc 0)) \<circ> (hd \<circ> i_constraint_to_qdelta_constraint)"
  have enumerated_f_cs\<^sub>l\<^sub>u: "enumerated 0 (map f cs\<^sub>l @ map f cs\<^sub>u)"
  proof -
    have m: "map fst (cs\<^sub>l @ cs\<^sub>u) = map (fst \<circ> f) (cs\<^sub>l @ cs\<^sub>u)"
      by (rule map_cong) (auto simp add: f_def cs\<^sub>l_def cs\<^sub>u_def)
    then show ?thesis
      using enumerated_cs\<^sub>l\<^sub>u unfolding m enumerated[symmetric] by auto
  qed
  define tail where
    "tail = preprocess'.atoms m (map (map_prod id normalize_ns_constraint) (to_ns acs))"
  have m: "m = Poly_Mapping (preprocess' ncs' sv')"
  proof -
    have "m = Poly_Mapping (preprocess' (filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs) sv)"
      unfolding m_def apply(subst preprocess'.Poly_Mapping) by auto
    also have "filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs
      = filter (\<lambda>(i, nc). \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs'"
      using is_monom_Var oa Var_uneq_0  unfolding ncs'_def
      by (intro filter_list_update) (auto simp add: ncs_i_oa)
    also have "sv = sv'"
      using sv_sv' by simp
    also have "Poly_Mapping (preprocess' (filter (\<lambda>a. case a of (i, nc) \<Rightarrow> \<not> is_monom (Simplex.poly nc) \<and> Simplex.poly nc \<noteq> 0) ncs') sv')
    = Poly_Mapping (preprocess' ncs' sv')"
      unfolding s\<^sub>3\<^sub>1\<^sub>1_def apply(subst preprocess'.Poly_Mapping[symmetric]) by auto
    finally show ?thesis
      by simp
  qed
  have "Atoms s\<^sub>2\<^sub>1\<^sub>1 = preprocess'.atoms m ncs"
    using m_def unfolding s\<^sub>2\<^sub>1\<^sub>1_def by (subst preprocess'.atoms) (auto)
  also note ncs
  also have "preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u) @
     map (map_prod id normalize_ns_constraint) (to_ns acs)) =
     preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u)) @ tail"
    unfolding tail_def by (subst preprocess'.atoms_append) auto
  also have "preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) (cs\<^sub>l @ cs\<^sub>u))
     = map f (cs\<^sub>l @ cs\<^sub>u)"
    unfolding f_def using is_monom_Var
    by (subst preprocess'.atoms_map) (auto simp add: comp_def cs\<^sub>u_def cs\<^sub>l_def)
  finally have Atoms_s\<^sub>2\<^sub>1\<^sub>1: "Atoms s\<^sub>2\<^sub>1\<^sub>1 = map f (cs\<^sub>l @ cs\<^sub>u) @ tail"
    unfolding tail_def f_def by blast
  have "Atoms s\<^sub>3\<^sub>1\<^sub>1 = preprocess'.atoms m ncs'"
    using m unfolding s\<^sub>3\<^sub>1\<^sub>1_def by (subst preprocess'.atoms) (auto)
  also note ncs''
  also have "preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)])
       @ map (map_prod id normalize_ns_constraint) (to_ns acs))
     = preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]))
       @ tail"
    unfolding tail_def using preprocess'.atoms_append by auto
  also have "preprocess'.atoms m (map (hd \<circ> i_constraint_to_qdelta_constraint) ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]))
     =  map f ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)])"
    apply(subst preprocess'.atoms_map)
    using set_update_subset_insert[of "(cs\<^sub>l @ cs\<^sub>u)" i "(i,c)"] is_monom_Var
    by (auto split: if_splits simp add: f_def comp_def cs\<^sub>l_def cs\<^sub>u_def c_def)
  finally have Atoms_s\<^sub>3\<^sub>1\<^sub>1: "Atoms s\<^sub>3\<^sub>1\<^sub>1 = map f ((cs\<^sub>l @ cs\<^sub>u)[i := (i, c)]) @ tail"
    unfolding f_def by (simp add: map_update comp_def id_def)
  also have 1: "set \<dots> = insert (f (i, c)) (set (map f cs\<^sub>l @ map f cs\<^sub>u) - {i} \<times> UNIV \<union> set tail)"
    unfolding map_update apply(simp)
    apply(subst set_update_distinct)
    subgoal using enumerated_f_cs\<^sub>l\<^sub>u by (simp add: enumerated_enumerate)
    subgoal unfolding cs\<^sub>l_def cs\<^sub>u_def using i_length_Is by simp
    apply(subst enumerated_diff[of 0])
    subgoal using enumerated_f_cs\<^sub>l\<^sub>u by simp
    subgoal unfolding cs\<^sub>l_def cs\<^sub>u_def using i_length_Is by simp
    apply(subst Un_insert_left)
    unfolding c_def by (simp)
  also have "set (map f cs\<^sub>l @ map f cs\<^sub>u) - {i} \<times> UNIV \<union> set tail =
        (set (map f cs\<^sub>l @ map f cs\<^sub>u) \<union> set tail) - {i} \<times> UNIV"
  proof -
    have "False" if "(i, b) \<in> set tail" for b
    proof -
      have "i \<in> set (map fst (map (map_prod id normalize_ns_constraint) (to_ns acs)))"
        using that unfolding tail_def
        by (intro preprocess'.atoms_index[of _ m]) (auto simp add: rev_image_eqI)
      then have "i \<in> set (map fst acs)"
        apply(auto simp add: to_ns_def)
        subgoal for ba x
          apply(cases ba)
          by (auto simp add: rev_image_eqI)
        done
      then show False
        using i_acs by simp
    qed
    then have t: "set tail = set tail - {i} \<times> UNIV"
      by (auto)
    show ?thesis
      by (subst t) blast
  qed
  also have "\<dots> = set (Atoms s\<^sub>2\<^sub>1\<^sub>1) - {i} \<times> UNIV"
    unfolding Atoms_s\<^sub>2\<^sub>1\<^sub>1 by auto
  also have "(f (i, c)) = (i, qda)"
    unfolding f_def c_def qda_def using assms is_monom_Var monom_coeff_Var  max_var_Var
    by (auto simp add: monom_var_def atom_to_qdatom_def)
  finally have s\<^sub>3\<^sub>1\<^sub>1_Atoms: "set (Atoms s\<^sub>3\<^sub>1\<^sub>1) = insert ((i, qda)) (set (Atoms s\<^sub>2\<^sub>1\<^sub>1) - ({i} \<times> UNIV))"
    by blast
  have pp2: "preprocess_part_2 (Atoms s\<^sub>3\<^sub>1\<^sub>1) (Tableau s\<^sub>3\<^sub>1\<^sub>1) = preprocess_part_2 (Atoms s\<^sub>2\<^sub>1\<^sub>1) (Tableau s\<^sub>2\<^sub>1\<^sub>1)"
  proof -
    have "atom_var y = x" if "(i, y) \<in> set (Atoms s\<^sub>2\<^sub>1\<^sub>1)" for y
    proof -
      have tail: False if "(i, y) \<in> set tail"
      proof -
        have "i \<in> set (map fst (preprocess'.atoms m (map (map_prod id normalize_ns_constraint) (to_ns acs))))"
          using that unfolding tail_def by force
        then have "i \<in> set (map fst (map (map_prod id normalize_ns_constraint) (to_ns acs)))"
          by (rule preprocess'.atoms_index)
        then have "i \<in> set (map fst acs)"
          unfolding to_ns_def apply(auto) subgoal for ba x'
            by (cases ba) (force)+
          done
        then show False
          using i_acs by auto
      qed
      moreover have "atom_var y = x" if "(i, y) \<in> set (map f (cs\<^sub>l @ cs\<^sub>u))"
      proof -
        have "enumerated 0 (map f (cs\<^sub>l @ cs\<^sub>u))"
          using enumerated_cs\<^sub>l\<^sub>u unfolding enumerated[symmetric] f_def
          by (auto simp add: cs\<^sub>l_def cs\<^sub>u_def comp_def i_constraint_to_qdelta_constraint_def split: prod.splits)
        then have "(i, y) = (map f (cs\<^sub>l @ cs\<^sub>u)) ! i"
          apply(subst enumerated_nth[of 0])
          using that unfolding Atoms_s\<^sub>2\<^sub>1\<^sub>1 using tail by auto
        also have "\<dots> = f ((cs\<^sub>l @ cs\<^sub>u) ! i)"
          using i_length_cs\<^sub>l\<^sub>u by (subst nth_map) auto
        also have "atom_var (snd \<dots>) = x"
          unfolding cs\<^sub>l\<^sub>u_x f_def using monom_coeff_Var is_monom_Var monom_var_Var by(auto)
        finally show ?thesis
          by auto
      qed
      ultimately show ?thesis
        using that unfolding Atoms_s\<^sub>2\<^sub>1\<^sub>1 by (auto)
    qed
    moreover have "x \<in> atom_var ` snd ` set (Atoms s\<^sub>2\<^sub>1\<^sub>1)"
      unfolding Atoms_s\<^sub>2\<^sub>1\<^sub>1 f_def using is_monom_Var monom_coeff_Var monom_var_Var apply(auto simp add: cs\<^sub>l_def)
      using assms(2)
      by (smt UnCI atom_var.simps(2) image_iff snd_conv)
    ultimately have "atom_var ` snd ` set (Atoms s\<^sub>3\<^sub>1\<^sub>1) = atom_var ` snd ` set (Atoms s\<^sub>2\<^sub>1\<^sub>1)"
      unfolding s\<^sub>3\<^sub>1\<^sub>1_Atoms qda_def
        (* TODO: clean me *)
      by (auto simp add: atom_to_qdatom_def assms) (metis DiffI SigmaE2 image_eqI singletonD snd_conv)
    then show ?thesis
      unfolding preprocess_part_2_def t_s\<^sub>3\<^sub>1\<^sub>1 by simp
  qed
  have as\<^sub>3\<^sub>1: "as\<^sub>3\<^sub>1 = Atoms s\<^sub>3\<^sub>1\<^sub>1"
    using preprocess s\<^sub>2(2) unfolding s\<^sub>2_def inv_simps ncs'
      preprocess_def unfolding ncs_def[symmetric] preprocess_part_1_def
      sv_def[symmetric] sv'_def[symmetric]
      Let_def s\<^sub>2\<^sub>1\<^sub>1_def[symmetric] s\<^sub>3\<^sub>1\<^sub>1_def[symmetric] apply(auto)
    unfolding pp2[symmetric] by (auto split: prod.splits)
  have "ncs\<^sub>3 = map snd (to_ns cs')"
  proof -
    note cs'_to_ns
    also have "map snd ((to_ns cs)[i := (i, atom_to_qdnsconstr (snd new))]) =
     (map snd (to_ns cs))[fst new := atom_to_qdnsconstr (snd new)]"
      apply(subst map_update) by (auto simp add: i_def assms)
    also have "map snd (to_ns cs) = ncs\<^sub>2"
      using s\<^sub>2 unfolding s\<^sub>2_def invariant_simplex.simps inv_simps by simp
    also have "ncs\<^sub>2[fst new := atom_to_qdnsconstr (snd new)] = ncs\<^sub>3"
      using s\<^sub>3_def unfolding s\<^sub>3 update_iatom_in_state'_def s\<^sub>2_def by simp
    finally show ?thesis
      by simp
  qed
  moreover have "tv\<^sub>3 = tv\<^sub>3\<^sub>1"
  proof -
    have "tv\<^sub>3 = tv\<^sub>2"
      using s\<^sub>3 unfolding s\<^sub>3_def s\<^sub>2_def by (auto simp add: update_iatom_in_state'_def)
    also have "tv\<^sub>2 = tv\<^sub>2\<^sub>1"
      using s\<^sub>2 unfolding s\<^sub>2_def inv_simps preprocess_cs by (auto)
    also have "\<dots> = tv\<^sub>3\<^sub>1"
      using preprocess_cs unfolding preprocess_def preprocess_part_1_def
      unfolding ncs_def[symmetric] sv_def[symmetric]
      using preprocess unfolding preprocess_def  preprocess_part_1_def unfolding ncs' sv'_def[symmetric]
      apply(simp) unfolding s\<^sub>2\<^sub>1\<^sub>1_def[symmetric] s\<^sub>3\<^sub>1\<^sub>1_def[symmetric]
      apply(simp) unfolding pp2[symmetric] \<open>preprocess_part_2 (Atoms s\<^sub>3\<^sub>1\<^sub>1) (Tableau s\<^sub>3\<^sub>1\<^sub>1) = (t\<^sub>3\<^sub>1\<^sub>1, tv\<^sub>3\<^sub>1\<^sub>1)\<close>
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have "set ui\<^sub>3 = set ui\<^sub>3\<^sub>1"
  proof -
    have "ui\<^sub>3 = ui\<^sub>2"
      using s\<^sub>3_def unfolding s\<^sub>3 update_iatom_in_state'_def s\<^sub>2_def by (auto)
    also have "set ui\<^sub>2 = set ui\<^sub>2\<^sub>1"
      using s\<^sub>2(2) unfolding s\<^sub>2_def unfolding inv_simps preprocess_cs by (simp)
    also have "ui\<^sub>2\<^sub>1 = UnsatIndices s\<^sub>2\<^sub>1\<^sub>1"
      using preprocess_cs unfolding preprocess_def ncs_def[symmetric] preprocess_part_1_def
        sv_def[symmetric] Let_def s\<^sub>2\<^sub>1\<^sub>1_def[symmetric] by (auto split: prod.splits)
    also have "\<dots> = UnsatIndices s\<^sub>3\<^sub>1\<^sub>1"
      by (simp add: u_s\<^sub>3\<^sub>1\<^sub>1)
    also have "\<dots> = ui\<^sub>3\<^sub>1"
      using preprocess unfolding preprocess_def ncs' preprocess_part_1_def Let_def sv'_def[symmetric]
        s\<^sub>3\<^sub>1\<^sub>1_def[symmetric]  by (auto split: prod.splits)
    finally show ?thesis
      by simp
  qed
  moreover have "(\<forall>i. set (list_map_to_fun as\<^sub>3 i) = set as\<^sub>3\<^sub>1 \<inter> {i} \<times> UNIV)"
  proof -
    have "(\<forall>i. set (list_map_to_fun as\<^sub>2 i) = set (Atoms s\<^sub>2\<^sub>1\<^sub>1) \<inter> {i} \<times> UNIV)"
      using s\<^sub>2(2) unfolding s\<^sub>2_def inv_simps ncs'
        preprocess_def unfolding ncs_def[symmetric] preprocess_part_1_def
        sv_def[symmetric] sv'_def[symmetric]
        Let_def s\<^sub>2\<^sub>1\<^sub>1_def[symmetric] s\<^sub>3\<^sub>1\<^sub>1_def[symmetric] by (auto split: prod.splits)
    then show ?thesis
      unfolding as\<^sub>3 as\<^sub>3\<^sub>1 s\<^sub>3\<^sub>1\<^sub>1_Atoms by (auto simp add: list_map_to_fun_def)
  qed
  moreover have "invariant_s t\<^sub>3\<^sub>1 (set as\<^sub>3\<^sub>1 \<inter> set ls\<^sub>2 \<times> UNIV) l3s\<^sub>3"
  proof -
    have "invariant_s t\<^sub>3\<^sub>1 (set (Atoms s\<^sub>2\<^sub>1\<^sub>1) \<inter> set ls\<^sub>2 \<times> UNIV) l3s\<^sub>2"
      using preprocess s\<^sub>2(2) unfolding s\<^sub>2_def inv_simps ncs'
        preprocess_def unfolding ncs_def[symmetric] preprocess_part_1_def
        sv_def[symmetric] sv'_def[symmetric]
        Let_def s\<^sub>2\<^sub>1\<^sub>1_def[symmetric] s\<^sub>3\<^sub>1\<^sub>1_def[symmetric] apply(auto)
      unfolding pp2[symmetric] by (auto split: prod.splits)
    also have "set (Atoms s\<^sub>2\<^sub>1\<^sub>1) \<inter> set ls\<^sub>2 \<times> UNIV = set (Atoms s\<^sub>3\<^sub>1\<^sub>1) \<inter> set ls\<^sub>2 \<times> UNIV"
      unfolding s\<^sub>3\<^sub>1\<^sub>1_Atoms using distinct_ls by (auto simp add: ls\<^sub>2)
    also have "Atoms s\<^sub>3\<^sub>1\<^sub>1 = as\<^sub>3\<^sub>1"
      using as\<^sub>3\<^sub>1 by simp
    also have "l3s\<^sub>2 = l3s\<^sub>3"
      using s\<^sub>3_def unfolding s\<^sub>2_def s\<^sub>3 update_iatom_in_state'_def by simp
    finally show ?thesis
      by simp
  qed
  moreover have "set ls\<^sub>2 \<inter> set ui\<^sub>3 = {}"
  proof -
    have "set ui\<^sub>3 = set ui\<^sub>2"
      using s\<^sub>3_def unfolding s\<^sub>3 s\<^sub>2_def update_iatom_in_state'_def by (auto)
    also have "set ls\<^sub>2 \<inter> set ui\<^sub>2 = {}"
      using s\<^sub>2 unfolding s\<^sub>2_def inv_simps by auto
    finally show ?thesis
      by simp
  qed
  ultimately have inv: "invariant_simplex cs' (set ls\<^sub>2) s\<^sub>3"
    unfolding s\<^sub>3  unfolding update_iatom_in_state'_def unfolding inv_simps preprocess by (auto)
  show "state_invariant acs Is lb' ub' s'" if "bnb_update_state'' acs Is lb' ub' s new = Some s'"
  proof -
    have "assert_simplex (fst new) (update_iatom_in_state' s\<^sub>2 new) = Sat s'"
      using s\<^sub>2 assms ls_cs' that unfolding bnb_update_state''_def ls\<^sub>2_def
      by (auto simp add: Let_def cs'_def elim: sum_to_option.elims)
    moreover have "insert (fst new) (set ls\<^sub>2) = set ls"
    proof -
      have i: "i \<in> set ls"
        unfolding ls_def i_def cs_def i_bounds_to_constraints_def using assms by (auto)
      have "fst new = i"
        using assms unfolding i_def by auto
      also have "insert i (set ls\<^sub>2) = set ls"
        unfolding ls\<^sub>2 using i distinct_ls by (auto)
      finally show ?thesis
        by auto
    qed
    ultimately have "invariant_simplex cs' (set ls) s'"
      using inv assert_simplex_ok unfolding s\<^sub>3_def by metis
    then show ?thesis
      using enumerated_cs' unfolding state_invariant_def cs'_def ls_cs' by (fastforce simp add: Let_def image_Un)
  qed
  show "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb' ub' @ acs))"
    if "bnb_update_state'' acs Is lb' ub' s new = None"
  proof -
    have "\<exists>ds. assert_simplex (fst new) (update_iatom_in_state' s\<^sub>2 new) = Inl ds"
      using s\<^sub>2 assms that unfolding bnb_update_state''_def ls\<^sub>2_def cs'_def ls_cs'
      by (auto simp add: Let_def cs'_def elim: sum_to_option.elims)
    then obtain ds where "assert_simplex (fst new) (update_iatom_in_state' s\<^sub>2 new) = Inl ds"
      by blast
    moreover have "insert (fst new) (set ls\<^sub>2) = set ls"
    proof -
      have i: "i \<in> set ls"
        unfolding ls_def i_def cs_def i_bounds_to_constraints_def using assms by (auto)
      have "fst new = i"
        using assms unfolding i_def by auto
      also have "insert i (set ls\<^sub>2) = set ls"
        unfolding ls\<^sub>2 using i distinct_ls by (auto)
      finally show ?thesis
        by auto
    qed
    ultimately have "set ds \<subseteq> insert (fst new) (set ls\<^sub>2) \<and> minimal_unsat_core (set ds) cs'"
      using assert_simplex_unsat inv unfolding s\<^sub>3_def by blast
    then show ?thesis
      unfolding minimal_unsat_core_def cs'_def by force
  qed
qed

lemma i_bounds_to_constraints:
  "map snd (i_bounds_to_constraints Is lb ub) = bounds_to_constraints Is (snd \<circ> lb) (snd \<circ> ub)"
  unfolding i_bounds_to_constraints_def bounds_to_constraints_def by auto

function bnb_state_core where
  "bnb_state_core cs Is lb ub s =
    (if state_invariant cs Is lb ub s then
    (case check_simplex s of
       (_, Some _) \<Rightarrow> None
     | (s', None) \<Rightarrow> (let v = solution_simplex s' in
         case find (\<lambda> x. v x \<notin> \<int>) Is of
           None \<Rightarrow> Some v
         | Some x \<Rightarrow>
          let new_leq = (fst (ub x), Leq x (rat_of_int \<lfloor>v x\<rfloor>));
              new_geq = (fst (lb x), Geq x (rat_of_int \<lceil>v x\<rceil>));
              ub' = ub(x := (fst (ub x), \<lfloor>v x\<rfloor>));
              lb' = lb(x := (fst (lb x), \<lceil>v x\<rceil>));
              left_b = (bnb_update_state'' cs Is lb ub' s' new_leq \<bind> bnb_state_core cs Is lb ub')
          in case left_b of
                None \<Rightarrow> (bnb_update_state'' cs Is lb' ub s' new_geq \<bind> bnb_state_core cs Is lb' ub) |
                Some v \<Rightarrow> Some v))
      else None)"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda>(_,Is,lb,ub,_). bb_measure (Is,snd \<circ> lb, snd \<circ> ub))", force, goal_cases)
  case (1 cs Is lb ub s s' sres v x new_leq new_geq ub' lb' s'')
  from 1 have "check_simplex s = (s',None)" by auto
  note 1 = 1(1) this 1(4-)
  let ?ubs = "snd \<circ> ub"
  let ?ubs' = "snd \<circ> ub'"
  let ?lbs = "snd \<circ> lb"
  have v: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is ?lbs ?ubs)"
    using state_invariant_simplex 1 by (auto simp add: i_bounds_to_constraints)
  have x: "x \<in> set Is" and "v x \<notin> \<int>"
    using find_Some_set 1 by metis+
  then have "v x \<le> of_int (?ubs x)"
    using bounds_to_constraints_sat v by auto
  then have ub'x: "\<lfloor>v x\<rfloor> < (?ubs x)"
    using floor_less[OF \<open>v x \<notin> \<int>\<close>] by linarith
  have "(\<Sum>i\<leftarrow>Is. ?ubs' i - ?lbs i) = ?ubs' x - ?lbs x + (\<Sum>i\<leftarrow>remove1 x Is. ?ubs' i - ?lbs i)"
    using sum_list_map_remove1[OF x] by blast
  moreover have "?ubs' x - ?lbs x < ?ubs x - ?lbs x"
    unfolding `ub' = ub(x := (fst (ub x), \<lfloor>v x\<rfloor>))` using ub'x by auto
  moreover have "(\<Sum>i\<leftarrow>remove1 x Is. ?ubs' i - ?lbs i) \<le> (\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs i)"
    by (intro sum_list_mono) (use ub'x 1 in auto)
  moreover have "(\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs i) = ?ubs x - ?lbs x + (\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs i)"
    using sum_list_map_remove1[OF x] by blast
  ultimately have "(\<Sum>i\<leftarrow>Is. ?ubs' i - ?lbs i) < (\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs i)"
    by linarith
  thus ?case
    using nonnint_sat_pos_measure'[OF v] 1 by auto
next
  case (2 cs Is lb ub s s' sres v x new_leq new_geq ub' lb' s'')
  from 2 have "check_simplex s = (s',None)" by auto
  note 2 = 2(1) this 2(4-)
  let ?ubs = "snd \<circ> ub"
  let ?lbs = "snd \<circ> lb"
  let ?lbs' = "snd \<circ> lb'"
  have v: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is ?lbs ?ubs)"
    using state_invariant_simplex 2 by (auto simp add: i_bounds_to_constraints)
  have x: "x \<in> set Is" and vx_Int: "v x \<notin> \<int>"
    using find_Some_set 2 by metis+
  then have "of_int (?lbs x) \<le> v x"
    using bounds_to_constraints_sat v by auto
  then have lb'x: "?lbs x < \<lceil>v x\<rceil>"
    by (subst less_ceiling_iff) (use vx_Int Ints_of_int less_eq_rat_def in metis)
  have "(\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs' i) = ?ubs x - ?lbs' x + (\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs' i)"
    using sum_list_map_remove1[OF x] by blast
  moreover have "?ubs x - ?lbs' x < ?ubs x - ?lbs x"
    unfolding `lb' = lb(x := (fst (lb x), \<lceil>v x\<rceil>))` using lb'x by auto
  moreover have "(\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs' i) \<le> (\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs i)"
    by (intro sum_list_mono) (use lb'x 2 in auto)
  moreover have "(\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs i) = ?ubs x - ?lbs x + (\<Sum>i\<leftarrow>remove1 x Is. ?ubs i - ?lbs i)"
    using sum_list_map_remove1[OF x] by blast
  ultimately have "(\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs' i) < (\<Sum>i\<leftarrow>Is. ?ubs i - ?lbs i)"
    by linarith
  thus ?case
    using nonnint_sat_pos_measure'[OF v] 2 by auto
qed

declare bnb_state_core.simps[simp del]

(* TODO: refactor/cleanup proof, remove apply scripts *)
lemma bnb_state_core_sat:
  assumes "state_invariant cs Is lb ub s" "bnb_state_core cs Is lb ub s = Some v"
  shows "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` (set cs), set Is)"
  using assms proof (induction arbitrary: v rule: bnb_state_core.induct )
  case (1 cs Is lb ub s)
  note [simp] = bnb_state_core.simps[of cs Is lb ub s] (* activate simp-rules only for lb ub *)
  obtain s' sres where check: "check_simplex s = (s',sres)" by force
  show ?case
  proof (cases sres)
    case None
    note ni = `state_invariant cs Is lb ub s`
    note s' = check[unfolded None]
    note ok = solution_simplex[OF check_simplex_ok[OF _ s']]
    define r where "r = solution_simplex s'"
    then have r: "r \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub @ cs))"
      using 1(3,4) by (intro state_invariant_simplex[OF _ s']) (auto intro!: state_invariant_simplex)
    have ni_s': "checked_bnc cs Is lb ub s'"
      using ni s' check_simplex_ok
      by (auto simp add: checked_bnc_def state_invariant_def Let_def intro!: checked_invariant_simplex)
    show ?thesis
    proof (cases "find (\<lambda> x. r x \<notin> \<int>) Is")
      case None
      then have "\<forall>x \<in> set Is. r x \<in> \<int>"
        using find_None_iff by metis
      then have r: "r \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` (set cs), set Is)"
        using r by auto
      also have "r = v"
        using 1(3,4) s' None unfolding r_def by auto
      finally show ?thesis
        by simp
    next
      case (Some x)
      have x_Is: "x \<in> set Is"
        by (meson Some find_Some_set)
      note x = Some
      define ub' where "ub' = ub(x := (fst (ub x), \<lfloor>r x\<rfloor>))"
      define new_leq where "new_leq = (fst (ub x), Leq x (rat_of_int \<lfloor>r x\<rfloor>))"
      define lb' where "lb' = lb(x := (fst (lb x), \<lceil>r x\<rceil>))"
      define new_geq where "new_geq = (fst (lb x), Geq x (rat_of_int \<lceil>r x\<rceil>))"
      note lets = ub'_def new_leq_def lb'_def new_geq_def
      show ?thesis
      proof (cases "bnb_update_state'' cs Is lb ub' s' new_leq")
        case (Some s'')
        note s'' = Some
        then show ?thesis
        proof (cases "bnb_state_core cs Is lb ub' s''")
          case (Some v')
          have "x \<in> set Is"
            using x by (meson find_Some_set)
          then have ni': "state_invariant cs Is lb ub' s''"
            apply(intro bnb_update_state_invariant)
            using s' 1(3) ni_s' ub'_def new_leq_def s'' by (auto)
          have "v' \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)"
            apply(rule 1(1))
            using 1 apply(blast)
                      apply(rule sym, rule s', rule refl)
            using r_def apply(blast)
            using x apply(blast)
                  prefer 5 using s'' apply(blast)
            using new_leq_def apply(simp)
                apply(simp)
            using ub'_def apply(simp)
              apply(simp)
             defer
            using Some ni' by (auto)
          also have "v' = v"
            using 1(3,4) s' x r_def s'' ub'_def new_leq_def Some by (auto)
          finally show ?thesis
            by simp
        next
          case None
          note None' = None
          then show ?thesis
          proof (cases "bnb_update_state'' cs Is lb' ub s' new_geq")
            case (None)
            then show ?thesis
              using 1(3,4) s' x r_def lets s'' None' by (auto)
          next
            case (Some s''')
            note Some' = Some
            then show ?thesis
            proof (cases "bnb_state_core cs Is lb' ub s'''")
              case (Some v')
              have ni': "state_invariant cs Is lb' ub s'''"
                apply(rule bnb_update_state_invariant) using Some' 1(3) ni_s' lets x_Is by (auto)
              have "v' \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)"
                apply(rule 1(2))
                using 1 apply(blast)
                            apply(rule sym, rule s', rule refl)
                using r_def apply(blast)
                using x apply(blast)
                        prefer 7 using Some' apply(blast)
                using lets apply(simp)
                using lets  apply(simp)
                using lets apply(simp)
                using lets apply(simp)
                   apply(simp)
                using s'' lets None apply(simp)
                using ni' Some ni by (auto)
              also have "v' = v"
                using 1(3,4) s' s'' x r_def s' lets Some' Some None by auto
              finally show ?thesis
                by simp
            next
              case None
              show ?thesis
                using `bnb_state_core cs Is lb ub' s'' = None`
                  1(3,4) s' s'' x r_def s' lets Some None by auto
            qed
          qed
        qed
      next
        case None
        note None' = None
        then show ?thesis
        proof (cases "bnb_update_state'' cs Is lb' ub s' new_geq")
          case None
          then show ?thesis
            using 1(3,4) s' x r_def lets None' by auto
        next
          case (Some s''')
          note Some' = Some
          then show ?thesis
          proof (cases "bnb_state_core cs Is lb' ub s'''")
            case (Some v')
            have ni': "state_invariant cs Is lb' ub s'''"
              apply(rule bnb_update_state_invariant) using Some Some' 1(3) ni_s' lets x_Is by (auto)
            have "v' \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)"
              apply(rule 1(2))
              using 1 apply(blast)
                          apply(rule sym, rule s', rule refl)
              using r_def apply(blast)
              using x apply(blast)
                      prefer 7 using Some' apply(blast)
              using lets apply(simp)
              using lets  apply(simp)
              using lets apply(simp)
              using lets apply(simp)
                 apply(simp)
              using None' lets apply(simp)
              using ni' Some ni by (auto)
            also have "v' = v"
              using 1(3,4) s' None' x r_def lets Some' Some by auto
            finally show ?thesis
              by simp
          next
            case None
            show ?thesis
              using None' 1(3,4) s' x r_def lets Some None by auto
          qed
        qed
      qed
    qed
  next
    case (Some ds)
    then show ?thesis
      using check 1(3,4) by auto
  qed
qed

lemma bnb_state_core_unsat:
  assumes "state_invariant cs Is lb ub s" "bnb_state_core cs Is lb ub s = None"
    "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub))"
  shows "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` (set cs), set Is)"
  using assms proof (induction rule: bnb_state_core.induct)
  case (1 cs Is lb ub s)
  note ni = `state_invariant cs Is lb ub s`
  note bnb = `bnb_state_core cs Is lb ub s = None`
  note [simp] = bnb_state_core.simps[of cs Is lb ub s]
  obtain sres s' where check: "check_simplex s = (s',sres)" by force
  show ?case
  proof (cases sres)
    case None
    note s' = check[unfolded None]
    define r where "r = solution_simplex s'"
    then have r: "r \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub @ cs))"
      by (intro state_invariant_simplex) (use s' 1(3,4) in auto)
    note 1
    have ni_s': "checked_bnc cs Is lb ub s'"
      using ni s' check_simplex_ok
      by (auto simp add: checked_bnc_def state_invariant_def Let_def intro!: checked_invariant_simplex)
    show ?thesis
    proof (cases "find (\<lambda> x. r x \<notin> \<int>) Is")
      case None
      then show ?thesis
        using ni s' bnb r_def by (auto)
    next
      case (Some x)
      define ub' where "ub' = ub(x := (fst (ub x), \<lfloor>r x\<rfloor>))"
      define new_leq where "new_leq = (fst (ub x), Leq x (rat_of_int \<lfloor>r x\<rfloor>))"
      define lb' where "lb' = lb(x := (fst (lb x), \<lceil>r x\<rceil>))"
      define new_geq where "new_geq = (fst (lb x), Geq x (rat_of_int \<lceil>r x\<rceil>))"
      define bus where "bus = bnb_update_state'' cs Is lb ub' s' new_leq"
      define left_b where "left_b = (bus \<bind> bnb_state_core cs Is lb ub')"
      note lets = ub'_def new_leq_def lb'_def new_geq_def
      have x_Is: "x \<in> set Is" and rx: "r x \<notin> \<int>"
        using Some find_Some_set by metis+
      note x = Some
      show ?thesis
      proof (cases left_b)
        case None
        have v_ub': "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)" if "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub'))"
        proof (cases bus)
          case (None)
          then have "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub' @ cs))"
            using ni_s' x_Is ub'_def bus_def new_leq_def by (intro bnb_update_state_Unsat) (auto)
          then show ?thesis
            using that by auto
        next
          case (Some s'')
          then have "state_invariant cs Is lb ub' s''"
            using ni_s' x_Is bus_def ub'_def new_leq_def
            by (intro bnb_update_state_invariant) (auto)
          moreover have "bnb_state_core cs Is lb ub' s'' = None"
            using None Some unfolding left_b_def by (auto)
          ultimately show ?thesis
            apply(intro 1(1))
            using that Some ni s' x r_def ub'_def bus_def new_leq_def by (auto simp add: fun_upd_def)
        qed
        have v_lb': "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)" if "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb' ub))"
        proof (cases "bnb_update_state'' cs Is lb' ub s' new_geq")
          case (None)
          then have "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb' ub @ cs))"
            using ni_s' x_Is lb'_def bus_def new_geq_def by (intro bnb_update_state_Unsat) (auto)
          then show ?thesis
            using that by auto
        next
          case (Some s'')
          then have "state_invariant cs Is lb' ub s''"
            using ni_s' x_Is bus_def lb'_def new_geq_def
            by (intro bnb_update_state_invariant) (auto)
          moreover have "bnb_state_core cs Is lb' ub s'' = None"
            using bnb ni s' x r_def None Some unfolding left_b_def bus_def lets
            by (auto simp add: Let_def)
          ultimately show ?thesis
            apply(intro 1(2))
            using that Some ni s' x r_def lb'_def bus_def new_geq_def None
            unfolding left_b_def bus_def lets fun_upd_def by (auto)
        qed
        show ?thesis
        proof rule
          assume v: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs, set Is)"
          then have vx: "v x \<in> \<int>"
            using x_Is by auto
          show False
          proof (cases "v x \<le> r x")
            case True
            then have "v x \<le> rat_of_int \<lfloor>r x\<rfloor>"
              using vx int_le_floor_iff by blast
            then have "\<forall>i\<in>set Is. of_int (snd (lb i)) \<le> v i \<and> v i \<le> of_int (snd (ub' i))"
              using 1(5) unfolding ub'_def unfolding i_bounds_to_constraints
                bounds_to_constraints_sat by auto
            then have "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub'))"
              unfolding i_bounds_to_constraints bounds_to_constraints_sat by simp
            then show ?thesis
              using v_ub' v by blast
          next
            case False
            then have "rat_of_int \<lceil>r x\<rceil> \<le> v x"
              using vx int_ge_ceiling_iff by fastforce
            then have "\<forall>i\<in>set Is. of_int (snd (lb' i)) \<le> v i \<and> v i \<le> of_int (snd (ub i))"
              using 1(5) unfolding lb'_def unfolding i_bounds_to_constraints
                bounds_to_constraints_sat by auto
            then have "v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb' ub))"
              unfolding i_bounds_to_constraints bounds_to_constraints_sat by simp
            then show ?thesis
              using v_lb' v by blast
          qed
        qed
      next
        case (Some a)
        then show ?thesis
          using bnb ni s' bnb r_def x
          apply (auto simp add: left_b_def bus_def Let_def)
            (* TODO: Why is the simplifier not unfolding ub' ? *)
          unfolding lets by auto
      qed
    qed
  next
    case (Some a)
    then have "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd (i_bounds_to_constraints Is lb ub @ cs))"
      using ni check by (intro state_invariant_simplex_Unsat) (auto)
    then have "\<not> v \<Turnstile>\<^sub>c\<^sub>s set (map snd cs)"
      using 1 by auto
    then show ?thesis
      by simp
  qed
qed

partial_function (option) bnb_state_core_p where
  [code]: "bnb_state_core_p cs Is lb ub s =
    (case check_simplex s of
       (_, Some _) \<Rightarrow> Some None
     | (s', None) \<Rightarrow> (let v = solution_simplex s' in
         case find (\<lambda> x. v x \<notin> \<int>) Is of
           None \<Rightarrow> Some (Some v)
         | Some x \<Rightarrow>
          let new_leq = (fst (the (Mapping.lookup ub x)), Leq x (rat_of_int \<lfloor>v x\<rfloor>));
              new_geq = (fst (the (Mapping.lookup lb x)), Geq x (rat_of_int \<lceil>v x\<rceil>));
              ub' = Mapping.update x (fst (the (Mapping.lookup ub x)), \<lfloor>v x\<rfloor>) ub;
              lb' = Mapping.update x (fst (the (Mapping.lookup lb x)), \<lceil>v x\<rceil>) lb in
           (case bnb_update_state'' cs Is (the \<circ> (Mapping.lookup lb)) (the \<circ> (Mapping.lookup ub')) s' new_leq of
                       Some s'' \<Rightarrow> bnb_state_core_p cs Is lb ub' s'' |
                       None \<Rightarrow> Some None) \<bind>
           (\<lambda>t. case t of
                None \<Rightarrow> case bnb_update_state'' cs Is (the \<circ> (Mapping.lookup lb')) (the \<circ> (Mapping.lookup ub)) s' new_geq of
                          Some s'' \<Rightarrow> bnb_state_core_p cs Is lb' ub s'' |
                          None \<Rightarrow> Some None |
                Some v \<Rightarrow> Some (Some v))))"


lemma bnb_state_core_p:
  assumes "lb = (the \<circ> (Mapping.lookup lb\<^sub>m))" "ub = (the \<circ> (Mapping.lookup ub\<^sub>m))"
    "state_invariant cs Is lb ub s"
  shows "bnb_state_core_p cs Is lb\<^sub>m ub\<^sub>m s = Some (bnb_state_core cs Is lb ub s)"
  using assms proof (induction cs Is lb ub s arbitrary: lb\<^sub>m ub\<^sub>m rule: bnb_state_core.induct)
  case (1 cs Is lb ub s)
  obtain s' sres where check: "check_simplex s = (s',sres)" by force
  show ?case
  proof (cases sres)
    case (Some a)
    then show ?thesis using check by (simp add: bnb_state_core_p.simps bnb_state_core.simps)
  next
    case None
    with check have s': "check_simplex s = (s',None)" by auto
    define i_b where "i_b = i_bounds_to_constraints Is lb ub @ cs"
    have "checked_simplex i_b (fst ` set i_b) s'"
      apply(rule check_simplex_ok[of _ _ s])
      using s' 1(5) unfolding state_invariant_def i_b_def by (metis)+
    then have c_bnc: "checked_bnc cs Is lb ub s'"
      using 1(5) unfolding state_invariant_def i_b_def checked_bnc_def by metis
    define v where "v = solution_simplex s'"  
    show ?thesis
    proof (cases "find (\<lambda> x. v x \<notin> \<int>) Is")
      case None
      then show ?thesis using 1 by (simp add: v_def s' bnb_state_core_p.simps bnb_state_core.simps)
    next
      case (Some x)
      note Some1 = Some
      have x_Is: "x \<in> set Is"
        by (meson Some1 find_Some_set)
      define new_leq where "new_leq = (fst (ub x), Leq x (rat_of_int \<lfloor>v x\<rfloor>))"
      define new_geq where "new_geq = (fst  (lb x), Geq x (rat_of_int \<lceil>v x\<rceil>))"
      define ub' where "ub' = ub(x := (fst (ub x), \<lfloor>v x\<rfloor>))"
      define lb' where "lb' = lb(x := (fst (lb x), \<lceil>v x\<rceil>))"
      define new_leq where "new_leq = (fst (ub x), Leq x (rat_of_int \<lfloor>v x\<rfloor>))"
      define ub'\<^sub>m where "ub'\<^sub>m = Mapping.update x (fst (the (Mapping.lookup ub\<^sub>m x)), \<lfloor>v x\<rfloor>) ub\<^sub>m"
      define lb'\<^sub>m where "lb'\<^sub>m = Mapping.update x (fst (the (Mapping.lookup lb\<^sub>m x)), \<lceil>v x\<rceil>) lb\<^sub>m"
      define bus\<^sub>u where "bus\<^sub>u = bnb_update_state'' cs Is lb ub' s' new_leq"
      define bus\<^sub>l where "bus\<^sub>l = bnb_update_state'' cs Is lb' ub s' new_geq"
      define t\<^sub>p\<^sub>u where "t\<^sub>p\<^sub>u = (case bus\<^sub>u of Some s'' \<Rightarrow> bnb_state_core_p cs Is lb\<^sub>m ub'\<^sub>m s'' |
                       None \<Rightarrow> Some None)"
      define t\<^sub>u where "t\<^sub>u = (case bus\<^sub>u of Some s'' \<Rightarrow> bnb_state_core cs Is lb ub' s'' |
                       None \<Rightarrow> None)"
      have t\<^sub>u: "t\<^sub>p\<^sub>u = Some t\<^sub>u"
      proof (cases bus\<^sub>u)
        case None
        then show ?thesis unfolding t\<^sub>p\<^sub>u_def t\<^sub>u_def by simp
      next
        case (Some s'')
        have "state_invariant cs Is lb ub' s''"
          apply(rule bnb_update_state_invariant[of _ _ _ _ _ x, where t=False])
              apply(rule c_bnc)
             apply (meson Some1 find_Some_set)
          using new_leq_def[unfolded v_def] apply(blast)
          using ub'_def v_def apply(simp)
          using ub'_def v_def apply(simp)
          using Some unfolding bus\<^sub>u_def ub'_def new_leq_def 1 comp_def v_def by auto
        then have "bnb_state_core_p cs Is lb\<^sub>m ub'\<^sub>m s'' = Some (bnb_state_core cs Is lb ub' s'')"
          apply(intro 1(1)[OF _ sym refl, OF _ s'])
          using 1 Some1 apply(auto simp add: v_def ub'_def)[7]
          subgoal
            using Some unfolding bus\<^sub>u_def ub'_def new_leq_def 1 comp_def v_def by blast
          using 1 apply(blast)
          using ub'_def ub'\<^sub>m_def 1 apply(auto)[1]
          by blast
        then show ?thesis using Some unfolding t\<^sub>p\<^sub>u_def t\<^sub>u_def by simp
      qed
      have "bnb_state_core_p cs Is lb\<^sub>m ub\<^sub>m s =
            t\<^sub>p\<^sub>u \<bind>
            (\<lambda>t. case t of
                   None \<Rightarrow> case bus\<^sub>l of
                     Some s'' \<Rightarrow> bnb_state_core_p cs Is lb'\<^sub>m ub\<^sub>m s'' |
                     None \<Rightarrow> Some None |
                   Some v \<Rightarrow> Some (Some v))"
        using s' Some1
        unfolding 1 t\<^sub>p\<^sub>u_def bus\<^sub>u_def bus\<^sub>l_def ub'_def lb'_def v_def new_leq_def new_geq_def ub'\<^sub>m_def lb'\<^sub>m_def
        by (subst bnb_state_core_p.simps) (auto simp add: 1 Let_def fun_upd_comp  v_def)
      then have bp: "bnb_state_core_p cs Is lb\<^sub>m ub\<^sub>m s = (case t\<^sub>u of
                   None \<Rightarrow> case bus\<^sub>l of
                     Some s'' \<Rightarrow> bnb_state_core_p cs Is lb'\<^sub>m ub\<^sub>m s'' |
                     None \<Rightarrow> Some None |
                   Some v \<Rightarrow> Some (Some v))"
        unfolding t\<^sub>u by simp
      have b: "bnb_state_core cs Is lb ub s =
            (case t\<^sub>u of
                   None \<Rightarrow> case bus\<^sub>l of
                     Some s'' \<Rightarrow> bnb_state_core cs Is lb' ub s'' |
                     None \<Rightarrow> None |
                   Some v \<Rightarrow> (Some v))"
        using s' Some1
        unfolding 1 comp_def t\<^sub>u_def bus\<^sub>u_def bus\<^sub>l_def ub'_def lb'_def v_def new_leq_def new_geq_def ub'\<^sub>m_def lb'\<^sub>m_def
        using 1(5)
        by (subst bnb_state_core.simps) (auto simp add: 1 Let_def v_def split: Option.bind_splits option.splits)
      then show ?thesis
      proof (cases t\<^sub>u)
        case None
        note None' = None
        then show ?thesis
        proof (cases bus\<^sub>l)
          case None
          then show ?thesis using None' unfolding bp b by (simp)
        next
          case (Some s'')
          have "state_invariant cs Is lb' ub s''"
            apply(rule bnb_update_state_invariant[where new = new_geq and t = True])
                apply(rule c_bnc)
            using x_Is apply(simp)
            using new_geq_def apply(simp)
            subgoal unfolding lb'_def lb'\<^sub>m_def 1 by auto[1]
            using Some unfolding bus\<^sub>l_def lb'_def new_geq_def v_def 1 comp_def by auto
          then show ?thesis  using None' Some unfolding bp b apply (simp)
            apply(rule 1(2)[of _ _ _ _ _ _ _ _ t\<^sub>u, OF _ sym refl, OF _ s'])
            using 1 Some1 apply(auto simp add: v_def lb'_def)[7]
            subgoal
              unfolding t\<^sub>u_def bus\<^sub>u_def ub'_def new_leq_def 1 comp_def v_def by (auto split: option.splits)
                apply(auto)[1]
            subgoal
              unfolding bus\<^sub>l_def lb'_def new_geq_def v_def 1 comp_def by blast
            subgoal unfolding lb'_def lb'\<^sub>m_def 1 by auto[1]
            subgoal unfolding 1 by simp
            by simp
        qed
      next
        case (Some a)
        then show ?thesis unfolding bp b by simp
      qed
    qed
  qed
qed

definition bnb_state_init where
  "bnb_state_init cs Is lb ub =
    (let
     lb' = zip Is [0 ..<length Is];
     ub' = zip Is [length Is ..<length Is + length Is];
     lb' = map (\<lambda>(x,y). (x, y, lb x)) lb';
     ub' = map (\<lambda>(x,y). (x, y, ub x)) ub';
     lb_m = Mapping.of_alist lb';
     ub_m = Mapping.of_alist ub';
     cs' = zip [length Is + length Is ..< length Is + length Is + length cs] cs;
     bs = i_bounds_to_constraints Is (the \<circ> (Mapping.lookup lb_m)) (the \<circ> (Mapping.lookup ub_m)) @ cs';
     s = (assert_all_simplex (map fst bs) (init_simplex bs))
     in (cs', lb_m, ub_m, s))
    "

lemma bnb_state_init:
  assumes "distinct Is" "bnb_state_init cs Is lb ub = (cs', lb_m, ub_m, s')" "s' = Inr s"
  shows "state_invariant cs' Is (the \<circ> Mapping.lookup lb_m) (the \<circ> Mapping.lookup ub_m) s"
proof -
  define bs where "bs = i_bounds_to_constraints Is (the \<circ> Mapping.lookup lb_m) (the \<circ> Mapping.lookup ub_m) @ cs'"
  have ub_m: "ub_m = Mapping.of_alist (map2 (\<lambda>x y. (x, y, ub x)) Is [length Is..<length Is + length Is])"
    using assms unfolding bnb_state_init_def by (simp add: Let_def)
  have lb_m: "lb_m = Mapping.of_alist (map2 (\<lambda>x y. (x, y, lb x)) Is [0..<length Is])"
    using assms unfolding bnb_state_init_def by (simp add: Let_def)
  have 1: "map (\<lambda>x. fst (the (map_of (map2 (\<lambda>x y. (x, y, f x)) xs ys) x))) xs = ys"
    if "length ys = length xs" "distinct xs" for ys::"'c list" and xs and f::"'a \<Rightarrow> 'b"
    using that 
  proof (induction xs arbitrary: ys)
    case (Cons x xs)
    then have "\<exists>y ys'. ys = y # ys'"
      by (metis length_nth_simps(2) list.exhaust list.map(1) list.map(2) list.simps(3) list.size(3) nth_Cons_0 nth_Cons_Suc zip_Nil)
    then obtain y ys' where "ys = y # ys'"
      by blast
    then show ?case
      apply(auto)
      using Cons apply(auto)
      by (smt map_eq_conv)
  qed simp
  have "map (\<lambda>x. fst (the (Mapping.lookup (Mapping.of_alist (map2 (\<lambda>x y. (x, y, lb x)) Is [0..<length Is])) x))) Is
   = [0..<length Is]"
    using 1[of " [0..<length Is]" "Is" lb] assms
    unfolding lb_m by (simp add: lookup_of_alist)
  moreover have "map (\<lambda>x. fst (the (Mapping.lookup ub_m x))) Is
   = [length Is..<length Is + length Is]"
    using 1[of " [length Is..<length Is + length Is]" "Is" ub] assms
    unfolding ub_m lookup_of_alist by simp
  ultimately have "enumerated 0 bs"
    unfolding bs_def enumerated[symmetric] apply(auto simp add: i_bounds_to_constraints_def lb_m comp_def)
    using assms unfolding bnb_state_init_def apply(auto simp add: Let_def)
    by (smt add.commute add.left_commute append_assoc upt_add_eq_append zero_le)
  moreover have "invariant_simplex bs ({} \<union> set (map fst bs)) s"
    apply(rule assert_all_simplex_ok)
     apply(rule checked_invariant_simplex)
     apply(rule init_simplex)
    using assms unfolding bnb_state_init_def by (auto simp add: bs_def Let_def)
  ultimately show ?thesis
    unfolding state_invariant_def unfolding bs_def by (simp add: Let_def image_Un)
qed

lemma bnb_state_init':
  assumes "distinct Is" "bnb_state_init cs Is lb ub = (cs', lb_m, ub_m, s')" "s' = Inl I"
  shows "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set ((bounds_to_constraints Is lb ub) @ cs)"
proof -
  define bs where "bs = i_bounds_to_constraints Is (the \<circ> Mapping.lookup lb_m) (the \<circ> Mapping.lookup ub_m) @ cs'"
  have ub_m: "ub_m = Mapping.of_alist (map2 (\<lambda>x y. (x, y, ub x)) Is [length Is..<length Is + length Is])"
    using assms unfolding bnb_state_init_def by (simp add: Let_def)
  have lb_m: "lb_m = Mapping.of_alist (map2 (\<lambda>x y. (x, y, lb x)) Is [0..<length Is])"
    using assms unfolding bnb_state_init_def by (simp add: Let_def)
  have "map (\<lambda>x. snd (the (map_of (map2 (\<lambda>x y. (x, y, f x)) xs ys) x))) xs = map f xs"
    if "length ys = length xs" "distinct xs" for ys::"'c list" and xs and f::"'a \<Rightarrow> 'b"
    using that 
  proof (induction xs arbitrary: ys)
    case (Cons x xs)
    then have "\<exists>y ys'. ys = y # ys'"
      by (metis length_nth_simps(2) list.exhaust list.map(1) list.map(2) list.simps(3) list.size(3) nth_Cons_0 nth_Cons_Suc zip_Nil)
    then obtain y ys' where "ys = y # ys'"
      by blast
    then show ?case
      using Cons by auto
  qed simp
  then have 1: "(snd (the (map_of (map2 (\<lambda>x y. (x, y, f x)) xs ys) x))) = f x"
    if "length ys = length xs" "distinct xs" "x \<in> set xs"for ys::"'c list" and x xs and f::"'a \<Rightarrow> 'b"
    using map_eq_conv that by auto
  have "set I \<subseteq> set (map fst bs) \<union> {} \<and> minimal_unsat_core (set I) bs"
    apply(rule assert_all_simplex_unsat[of _ _ "init_simplex bs"])
    apply(rule checked_invariant_simplex)
    apply(rule init_simplex)
    using assms bs_def by (auto simp add: Let_def bnb_state_init_def)
  then have "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (map snd bs)"
    unfolding minimal_unsat_core_def by auto
  also have "map snd bs = bounds_to_constraints Is (snd \<circ> (the \<circ> Mapping.lookup lb_m))
                                                   (snd \<circ> (the \<circ> Mapping.lookup ub_m)) @ map snd cs'"
    unfolding bs_def by (simp add: i_bounds_to_constraints)
  also have "bounds_to_constraints Is (snd \<circ> (the \<circ> Mapping.lookup lb_m)) (snd \<circ> (the \<circ> Mapping.lookup ub_m))
    = bounds_to_constraints Is lb ub"
  proof -
    have "snd (the (Mapping.lookup lb_m x)) = lb x" if "x \<in> set Is" for x
      using that `distinct Is` unfolding lb_m lookup_of_alist by (auto simp add: 1)
    moreover have "snd (the (Mapping.lookup ub_m x)) = ub x" if "x \<in> set Is" for x
      using that `distinct Is` unfolding ub_m lookup_of_alist by (auto simp add: 1)
    ultimately show ?thesis
      unfolding bounds_to_constraints_def by simp
  qed
  also have "map snd cs' = cs"
    using assms unfolding bnb_state_init_def by (auto simp add: Let_def)
  finally show ?thesis
    by simp
qed

abbreviation (input) "Ltc \<equiv> Le_Constraint Lt_Rel"

(* There already exists a function `lec_of_constraint`, but it does not handle every
   cases. *)
primrec constraint_to_le_constraint where
  "constraint_to_le_constraint (LEQ l x) = [Leqc l x]"
| "constraint_to_le_constraint (GEQ l x) = [Leqc (-l) (-x)]"
| "constraint_to_le_constraint (LT l x) = [Ltc l x]"
| "constraint_to_le_constraint (GT l x) = [Ltc (-l) (-x)]"
| "constraint_to_le_constraint (EQ l x) = [Leqc l x, Leqc (-l) (-x)]"

lemma constraint_to_le_constraint:
  assumes "constraint_to_le_constraint c = cs"
  shows "v \<Turnstile>\<^sub>c c \<longleftrightarrow> (\<forall> c' \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c')"
  by (insert assms, cases c, auto simp: valuate_minus valuate_uminus)

definition var_list :: "constraint list \<Rightarrow> var list" where
  "var_list cs = (let lecs = concat (map constraint_to_le_constraint cs);
   polys = map lec_poly lecs in
   remdups (concat (map vars_list polys)))"

lemma varlist_distinct:
  shows "distinct (var_list cs)"
  unfolding var_list_def by simp

(* It could be interesting to re-index variables so that there are all consecutive
   in the normalization operation. *)
definition normalize where
  "normalize cs = concat (map constraint_to_le_constraint cs)"

lemma normalize_satisfies: "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (\<forall> c \<in> set (normalize cs). v \<Turnstile>\<^sub>l\<^sub>e c)"
  unfolding normalize_def using constraint_to_le_constraint by auto

lemma constrtoleconstr_preserves_vars:
  assumes "lec \<in> set (normalize cs)"
  shows "vars (lec_poly lec) \<subseteq> set (var_list cs)"
  using assms normalize_def set_vars_list var_list_def by auto

definition integral_linear_poly where "integral_linear_poly l = (\<forall> x. coeff l x \<in> \<int>)"
abbreviation "integral_constraint c \<equiv>
              (integral_linear_poly (lec_poly c) \<and> lec_const c \<in> \<int>)"
definition integral_constraints where
"integral_constraints cs = (\<forall> c \<in> set cs. integral_constraint c)"

primrec max_coeff :: "rat le_constraint \<Rightarrow> rat" where
"max_coeff (Le_Constraint _ l c) = Max ({\<bar>c\<bar>} \<union> {\<bar>coeff l x\<bar> | x. x \<in> vars l})"

lemma max_coeff_const: "max_coeff (Le_Constraint r l c) \<ge> \<bar>c\<bar>"
  using finite_vars by auto

lemma max_coeff: "max_coeff (Le_Constraint r l c) \<ge> \<bar>coeff l x\<bar>"
proof cases
  assume "x \<in> vars l"
  hence "\<bar>coeff l x\<bar> \<in> {\<bar>c\<bar>} \<union> {\<bar>coeff l x\<bar> | x. x \<in> vars l}" by blast
  thus ?thesis using finite_vars by simp
next
  assume "x \<notin> vars l"
  hence "\<bar>coeff l x \<bar> = 0" using coeff_zero by auto
  also have "0 \<le> max_coeff (Le_Constraint r l c)"
    using max_coeff_const[of c r l] by linarith
  finally show ?thesis by blast
qed

lemma integral_max_coeff:
  assumes "integral_constraint c"
  shows "max_coeff c \<in> \<int>"
proof -
  obtain r l x where c: "c = Le_Constraint r l x"
    using le_constraint.collapse[of c] by metis

  have "max_coeff c \<in> {\<bar>x\<bar>} \<union> {\<bar>coeff l i\<bar> | i. i \<in> vars l}"
    unfolding c max_coeff.simps
    by (rule Max_in, insert finite_vars, simp_all)
  moreover have "{\<bar>x\<bar>} \<subseteq> \<int>" using assms unfolding c by auto
  moreover have "{\<bar>coeff l i\<bar> | i. i \<in> vars l} \<subseteq> \<int>"
    using assms unfolding c integral_linear_poly_def by auto
  ultimately show ?thesis by blast
qed

definition max_coeff_constraints where
"max_coeff_constraints cs = Max (set (0 # map max_coeff cs))"

lemma max_coeff_constraints:
  assumes "c \<in> set cs"
  shows "\<bar>lec_const c\<bar> \<le> max_coeff_constraints cs" (is ?thes1)
    and "\<bar>coeff (lec_poly c) x\<bar> \<le> max_coeff_constraints cs" (is ?thes2)
proof -
  have "\<bar>lec_const c\<bar> \<le> max_coeff c"
    using max_coeff_const le_constraint.collapse by metis
  moreover have "max_coeff c \<le> max_coeff_constraints cs"
    unfolding max_coeff_constraints_def using assms by auto
  ultimately show ?thes1 by linarith
  have "\<bar>coeff (lec_poly c) x\<bar> \<le> max_coeff c"
    using max_coeff le_constraint.collapse by metis
  moreover have "max_coeff c \<le> max_coeff_constraints cs"
    unfolding max_coeff_constraints_def using assms by auto
  ultimately show ?thes2 by linarith
qed

lemma max_coeff_constraints_0: "0 \<le> max_coeff_constraints cs" 
  unfolding max_coeff_constraints_def by auto


primrec lec_coeffs :: "rat le_constraint \<Rightarrow> rat set" where
"lec_coeffs (Le_Constraint _ l c) = {c} \<union> {coeff l x | x. x \<in> vars l}"

lemma lecconst_in_leccoeffs:
  shows "lec_const lec \<in> lec_coeffs lec"
  unfolding lec_coeffs_def lec_const_def
  by (smt Set.insert_def insertI1 le_constraint.exhaust le_constraint.rec
      le_constraint.sel(3) lec_const_def singleton_conv)

lemma equal_leccoeffs_impl_equal_maxcoeff:
  assumes "lec_coeffs lec1 = lec_coeffs lec2"
  shows "max_coeff lec1 = max_coeff lec2" and
    "max_coeff_constraints [lec1] = max_coeff_constraints [lec2]"
proof -
  let ?fct = "rec_le_constraint (\<lambda>_ l c. {\<bar>c\<bar>} \<union> {\<bar>coeff l x\<bar> |x. x \<in> vars l})"
  have "\<And>lec. rec_le_constraint (\<lambda>_ l c. {\<bar>c\<bar>}) lec = {\<bar>lec_const lec\<bar>}"
    by (metis le_constraint.exhaust_sel le_constraint.rec)
  moreover have "\<And>lec. rec_le_constraint (\<lambda>_ l c. {\<bar>coeff l x\<bar> |x. x \<in> vars l}) lec =
      {\<bar> coeff (lec_poly lec) x \<bar> |x. x \<in> vars (lec_poly lec)}"
  proof -
    fix lec :: "'a le_constraint"
    obtain ll :: "'a le_constraint \<Rightarrow> le_rel" and lla :: "'a le_constraint \<Rightarrow> linear_poly"
      and aa :: "'a le_constraint \<Rightarrow> 'a" where
      f1: "\<And>l. Le_Constraint (ll l) (lla l) (aa l) = l"
      by (metis (no_types) le_constraint.exhaust)
    then have f2: "\<And>l. lec_poly l = lla l" by (metis le_constraint.sel(2))
    have "\<And>f l. f (ll l) (lla l) (aa l) = (rec_le_constraint f l::rat set)"
      using f1 by (metis le_constraint.rec)
    then show
      "rec_le_constraint (\<lambda>l la a. {\<bar>Abstract_Linear_Poly.coeff la n\<bar> |n. n \<in> vars la}) lec
      = {\<bar>Abstract_Linear_Poly.coeff (lec_poly lec) n\<bar> |n. n \<in> vars (lec_poly lec)}"
      using f2 by presburger
  qed
  ultimately have "\<And>lec. ?fct lec = {\<bar>lec_const lec\<bar>} \<union>
      {\<bar> coeff (lec_poly lec) x \<bar> |x. x \<in> vars (lec_poly lec)}"
    by (smt insertE le_constraint.collapse le_constraint.rec mem_Collect_eq)
  moreover have "\<And>lec. abs ` ({lec_const lec } \<union>
      { coeff (lec_poly lec) x |x. x \<in> vars (lec_poly lec)}) = {\<bar>lec_const lec\<bar>} \<union>
      {\<bar> coeff (lec_poly lec) x \<bar> |x. x \<in> vars (lec_poly lec)}" by auto
  moreover have "{lec_const lec1 } \<union> { coeff (lec_poly lec1) x |x. x \<in> vars (lec_poly lec1)}
     = {lec_const lec2 } \<union> { coeff (lec_poly lec2) x |x. x \<in> vars (lec_poly lec2)}"
  proof -
    have "\<exists>l la. lec_coeffs (Le_Constraint la (lec_poly lec1) (lec_const lec1)) =
      lec_coeffs (Le_Constraint l (lec_poly lec2) (lec_const lec2))"
      by (metis assms le_constraint.exhaust le_constraint.sel(2) le_constraint.sel(3))
    then show ?thesis by simp
  qed
  ultimately have "?fct lec1 = ?fct lec2" by metis
  hence 1: "rec_le_constraint (\<lambda>_ l c. Max({\<bar>c\<bar>} \<union>
            {\<bar>Abstract_Linear_Poly.coeff l x\<bar> |x. x \<in> vars l})) lec1 =
            rec_le_constraint (\<lambda>_ l c. Max({\<bar>c\<bar>} \<union>
            {\<bar>Abstract_Linear_Poly.coeff l x\<bar> |x. x \<in> vars l})) lec2"
    by (metis (no_types, lifting) le_constraint.collapse le_constraint.rec)
  thus "max_coeff_constraints [lec1] = max_coeff_constraints [lec2]"
    unfolding max_coeff_constraints_def max_coeff_def by simp
  thus "max_coeff lec1 = max_coeff lec2" unfolding max_coeff_def using 1 by simp
qed

lemma equal_mapleccoeffs_impl_equal_maxcoeff:
  assumes "map lec_coeffs lecs1 = map lec_coeffs lecs2"
  shows "map max_coeff lecs1 = map max_coeff lecs2" and
    "max_coeff_constraints lecs1 = max_coeff_constraints lecs2"
proof -
  have "\<And>i. max_coeff (lecs1 ! i) = max_coeff (lecs2 ! i)"
  proof(goal_cases)
    case (1 i)
    then show ?case using assms equal_leccoeffs_impl_equal_maxcoeff
      length_map map_nth_conv by (metis (no_types, lifting) undef_vec)
  qed
  hence "\<And>i. (map max_coeff lecs1) ! i = (map max_coeff lecs2) ! i"
    by (metis assms length_map nth_map undef_vec)
  thus "map max_coeff lecs1 = map max_coeff lecs2"
    by (metis assms length_map nth_equalityI)
  thus "max_coeff_constraints lecs1 = max_coeff_constraints lecs2"
    unfolding max_coeff_constraints_def by simp
qed

definition constraints_to_pairs ::
  "rat le_constraint list \<Rightarrow> (linear_poly \<times> rat) list \<times> (linear_poly \<times> rat) list"
where "constraints_to_pairs cs =
  (let leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs in
   let lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs in
   (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
    map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs))"

lemma constraints_to_pairs:
  assumes "constraints_to_pairs cs = (leq_pairs, lt_pairs)"
  shows "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> ((\<forall> (l, x) \<in> set leq_pairs. (l \<lbrace> v \<rbrace>) \<le> x) \<and>
                                       (\<forall> (l, x) \<in> set lt_pairs. (l \<lbrace> v \<rbrace>) < x))"
    (is "?L \<longleftrightarrow> ?R")
  and "integral_constraints cs \<Longrightarrow>
      (l, x) \<in> set leq_pairs \<union> set lt_pairs \<Longrightarrow> integral_linear_poly l \<and> x \<in> \<int>"
    (is "?INT0 \<Longrightarrow> ?LX \<Longrightarrow> ?INT1")
  and "(l, x) \<in> set leq_pairs \<union> set lt_pairs \<Longrightarrow>
        \<bar>coeff l i\<bar> \<le> max_coeff_constraints cs \<and> \<bar>x\<bar> \<le> max_coeff_constraints cs"
    (is "?LX' \<Longrightarrow> ?BND")
proof -
  define leq_cs where "leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs"
  define lt_cs where "lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs"
  have "constraints_to_pairs cs = (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
                                   map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs)"
    unfolding constraints_to_pairs_def leq_cs_def lt_cs_def
    by metis
  hence leq_pairs: "leq_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs"
     and lt_pairs: "lt_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs"
    using assms by auto


  have constructor: "\<And> c. c = Leq_Rel \<or> c = Lt_Rel"
  proof -
    fix c show "c = Leq_Rel \<or> c = Lt_Rel" by (cases c, simp_all)
  qed

  have "\<forall> c \<in> set leq_cs. lec_rel c = Leq_Rel" unfolding leq_cs_def by fastforce
  (* Why do automatic proving perform so bad on the following statement? Is there
     an infinite simplifications loop or something like that? *)
  hence leq_decomp: "\<forall> c \<in> set leq_cs. c = Le_Constraint Leq_Rel (lec_poly c) (lec_const c)"
    using leq_cs_def le_constraint.collapse by metis
  have "\<forall> c \<in> set lt_cs. lec_rel c = Lt_Rel" unfolding lt_cs_def by fastforce
  hence lt_decomp: "\<forall> c \<in> set lt_cs. c = Le_Constraint Lt_Rel (lec_poly c) (lec_const c)"
    using leq_cs_def le_constraint.collapse by metis

  have sets: "set cs = set leq_cs \<union> set lt_cs"
    unfolding leq_cs_def lt_cs_def using constructor by auto
  have "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
        (\<forall> c \<in> set leq_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<and> (\<forall> c \<in> set lt_cs. v \<Turnstile>\<^sub>l\<^sub>e c)"
    unfolding leq_cs_def lt_cs_def using constructor by auto
  also have "(\<forall> c \<in> set leq_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
             (\<forall> c \<in> set leq_cs. ((lec_poly c) \<lbrace> v \<rbrace>) \<le> (lec_const c))"
    using leq_decomp satisfiable_le_constraint.simps[of v] rel_of.simps(1) by metis
  also have "(\<forall> c \<in> set lt_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
             (\<forall> c \<in> set lt_cs. ((lec_poly c) \<lbrace> v \<rbrace>) < (lec_const c))"
    using lt_decomp satisfiable_le_constraint.simps[of v] rel_of.simps(2) by metis
  finally show "?L \<longleftrightarrow> ?R" unfolding leq_pairs lt_pairs by auto

  show "?INT0 \<Longrightarrow> ?LX \<Longrightarrow> ?INT1"
    unfolding integral_constraints_def leq_pairs lt_pairs sets
    by auto

  assume "?LX'"
  then obtain c where c: "c \<in> set cs"
                and l: "l = lec_poly c" and x: "x = lec_const c"
    unfolding leq_pairs lt_pairs sets by auto
  show ?BND
    unfolding l x using max_coeff_constraints[OF c]
    by blast
qed

lift_definition vec_of_poly :: "linear_poly \<Rightarrow> nat \<Rightarrow> rat vec" is
  "\<lambda> l n. vec n l"
  .

lemma vec_of_poly_dim[simp]: "vec_of_poly v n \<in> carrier_vec n"
  by (transfer, auto)

lemma inverse_vec_of_poly:
  assumes "n > max_var l"
  shows "poly_of_vec (vec_of_poly l n) = l"
proof -
  have "\<forall> i \<ge> n. i \<notin> vars l" using assms max_var_max by fastforce
  thus ?thesis by (transfer, force)
qed

lemma dot_vec_of_poly:
  assumes v: "v \<in> carrier_vec n"
  assumes l: "n > Abstract_Linear_Poly.max_var l"
  shows "(vec_of_poly l n) \<bullet> v = (l \<lbrace> val_of_vec v \<rbrace>)"
  using valuate_poly_of_vec[OF v, of "vec_of_poly l n"]
        inverse_vec_of_poly[OF l] by simp

lemma integral_vec_of_poly:
  "integral_linear_poly l \<Longrightarrow> vec_of_poly l n \<in> \<int>\<^sub>v"
  unfolding integral_linear_poly_def
  by (transfer, auto simp: Ints_vec_def)


lemma vec_of_poly_bound:
  "\<forall> x. \<bar>coeff l x\<bar> \<le> Bnd \<Longrightarrow> vec_of_poly l n \<in> Bounded_vec Bnd"
  by (transfer, auto simp: Bounded_vec_def)

abbreviation "lec_max_var \<equiv> max_var \<circ> lec_poly"

definition constraints_max_var :: "rat le_constraint list \<Rightarrow> nat" where
"constraints_max_var cs = Max (set (0 # map lec_max_var cs))"

lemma constraints_max_var_to_pairs:
  assumes "constraints_to_pairs cs = (leq_pairs, lt_pairs)"
  assumes "(l, x) \<in> set leq_pairs \<union> set lt_pairs"
  shows "max_var l \<le> constraints_max_var cs"
proof -
  define leq_cs where "leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs"
  define lt_cs where "lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs"
  have "constraints_to_pairs cs = (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
                                   map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs)"
    unfolding constraints_to_pairs_def leq_cs_def lt_cs_def
    by metis
  hence leq_pairs: "leq_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs"
     and lt_pairs: "lt_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs"
    using assms(1) by auto
  then obtain c where "c \<in> set cs" and "l = lec_poly c"
    using assms(2) unfolding leq_pairs lt_pairs leq_cs_def lt_cs_def by force
  moreover have "constraints_max_var cs = Max (set (0 # map lec_max_var cs))"
    unfolding constraints_max_var_def by presburger
  ultimately show ?thesis by simp
qed

definition mats_vecs_of_constraints ::
  "rat le_constraint list \<Rightarrow> rat mat \<times> rat vec \<times> rat mat \<times> rat vec" where
"mats_vecs_of_constraints cs = (
  let n = 1 + constraints_max_var cs in
  let (leq_pairs, lt_pairs) = constraints_to_pairs cs in
  let leq_polys = map fst leq_pairs in
  let leq_rows = map (\<lambda> l. vec_of_poly l n) leq_polys in
  let leq_bounds = map snd leq_pairs in
  let lt_polys = map fst lt_pairs in
  let lt_rows = map (\<lambda> l. vec_of_poly l n) lt_polys in
  let lt_bounds = map snd lt_pairs in
  (mat_of_rows n leq_rows, vec_of_list leq_bounds,
   mat_of_rows n lt_rows, vec_of_list lt_bounds))"

lemma satisfies_le_constraint_depend:
  assumes "n > lec_max_var c"
  and "\<forall> x < n. v0 x = v1 x"
shows "v0 \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v1 \<Turnstile>\<^sub>l\<^sub>e c"
proof -
  from assms have "\<forall> x \<in> vars (lec_poly c). v0 x = v1 x"
    using max_var_max[of _ "lec_poly c"] by force
  hence "((lec_poly c) \<lbrace> v0 \<rbrace>) = ((lec_poly c) \<lbrace> v1 \<rbrace>)"
    using valuate_depend by blast
  thus ?thesis
    using satisfiable_le_constraint.simps le_constraint.collapse by metis
qed

lemma satisfies_constraints_depend:
  assumes "n > constraints_max_var cs"
  and "\<forall> x < n. v0 x = v1 x"
shows "(\<forall> c \<in> set cs. v0 \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> (\<forall> c \<in> set cs. v1 \<Turnstile>\<^sub>l\<^sub>e c)"
proof -
  have "constraints_max_var cs =  Max (set (0 # map lec_max_var cs))"
    unfolding constraints_max_var_def by presburger
  hence "\<And> c. c \<in> set cs \<Longrightarrow> lec_max_var c < n" using assms(1) by fastforce
  thus ?thesis using satisfies_le_constraint_depend[OF _ assms(2)] by blast
qed

lemma mats_vecs_of_constraints:
  assumes "mats_vecs_of_constraints cs = (A, b, A', b')"
   and n: "n = 1 + constraints_max_var cs"
  shows "\<exists> nr nr'. A \<in> carrier_mat nr n \<and>
                   b \<in> carrier_vec nr \<and>
                   A' \<in> carrier_mat nr' n \<and>
                   b' \<in> carrier_vec nr'" (is ?DIM)
   and "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> (A *\<^sub>v (vec n v) \<le> b \<and> A' *\<^sub>v (vec n v) <\<^sub>v b')"
     (is "?L \<longleftrightarrow> ?R")
   and "integral_constraints cs \<Longrightarrow> A \<in> \<int>\<^sub>m \<and> b \<in> \<int>\<^sub>v \<and> A' \<in> \<int>\<^sub>m \<and> b' \<in> \<int>\<^sub>v"
      (is "?INT0 \<Longrightarrow> ?INT1")
   and "A \<in> Bounded_mat (max_coeff_constraints cs) \<and>
        b \<in> Bounded_vec (max_coeff_constraints cs) \<and>
        A' \<in> Bounded_mat (max_coeff_constraints cs) \<and>
        b' \<in> Bounded_vec (max_coeff_constraints cs)" (is ?BNDS)
proof -
  obtain leq_pairs lt_pairs leq_polys lt_polys
         leq_rows leq_bounds lt_rows lt_bounds
         where
          pairs: "constraints_to_pairs cs = (leq_pairs, lt_pairs)" and
          leq_polys: "leq_polys = map fst leq_pairs" and
          leq_rows: "leq_rows = map (\<lambda> l. vec_of_poly l n) leq_polys" and
          leq_bounds: "leq_bounds = map snd leq_pairs" and
          lt_polys: "lt_polys = map fst lt_pairs" and
          lt_rows: "lt_rows = map (\<lambda> l. vec_of_poly l n) lt_polys" and
          lt_bounds: "lt_bounds = map snd lt_pairs" and
          res: "mats_vecs_of_constraints cs = (mat_of_rows n leq_rows,
                                               vec_of_list leq_bounds,
                                               mat_of_rows n lt_rows,
                                               vec_of_list lt_bounds)"
    unfolding mats_vecs_of_constraints_def
      apply(cases "constraints_to_pairs cs")
      apply(simp add: n del: vec_of_list_map)
      done
    from res assms(1) have A: "A = mat_of_rows n leq_rows" and
                           b: "b = vec_of_list leq_bounds" and
                           A': "A' = mat_of_rows n lt_rows" and
                           b': "b' = vec_of_list lt_bounds" by auto
  have A_carrier: "A \<in> carrier_mat (length leq_pairs) n" and
       b_carrier: "b \<in> carrier_vec (length leq_pairs)"
    using A b leq_rows leq_polys leq_bounds by (fastforce, fastforce)
  have A'_carrier: "A' \<in> carrier_mat (length lt_pairs) n" and
       b'_carrier: "b' \<in> carrier_vec (length lt_pairs)"
    using A' b' lt_rows lt_polys lt_bounds by (fastforce, fastforce)
  show ?DIM using A_carrier b_carrier A'_carrier b'_carrier by blast

  show "?L \<longleftrightarrow> ?R" proof(standard)
    assume v: ?L

    have "A *\<^sub>v (vec n v) \<le> b"
    proof (rule lesseq_vecI[OF _ b_carrier], insert A_carrier, simp)
      fix i
      assume i: "i < length leq_pairs"
      hence i': "i < dim_row A" using A leq_rows leq_polys by fastforce
      have pairs_i: "(leq_polys ! i, leq_bounds ! i) \<in> set leq_pairs"
        using i leq_polys leq_bounds by fastforce
      have max_var: "max_var (leq_polys ! i) < n" using n leq_polys
        using constraints_max_var_to_pairs[OF pairs, of "leq_polys ! i" "leq_bounds ! i"]
              pairs_i by force

      from v have "(\<forall> (l, x) \<in> set leq_pairs. (l \<lbrace> v \<rbrace>) \<le> x)"
        using constraints_to_pairs(1)[OF pairs] by blast
      hence "(leq_polys ! i) \<lbrace> v \<rbrace> \<le> leq_bounds ! i"
        using i leq_polys leq_bounds by auto
      also have "valuate (leq_polys ! i) v =
                 valuate (leq_polys ! i) (val_of_vec (vec n v))"
        unfolding val_of_vec_def
        apply(rule valuate_depend)
        apply(insert max_var max_var_max, force)
        done
      also have "\<dots> = vec_of_poly (leq_polys ! i) n \<bullet> (vec n v)"
        using dot_vec_of_poly[of "vec n v" n, OF _ max_var] by fastforce
      also have "vec_of_poly (leq_polys ! i) n = row A i"
        unfolding A leq_rows leq_polys
        using i length_map[of fst leq_pairs] by fastforce
      also have "row A i \<bullet> vec n v = (A *\<^sub>v (vec n v)) $ i"
        using index_mult_mat_vec[OF i'] by presburger
      also have "leq_bounds ! i = b $ i" unfolding b using i leq_bounds by fastforce
      finally show "(A *\<^sub>v (vec n v)) $ i \<le> b $ i" by blast
    qed

    moreover

    have "A' *\<^sub>v (vec n v) <\<^sub>v b'"
    proof (rule less_vecI[OF _ b'_carrier], insert A'_carrier, simp)
      fix i
      assume i: "i < length lt_pairs"
      hence i': "i < dim_row A'" using A' lt_rows lt_polys by force
      have pairs_i: "(lt_polys ! i, lt_bounds ! i) \<in> set lt_pairs"
        using i lt_polys lt_bounds by fastforce
      have max_var: "max_var (lt_polys ! i) < n" using n leq_polys
        using constraints_max_var_to_pairs[OF pairs] pairs_i by fastforce

      from v have "(\<forall> (l, x) \<in> set lt_pairs. (l \<lbrace> v \<rbrace>) < x)"
        using constraints_to_pairs(1)[OF pairs] by algebra
      hence "(lt_polys ! i) \<lbrace> v \<rbrace> < lt_bounds ! i"
        using i lt_polys lt_bounds by auto
      also have "valuate (lt_polys ! i) v =
                 valuate (lt_polys ! i) (val_of_vec (vec n v))"
        unfolding val_of_vec_def
        apply(rule valuate_depend)
        apply(insert max_var max_var_max, force)
        done
      also have "\<dots> = vec_of_poly (lt_polys ! i) n \<bullet> (vec n v)"
        using dot_vec_of_poly[of "vec n v" n, OF _ max_var] by fastforce
      also have "vec_of_poly (lt_polys ! i) n = row A' i"
        unfolding A' lt_rows lt_polys
        using i length_map[of fst lt_pairs] by fastforce
      also have "row A' i \<bullet> vec n v = (A' *\<^sub>v (vec n v)) $ i"
        using index_mult_mat_vec[OF i'] by presburger
      also have "lt_bounds ! i = b' $ i" unfolding b' using i lt_bounds by fastforce
      finally show "(A' *\<^sub>v (vec n v)) $ i < b' $ i" by blast
    qed
    ultimately show ?R by fastforce

  next
    assume R: ?R
    define x where "x = vec n v"
    have xn: "x \<in> carrier_vec n" and x0: "A *\<^sub>v x \<le> b" and x1: "A' *\<^sub>v x <\<^sub>v b'"
      using R unfolding x_def by auto
  {
    fix l t
    assume lt0: "(l, t) \<in> set leq_pairs"
    then obtain i where i: "i < length leq_pairs" and lt: "(l, t) = leq_pairs ! i"
      by (metis in_set_conv_nth)
    have max_var: "max_var l < n"
      using constraints_max_var_to_pairs[OF pairs, of l t] n lt0 by fastforce

    have "(A *\<^sub>v x) $ i \<le> b $ i" by (rule lesseq_vecD[OF b_carrier x0 i])
    also have "(A *\<^sub>v x) $ i = row A i \<bullet> x"
      by (rule index_mult_mat_vec, simp add: i A leq_rows leq_polys)
    also have "row A i = vec_of_poly l n"
      unfolding A leq_rows leq_polys
      using i length_map[of fst leq_pairs] lt fst_conv[of l t] by simp
    also have "vec_of_poly l n \<bullet> x = (l \<lbrace> val_of_vec x \<rbrace>)"
      by (rule dot_vec_of_poly[OF xn max_var])
    also have "b $ i = t" unfolding b leq_bounds using i lt
      using snd_conv[of l t] vec_of_list_index by simp
    finally have "(l \<lbrace> val_of_vec x \<rbrace>) \<le> t" by blast
  } moreover {
    fix l t
    assume lt0: "(l, t) \<in> set lt_pairs"
    then obtain i where i: "i < length lt_pairs" and lt: "(l, t) = lt_pairs ! i"
      by (metis in_set_conv_nth)
    have max_var: "max_var l < n"
      using constraints_max_var_to_pairs[OF pairs, of l t] n lt0 by fastforce

    have "(A' *\<^sub>v x) $ i < b' $ i"
      by (rule less_vecD[OF x1 b'_carrier i])
    also have "(A' *\<^sub>v x) $ i = row A' i \<bullet> x"
      by (rule index_mult_mat_vec, simp add: i A' lt_rows lt_polys)
    also have "row A' i = vec_of_poly l n"
      unfolding A' lt_rows lt_polys
      using i length_map[of fst lt_pairs] lt fst_conv[of l t] by simp
    also have "vec_of_poly l n \<bullet> x = (l \<lbrace> val_of_vec x \<rbrace>)"
      by (rule dot_vec_of_poly[OF xn max_var])
    also have "b' $ i = t" unfolding b' lt_bounds using i lt
      using snd_conv[of l t] vec_of_list_index by simp
    finally have "(l \<lbrace> val_of_vec x \<rbrace>) < t" by blast
  }
  ultimately have
    "(\<forall>(l, t)\<in>set leq_pairs. (l \<lbrace> val_of_vec x \<rbrace>) \<le> t) \<and>
     (\<forall>(l, t)\<in>set lt_pairs. (l \<lbrace> val_of_vec x \<rbrace>) < t)" by blast
  hence "\<forall> c \<in> set cs. val_of_vec x \<Turnstile>\<^sub>l\<^sub>e c"
    using constraints_to_pairs(1)[OF pairs] by presburger
  thus ?L  using satisfies_constraints_depend[of cs n v "val_of_vec x"] n
    unfolding x_def val_of_vec_def by fastforce
  qed

  have leq_rows_carrier: "set leq_rows \<subseteq> carrier_vec n" unfolding leq_rows by auto
  have lt_rows_carrier: "set lt_rows \<subseteq> carrier_vec n" unfolding lt_rows by auto

  let ?Bnd = "max_coeff_constraints cs"
  from constraints_to_pairs(3)[OF pairs]
  have polys: "\<forall> l \<in> set leq_polys \<union> set lt_polys. \<forall> i. \<bar>coeff l i\<bar> \<le> ?Bnd"
   and bounds: "\<forall> c \<in> set leq_bounds \<union> set lt_bounds. \<bar>c\<bar> \<le> ?Bnd"
    unfolding leq_polys lt_polys leq_bounds lt_bounds by (force, force)
  from polys have "set leq_rows \<union> set lt_rows \<subseteq> Bounded_vec ?Bnd"
    unfolding leq_rows lt_rows
    using vec_of_poly_bound[of _ _ n] by auto
  hence "A \<in> Bounded_mat ?Bnd \<and> A' \<in> Bounded_mat ?Bnd"
    using Bounded_vec_rows_Bounded_mat[of _ ?Bnd]
          rows_mat_of_rows[OF leq_rows_carrier]
          rows_mat_of_rows[OF lt_rows_carrier]
    unfolding A A' by fastforce
  moreover have "b \<in> Bounded_vec ?Bnd \<and> b' \<in> Bounded_vec ?Bnd"
    by(auto simp: b b' Bounded_vec_def bounds)
  ultimately show ?BNDS by blast

  assume int0: ?INT0
  from constraints_to_pairs(2)[OF pairs int0]
  have polys: "\<forall> l \<in> set leq_polys \<union> set lt_polys. integral_linear_poly l"
   and bounds: "set leq_bounds \<union> set lt_bounds \<subseteq> \<int>"
    unfolding leq_polys lt_polys leq_bounds lt_bounds
    by (force, force)

  from polys have "set leq_rows \<union> set lt_rows \<subseteq> \<int>\<^sub>v"
    unfolding leq_rows lt_rows using integral_vec_of_poly[of _ n] by auto
  hence "A \<in> \<int>\<^sub>m \<and> A' \<in> \<int>\<^sub>m" unfolding A A'
    using Ints_vec_rows_Ints_mat rows_mat_of_rows[OF leq_rows_carrier]
                                 rows_mat_of_rows[OF lt_rows_carrier] by fastforce
  moreover have "b \<in> \<int>\<^sub>v \<and> b' \<in> \<int>\<^sub>v" unfolding b b' Ints_vec_def
    using bounds by fastforce
  ultimately show ?INT1 by blast
qed

primrec mul_constraint where
"mul_constraint x (Le_Constraint r l c) = Le_Constraint r (x *R l) (x * c)"

lemma mul_constraint:
  assumes "x > 0"
  shows "v \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v \<Turnstile>\<^sub>l\<^sub>e mul_constraint x c"
proof -
  from le_constraint.collapse[of c] obtain r l y where
    decomp: "c = Le_Constraint r l y"
    by metis
  have "(l \<lbrace> v \<rbrace>) < y \<longleftrightarrow> ((x *R l) \<lbrace> v \<rbrace>) < x * y"
    using mult_less_cancel_left_pos[OF assms] valuate_scaleRat[of x l v]
    by force
  moreover have "(l \<lbrace> v \<rbrace>) \<le> y \<longleftrightarrow> ((x *R l) \<lbrace> v \<rbrace>) \<le> x * y"
    using mult_le_cancel_left_pos[OF assms] valuate_scaleRat[of x l v]
    by force
  ultimately show ?thesis unfolding decomp
    by (cases r, simp_all)
qed

primrec common_denominator where
"common_denominator (Le_Constraint _ l c) =
  (let coeffs_list = map (coeff l) (vars_list l) in
   let denominators = map (snd \<circ> quotient_of) (c # coeffs_list) in
   lcm_list denominators)"

lemma mult_denom_int:
  assumes "quotient_of x = (n, d)"
  and "d dvd d'"
  shows "of_int d' * x \<in> \<int>"
proof -
  from assms(2) obtain k where d': "d' = k * d" unfolding dvd_def by fastforce
  have "d \<noteq> 0" using assms quotient_of_nonzero(2)[of x] by auto
  hence "of_int n = of_int d * x" using quotient_of_div[OF assms(1)] by simp
  hence "of_int d * x \<in> \<int>" using Ints_of_int by metis
  hence "of_int k * (of_int d * x) \<in> \<int>" by simp
  hence "(of_int k * of_int d) * x \<in> \<int>" using mult.assoc by metis
  thus ?thesis unfolding d' by simp
qed

lemma common_denominator:
  shows "common_denominator c > 0" (is ?pos)
   and "of_int (common_denominator c) * lec_const c \<in> \<int>" (is ?const)
   and "of_int (common_denominator c) * (coeff (lec_poly c) i) \<in> \<int>"
     (is ?coeff)
proof -
  from le_constraint.collapse[of c] obtain r l x where
    decomp: "c = Le_Constraint r l x"
    by metis
  define coeffs_list where "coeffs_list = map (coeff l) (vars_list l)"
  define denominators where "denominators = map (snd \<circ> quotient_of) (x # coeffs_list)"
  have res: "common_denominator c = lcm_list denominators"
    unfolding decomp denominators_def coeffs_list_def common_denominator.simps
    by presburger

  have "0 \<notin> set denominators"
    unfolding denominators_def using quotient_of_nonzero(2) by fastforce
  thus ?pos using res list_lcm_pos(3) by presburger

  have "snd (quotient_of x) dvd common_denominator c"
    using list_lcm unfolding res denominators_def by auto
  thus ?const
    using mult_denom_int[OF surjective_pairing]
    unfolding decomp le_constraint.sel(3) by blast

  show ?coeff
  proof cases
    assume "i \<in> vars l"
    hence "coeff l i \<in> set coeffs_list"
      unfolding coeffs_list_def using set_vars_list by auto
    hence "snd (quotient_of (coeff l i)) dvd common_denominator c"
      using list_lcm unfolding res denominators_def by auto
    thus ?coeff
    using mult_denom_int[OF surjective_pairing]
    unfolding decomp le_constraint.sel(2) by blast
  next
    assume "i \<notin> vars l"
    hence "coeff l i = 0" using coeff_zero by fast
    thus ?coeff unfolding decomp le_constraint.sel(2) by auto
  qed
qed

definition
"constraint_to_ints c = mul_constraint (rat_of_int (common_denominator c)) c"

lemma constraint_to_ints: fixes c :: "rat le_constraint"
  shows "v \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v \<Turnstile>\<^sub>l\<^sub>e constraint_to_ints c" (is ?R0)
  and "integral_constraint (constraint_to_ints c)" (is ?R1)
proof -
  show ?R0
    using common_denominator(1) mul_constraint
    unfolding constraint_to_ints_def by presburger

  let ?x = "of_int (common_denominator c)"
  have "c = Le_Constraint (lec_rel c) (lec_poly c) (lec_const c)"
    using le_constraint.collapse by auto
  hence "mul_constraint ?x c =
         Le_Constraint (lec_rel c) (?x *R lec_poly c) (?x * lec_const c)"
    using mul_constraint.simps by metis
  hence "lec_poly (mul_constraint ?x c) = ?x *R lec_poly c"
   and "lec_const (mul_constraint ?x c) = ?x * lec_const c" by auto
  thus ?R1 using common_denominator(2-3) unfolding integral_linear_poly_def
unfolding constraint_to_ints_def
    by simp
qed

lemma equal_leccoeffs_impl_equal_leccoeffsconstrainttoints:
  assumes "lec_coeffs lec1 = lec_coeffs lec2"
  shows "lec_coeffs (constraint_to_ints lec1) = lec_coeffs (constraint_to_ints lec2)"
proof -
  have "\<And>lec. set ((lec_const lec)
      # (map (coeff (lec_poly lec)) (vars_list (lec_poly lec)))) = lec_coeffs lec"
    using lec_coeffs.simps
    by (metis Set.insert_def list.set(2) set_map singleton_conv Setcompr_eq_image
        le_constraint.collapse set_vars_list)
  hence cd_eq: "common_denominator lec1 = common_denominator lec2"
    unfolding common_denominator_def using assms
    by (metis (mono_tags, lifting) le_constraint.collapse le_constraint.rec set_map)
  have "\<And>x c. lec_coeffs (mul_constraint x c) = (\<lambda>y. x * y) ` (lec_coeffs c)"
  proof (goal_cases)
    case (1 x c)
    then show ?case
    proof (cases "x = 0")
      case True
      then show ?thesis unfolding lec_coeffs_def mul_constraint_def
        by (smt Collect_empty_eq Setcompr_eq_image Un_insert_left bot_set_def empty_iff
            image_cong image_constant_conv insert_not_empty le_constraint.exhaust
            le_constraint.rec mul_constraint.simps mult_zero_left
            rational_vector.scale_zero_left set_zero sup_bot.left_neutral vars_zero)
    next
      case False
      then show ?thesis
      proof -
        define r l cst where "r = lec_rel c" and "l = x *R lec_poly c"
          and "cst = x * (lec_const c)"
        have "lec_coeffs (Le_Constraint r l cst) = (\<lambda>y. x * y) ` (lec_coeffs c)"
          unfolding lec_coeffs_def r_def l_def cst_def
          by (smt Collect_cong Set.insert_def Setcompr_eq_image coeff_scaleRat
              image_insert le_constraint.collapse le_constraint.rec mem_Collect_eq
              singleton_conv vars_scaleRat False)
        thus ?thesis
          unfolding mul_constraint_def r_def l_def cst_def
          by (metis (no_types, lifting) le_constraint.collapse le_constraint.rec)
      qed
    qed
  qed
  thus ?thesis using cd_eq assms by (simp add: constraint_to_ints_def)
qed

lemma map_equal_leccoeffs_impl_equal_leccoeffsconstrainttoints:
  assumes "map lec_coeffs lecs1 = map lec_coeffs lecs2"
  shows "map lec_coeffs (map constraint_to_ints lecs1) =
    map lec_coeffs (map constraint_to_ints lecs2)"
proof -
  have "\<And>i. lec_coeffs (constraint_to_ints (lecs1 ! i)) =
    lec_coeffs (constraint_to_ints (lecs2 ! i))"
    using equal_leccoeffs_impl_equal_leccoeffsconstrainttoints assms length_map nth_map undef_vec
    by metis
  thus ?thesis
    by (metis (mono_tags, lifting) assms length_map nth_equalityI nth_map)
qed

lemma consttoints_preserves_vars:
  shows "vars (lec_poly (constraint_to_ints lec)) \<subseteq> vars (lec_poly lec)"
  unfolding constraint_to_ints_def mul_constraint_def
  by (metis (no_types, lifting) le_constraint.collapse le_constraint.inject
      le_constraint.rec vars_scaleRat1)


(* The following lemmas deal with the renaming of variables, which is needed in order
   to obtain bounds that depend on the number of variables, rather than on the largest
   index of any variable. *)
definition renvar_valuation :: "('a :: lrv valuation) \<Rightarrow> nat list \<Rightarrow> ('a :: lrv valuation)" where
  "renvar_valuation vl vrs = (\<lambda>i. if i < length vrs then vl (vrs ! i) else 0)"

definition renvar_index :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
"renvar_index i vrs = (if i\<in> set vrs then (index vrs i) else length vrs)"

definition renvar_index_set :: "nat set \<Rightarrow> nat list \<Rightarrow> nat set" where
  "renvar_index_set I vrs = (\<lambda>i. renvar_index i vrs) ` I"

lemma renvar_valuation_int:
  assumes "distinct vrs"
  shows "v i \<in> \<int> \<Longrightarrow> renvar_valuation v vrs (renvar_index i vrs) \<in> \<int>"
  unfolding renvar_valuation_def renvar_index_def by simp

lift_definition renvar_linearpoly :: "linear_poly \<Rightarrow> (nat list) \<Rightarrow> linear_poly" is
  "(\<lambda>p vrs. (\<lambda>i. if i < length vrs then p (vrs ! i) else 0))"
  by auto

lemma renvar_linearpoly_minus:
  shows "- renvar_linearpoly p vrs = renvar_linearpoly (-p) vrs"
proof -
  {
    fix v :: "var"
    define minp where "minp = -p"
    have "coeff (- renvar_linearpoly p vrs) v = - coeff (renvar_linearpoly p vrs) v"
      by simp
    also have "\<dots> = -(if v < length vrs then (coeff p (vrs ! v)) else 0)" by transfer auto
    also have "\<dots> = (if v < length vrs then (coeff minp (vrs ! v)) else 0)"
      unfolding minp_def by simp
    also have "\<dots> = coeff (renvar_linearpoly minp vrs) v" by transfer auto
    also have "\<dots> = coeff (renvar_linearpoly (-p) vrs) v" unfolding minp_def by simp
    finally have "coeff (- renvar_linearpoly p vrs) v = coeff (renvar_linearpoly (-p) vrs) v"
      by simp
  }
  thus ?thesis using poly_eqI by simp
qed

lemma renvar_linearpoly_diff:
  shows "renvar_linearpoly p1 vrs - renvar_linearpoly p2 vrs =
         renvar_linearpoly (p1 - p2) vrs"
proof -
  {
    fix v :: "var"
    define p1p2 where "p1p2 = p1 - p2"
    have "coeff (renvar_linearpoly p1 vrs - renvar_linearpoly p2 vrs) v
      = coeff (renvar_linearpoly p1 vrs) v - coeff (renvar_linearpoly p2 vrs) v"
      by simp
    also have "coeff (renvar_linearpoly p1 vrs) v =
              (if v < length vrs then (coeff p1 (vrs ! v)) else 0)" by transfer auto
    also have "coeff (renvar_linearpoly p2 vrs) v =
              (if v < length vrs then (coeff p2 (vrs ! v)) else 0)" by transfer auto
    also have "(if v < length vrs then (coeff p1 (vrs ! v)) else 0) -
               (if v < length vrs then (coeff p2 (vrs ! v)) else 0) =
               (if v < length vrs then (coeff p1p2 (vrs ! v)) else 0)"
      unfolding p1p2_def by simp
    also have "\<dots> = coeff (renvar_linearpoly p1p2 vrs) v" by (transfer, auto)
    finally have "coeff (renvar_linearpoly p1 vrs - renvar_linearpoly p2 vrs) v =
                  coeff (renvar_linearpoly (p1-p2) vrs) v" unfolding p1p2_def by simp
  } note coeffid = this
  thus ?thesis using poly_eq_iff coeffid by simp
qed

lemma varlist_renvar_linearpoly:
  assumes "vars p \<subseteq> set vrs" and "distinct vrs"
  shows "Max ({0} \<union> vars (renvar_linearpoly p vrs)) \<le> length vrs"
by (transfer,auto)

lemma renvar_linearpoly_var_range:
  shows "vars (renvar_linearpoly lp vrs) \<subseteq> {0..(length vrs -1)}"
  by (transfer, auto)

lemma renvar_linearpoly_sat:
  assumes "vars p \<subseteq> set vrs" and "distinct vrs"
  shows "(renvar_linearpoly p vrs)\<lbrace>renvar_valuation v vrs\<rbrace> = p\<lbrace>v\<rbrace>"
  unfolding renvar_valuation_def
  using assms
proof (transfer, simp, goal_cases)
  case (1 p vrs vl)
  show ?case
  proof -
    have seq: "{v. (v < length vrs \<longrightarrow> p (vrs ! v) \<noteq> 0) \<and> v < length vrs} =
          {v. v < length vrs \<and> p(vrs ! v) \<noteq> 0}" by blast
    let ?A = "{v. v < length vrs \<and> p(vrs ! v) \<noteq> 0}"
    let ?fct = "(\<lambda>x. vrs ! x)"
    have injo: "inj_on ?fct ?A" using 1 inj_on_nth by fastforce
    have seq2: "?fct ` ?A = {v. p v \<noteq> 0}"
    proof
      {
        fix x
        assume pxz: "x \<in> {v. p v \<noteq> 0}"
        hence "\<exists>i < length vrs. x = vrs ! i" by (metis 1(2) in_set_conv_nth subsetD)
        then obtain i where "x = vrs ! i" and "i < length vrs" by auto
        hence "x \<in> ?fct ` ?A" using pxz by simp
      }
      thus "{v. p v \<noteq> 0} \<subseteq> (!) vrs ` {v. v < length vrs \<and> p (vrs ! v) \<noteq> 0}" by blast
    qed auto
    show ?thesis
      by (metis (mono_tags, lifting) injo sum.reindex_cong seq2 seq)
  qed
qed

lemma renvar_linearpoly_coeff:
  assumes "vars p \<subseteq> set vrs" and "distinct vrs" and "i < length vrs"
  shows "coeff (renvar_linearpoly p vrs) i = coeff p (vrs ! i)"
  using assms
  by (transfer, simp)

fun renvar_leconstraint :: "rat le_constraint \<Rightarrow> nat list \<Rightarrow> rat le_constraint" where
  "renvar_leconstraint (Leqc l c) vrs = (Leqc (renvar_linearpoly l vrs) c)"
| "renvar_leconstraint (Ltc l c) vrs = (Ltc (renvar_linearpoly l vrs) c)"

lemma renvar_leconstraint_var_range:
  assumes "vars (lec_poly c) \<subseteq> set vrs" and "distinct vrs"
  shows "Max ({0} \<union> vars (lec_poly (renvar_leconstraint c vrs))) \<le> length vrs"
  by (smt le_constraint.collapse le_constraint.sel(2)
      le_rel.exhaust renvar_leconstraint.simps assms varlist_renvar_linearpoly)

lemma renvar_leconstraint_sat:
  assumes "vars (lec_poly c) \<subseteq> set vrs" and "distinct vrs"
  shows "(v :: rat valuation) \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow>
         (renvar_valuation v vrs) \<Turnstile>\<^sub>l\<^sub>e (renvar_leconstraint c vrs)"
  using renvar_linearpoly_sat[OF assms(1) assms(2)]
  by (metis (full_types) le_constraint.collapse le_rel.exhaust
      renvar_leconstraint.simps(1) renvar_leconstraint.simps(2)
      satisfiable_le_constraint.simps)

lemma lecpoly_renvar_commute:
  shows "lec_poly (renvar_leconstraint c vrs) = renvar_linearpoly (lec_poly c) vrs"
  by (metis (full_types) le_constraint.collapse le_constraint.sel(2) le_rel.exhaust
      renvar_leconstraint.simps)

lemma lecconst_renvar_commute:
  shows "lec_const lec = lec_const (renvar_leconstraint lec vrs)"
  by (metis le_constraint.sel(3) renvar_leconstraint.elims)

lemma leccoeffs_renvar_invariant:
  assumes "distinct vrs" and "vars (lec_poly lec) \<subseteq> set vrs"
  shows "lec_coeffs lec = lec_coeffs (renvar_leconstraint lec vrs)"
proof
  define renlec where "renlec = renvar_leconstraint lec vrs"
  {
    fix coef
    assume coef: "coef \<in> lec_coeffs lec"
    have "coef \<in> lec_coeffs (renvar_leconstraint lec vrs)"
    proof (cases "coef = lec_const lec")
      case True
      then show ?thesis using lecconst_renvar_commute[of lec vrs] lecconst_in_leccoeffs by simp
    next
      case False
      then show ?thesis
      proof -
        obtain vr where vr: "vr \<in> vars (lec_poly lec)" and
          cf: "coef = coeff (lec_poly lec) vr"
          by (smt False Un_insert_left coef insert_iff le_constraint.collapse
              lec_coeffs.simps mem_Collect_eq sup_bot.left_neutral)
        hence "coef = coeff (lec_poly renlec) (index vrs vr)"
          unfolding renlec_def using renvar_linearpoly_coeff[OF assms(2) assms(1)]
            lecpoly_renvar_commute assms(2) by auto
        thus ?thesis unfolding lec_coeffs_def renlec_def
          by (metis (mono_tags, lifting) UnI2 cf coeff_zero le_constraint.collapse
              le_constraint.rec mem_Collect_eq renlec_def vr)
      qed
    qed
  }
  thus "lec_coeffs lec \<subseteq> lec_coeffs (renvar_leconstraint lec vrs)" by auto
  {
    fix coef
    assume coef: "coef \<in> lec_coeffs renlec"
    have "coef \<in> lec_coeffs lec"
    proof (cases "coef = lec_const renlec")
      case True
      then show ?thesis using lecconst_renvar_commute[of lec vrs, symmetric]
          lecconst_in_leccoeffs unfolding renlec_def by simp
    next
      case False
      then show ?thesis
      proof -
        obtain vr where vr: "vr \<in> vars (lec_poly renlec)" and
          cf: "coef = coeff (lec_poly renlec) vr"
          by (smt False Un_insert_left coef insert_iff
              le_constraint.collapse lec_coeffs.simps mem_Collect_eq sup_bot.left_neutral)
        have "vrs \<noteq> []" using vr
          by (metis assms(2) coeff_zero diff_self in_set_simps(3) lecpoly_renvar_commute
              renvar_linearpoly_diff renlec_def subsetI subset_antisym zero_coeff_zero)
        hence "vr < length vrs"
          using One_nat_def atLeastAtMost_iff diff_Suc_less length_greater_0_conv
            lecpoly_renvar_commute renvar_linearpoly_var_range less_le_trans not_less
          by (metis (no_types, lifting) in_mono renlec_def vr)
        hence "coef = coeff (lec_poly lec) (vrs ! vr)"
          using cf unfolding renlec_def
          by (simp add: assms lecpoly_renvar_commute renvar_linearpoly_coeff)
        thus ?thesis unfolding lec_coeffs_def
          by (metis (mono_tags, lifting) UnI2 cf coeff_zero le_constraint.collapse
              le_constraint.rec mem_Collect_eq vr)
      qed
    qed
  }
  thus "lec_coeffs (renvar_leconstraint lec vrs) \<subseteq> lec_coeffs lec" unfolding renlec_def
    by auto
qed

primrec renvar_constraint :: "constraint \<Rightarrow> nat list \<Rightarrow> constraint" where
  "renvar_constraint (LEQ l x) vrs = (LEQ (renvar_linearpoly l vrs) x)"
| "renvar_constraint (GEQ l x) vrs = (GEQ (renvar_linearpoly l vrs) x)"
| "renvar_constraint (LT l x) vrs = (LT (renvar_linearpoly l vrs) x)"
| "renvar_constraint (GT l x) vrs = (GT (renvar_linearpoly l vrs) x)"
| "renvar_constraint (EQ l x) vrs = (EQ (renvar_linearpoly l vrs) x)"

lemma constrtoleconstr_renvar_commute:
  shows "set (constraint_to_le_constraint (renvar_constraint c vrs)) =
        (\<lambda>x. renvar_leconstraint x vrs) ` set (constraint_to_le_constraint c)"
  by (cases c, auto simp: renvar_linearpoly_diff renvar_linearpoly_minus)

lemma constrtoleconstr_renvar_commute_list:
  shows
    "constraint_to_le_constraint (renvar_constraint c vrs) =
       map (\<lambda>x. renvar_leconstraint x vrs) (constraint_to_le_constraint c)"
  by (cases c, auto simp: renvar_linearpoly_diff renvar_linearpoly_minus)

lemma renvar_constraint_var_range:
  assumes "set (var_list [c]) \<subseteq> set vrs" and "distinct vrs"
  shows "Max ({0} \<union> set (var_list [renvar_constraint c vrs])) \<le> length vrs"
  using var_list_def constrtoleconstr_renvar_commute set_vars_list assms
    renvar_leconstraint_var_range finite_vars by fastforce

lemma renvar_constraint_sat:
  assumes "set (var_list [c]) \<subseteq> set vrs" and "distinct vrs"
  shows "(v :: rat valuation) \<Turnstile>\<^sub>c c \<longleftrightarrow>
    (renvar_valuation v vrs) \<Turnstile>\<^sub>c renvar_constraint c vrs"
proof -
  have "\<forall>p \<in> set (map lec_poly (constraint_to_le_constraint c)). vars p \<subseteq> set vrs"
    using assms set_vars_list unfolding var_list_def by auto
  thus ?thesis using constraint_to_le_constraint renvar_leconstraint_sat assms
    constraint_to_le_constraint constrtoleconstr_renvar_commute by fastforce
qed

definition renvar_constraintlist where
  "renvar_constraintlist cs vrs = map (\<lambda>x. renvar_constraint x vrs) cs"

lemma renvar_constraintlist_var_range:
  assumes "set (var_list cs) \<subseteq> set vrs" and "distinct vrs"
  shows "Max ({0} \<union> set (var_list (renvar_constraintlist cs vrs))) \<le> length vrs"
  using var_list_def renvar_constraintlist_def renvar_constraint_def assms
    renvar_constraint_var_range Max_ge by fastforce

lemma renvar_constraintlist_sat:
  assumes "set (var_list cs) \<subseteq> set vrs" and "distinct vrs"
  shows "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow>
    (renvar_valuation v vrs) \<Turnstile>\<^sub>c\<^sub>s set (renvar_constraintlist cs vrs)"
proof -
  have "\<And>c. c \<in> set cs \<Longrightarrow>
    v \<Turnstile>\<^sub>c c \<longleftrightarrow> (renvar_valuation v vrs) \<Turnstile>\<^sub>c renvar_constraint c vrs"
    using var_list_def assms renvar_constraint_sat by fastforce
  thus ?thesis by (simp add: renvar_constraintlist_def)
qed

lemma renvar_constraintlist_sat':
  shows "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (renvar_valuation v (var_list cs)) \<Turnstile>\<^sub>c\<^sub>s
        set (renvar_constraintlist cs (var_list cs))"
   using renvar_constraintlist_sat unfolding var_list_def by simp

lemma leccoeffs_normalize_renvar_invariant:
  assumes "set (var_list cs) \<subseteq> set vrs" and "distinct vrs"
  shows "(map lec_coeffs (normalize cs)) =
    (map lec_coeffs (normalize (renvar_constraintlist cs vrs)))"
proof -
  have "normalize (renvar_constraintlist cs vrs) =
    (map (\<lambda>x. renvar_leconstraint x vrs) (normalize cs))"
    unfolding normalize_def renvar_constraintlist_def
    by (smt length_map map_nth_eq_conv renvar_constraintlist_def map_concat
        constrtoleconstr_renvar_commute_list)
  thus ?thesis
    using leccoeffs_renvar_invariant[OF assms(2)] assms(1) constrtoleconstr_preserves_vars
    by fastforce
qed

lemma maxcoeffconstraints_renvar_invariant:
  shows "(let le_cs = normalize cs;
    le_cs' = map constraint_to_ints le_cs in max_coeff_constraints le_cs') =
    (let le_cs = normalize (renvar_constraintlist cs (var_list cs));
    le_cs' = map constraint_to_ints le_cs in max_coeff_constraints le_cs')" (is "?A = ?B")
  using map_equal_leccoeffs_impl_equal_leccoeffsconstrainttoints varlist_distinct
    leccoeffs_normalize_renvar_invariant equal_mapleccoeffs_impl_equal_maxcoeff(2)
  by (meson order_refl)

definition truncate_val where
  "truncate_val v maxvr = (\<lambda>i. if i < maxvr then v i else 0)"

lemma truncated_valuation_linearpoly:
  assumes "vars p \<subseteq> set vrs" and "distinct vrs"
  shows "(renvar_linearpoly p vrs)\<lbrace>v\<rbrace> =
    (renvar_linearpoly p vrs)\<lbrace>truncate_val v (length vrs)\<rbrace>"
  unfolding truncate_val_def
  by(transfer, auto)

lemma truncated_valuation_leconstraint:
  assumes "vars (lec_poly c) \<subseteq> set vrs" and "distinct vrs"
  shows "v \<Turnstile>\<^sub>l\<^sub>e (renvar_leconstraint c vrs) \<longleftrightarrow>
    (truncate_val v (length vrs)) \<Turnstile>\<^sub>l\<^sub>e (renvar_leconstraint c vrs)"
  by (metis le_constraint.sel(2) renvar_leconstraint.elims le_constraint.collapse
      satisfiable_le_constraint.simps truncated_valuation_linearpoly assms)

lemma truncated_valuation_constraint:
  assumes "set (var_list [c]) \<subseteq> set vrs" and "distinct vrs"
  shows "(v :: rat valuation) \<Turnstile>\<^sub>c (renvar_constraint c vrs) \<longleftrightarrow>
    (truncate_val v (length vrs)) \<Turnstile>\<^sub>c (renvar_constraint c vrs)"
  using constrtoleconstr_renvar_commute constraint_to_le_constraint set_vars_list
    truncated_valuation_leconstraint assms var_list_def by fastforce

lemma renvar_valuation_indexset_sat:
  assumes "distinct vrs" and "set (var_list cs) \<subseteq> set vrs"
    and "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (renvar_constraintlist cs vrs), (renvar_index_set I vrs))
         \<and> (\<forall>i\<in> (renvar_index_set I vrs). \<bar>v i\<bar> \<le> bnd)"
  shows "\<exists>v'. v' \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I) \<and> (\<forall>i\<in> I. \<bar>v' i\<bar> \<le> bnd)"
proof -
  define rencs where "rencs = renvar_constraintlist cs vrs"
  define trv where "trv = truncate_val v (length vrs)"
  have mod: "trv \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (renvar_constraintlist cs vrs), (renvar_index_set I vrs))"
  proof -
    {
      fix rc
      assume c: "rc \<in> set (rencs)"
      from this obtain c where c: "c \<in> set cs" and "rc = renvar_constraint c vrs"
        and "set (var_list [c]) \<subseteq> set vrs"
        using assms(2) unfolding rencs_def renvar_constraintlist_def var_list_def
        by auto
      hence "trv \<Turnstile>\<^sub>c rc \<longleftrightarrow> v \<Turnstile>\<^sub>c rc" unfolding trv_def
        using truncated_valuation_constraint assms(1) by blast
    }
    thus ?thesis using assms(3) rencs_def satisfies_mixed_constraints.simps
      unfolding trv_def renvar_index_set_def truncate_val_def by simp
  qed
  define v' where "v' = (\<lambda>vr. if vr \<in> set vrs then v (index vrs vr) else 0)"
  have rv: "trv = renvar_valuation v' vrs"
    unfolding trv_def v'_def renvar_valuation_def truncate_val_def
    using assms(1) index_nth_id nth_mem by metis
  hence "v' \<Turnstile>\<^sub>c\<^sub>s set cs" using assms(1,2) mod
    using renvar_constraintlist_sat satisfies_mixed_constraints.simps by blast
  moreover have "\<forall> i \<in> I. v' i \<in> \<int>" using assms(3)
    by (simp add: renvar_index_def renvar_index_set_def v'_def)
  ultimately have md: "v' \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I)" by simp
  have "\<And>i. i \<in> (set vrs) \<Longrightarrow>
    v' i = v (renvar_index i vrs)" unfolding v'_def renvar_index_def by simp
  hence "\<forall>i\<in> I. \<bar>v' i\<bar> \<le> bnd" using rv
    using assms(3) renvar_index_set_def v'_def by auto
  thus ?thesis using md by blast
qed
(* End of variable-renaming lemmas. *)

definition compute_bound_num_of_vars :: "constraint list \<Rightarrow> int" where
"compute_bound_num_of_vars cs =
  (let le_cs = normalize cs in
  let le_cs' = map constraint_to_ints le_cs in
  let max_coeff = max_coeff_constraints le_cs' in
  let n = 1 + length (var_list cs) in
  int (n + 1) * det_bound_hadamard n \<lfloor>max_coeff\<rfloor>)"

definition compute_bound :: "constraint list \<Rightarrow> int" where
"compute_bound cs =
   (let le_cs = normalize cs in
   let le_cs' = map constraint_to_ints le_cs in
   let max_coeff = max_coeff_constraints le_cs' in
   let n = 1 + constraints_max_var le_cs' in
   int (n + 1) * det_bound_hadamard n \<lfloor>max_coeff\<rfloor>)"

lemma power_increasing_int: 
  "1 \<le> n \<Longrightarrow> n \<le> N \<Longrightarrow> 0 \<le> (a :: int) \<Longrightarrow> a ^ n \<le> a ^ N"
  by (cases "a = 0", insert power_increasing[of n N a], auto simp: power_0_left)

lemma det_bound_hadamard_0[simp]: "det_bound_hadamard n c \<ge> 0" 
  unfolding det_bound_hadamard_def sqrt_int_floor_def by auto

lemma det_bound_hadamard_mono: assumes "0 < n" "n \<le> m"
  shows "det_bound_hadamard n c \<le> det_bound_hadamard m c" 
  unfolding det_bound_hadamard_def sqrt_int_floor
  apply (intro floor_mono real_sqrt_le_mono)
  unfolding of_int_le_iff
  using assms
  by (smt (verit, ccfv_SIG) One_nat_def Suc_leI linordered_semidom_class.power_mono mult_mono mult_nonneg_nonneg of_nat_0_le_iff of_nat_mono power_increasing_int zero_le_power2)  

lemma computebound_leq_computeboundnumofvars:
  shows "compute_bound (renvar_constraintlist cs (var_list cs)) \<le> compute_bound_num_of_vars cs"
proof -
  define rencs where "rencs = renvar_constraintlist cs (var_list cs)"
  define le_cs where "le_cs = normalize rencs"
  define le_cs' where "le_cs' = map constraint_to_ints le_cs"
  define max_cf where "max_cf = max_coeff_constraints le_cs'"
  define n where "n = 1 + constraints_max_var le_cs'"
  define Bnd where "Bnd = int (n + 1) * det_bound_hadamard n \<lfloor>max_cf\<rfloor>"
  have id: "compute_bound (renvar_constraintlist cs (var_list cs)) = Bnd"
    unfolding compute_bound_def Bnd_def n_def max_cf_def le_cs'_def le_cs_def rencs_def
    by metis
  define nn where "nn = 1 + length (var_list cs)"
  define max_coeff where "max_coeff = (let le_cs = normalize cs;
    le_cs' = map constraint_to_ints le_cs in max_coeff_constraints le_cs')"
  have ineq0: "n \<le> nn"
  proof -
    have fav: "\<forall>v \<in> \<Union> (vars ` (set (map lec_poly le_cs'))). v \<le> length (var_list cs)"
      using rencs_def renvar_constraintlist_var_range varlist_distinct
      consttoints_preserves_vars constrtoleconstr_preserves_vars le_cs_def
      unfolding le_cs'_def by fastforce
    have "constraints_max_var le_cs' \<in> {0} \<union> \<Union> (vars ` (set (map lec_poly le_cs')))"
    proof (cases le_cs')
      case Nil
      then show ?thesis unfolding constraints_max_var_def by simp
    next
      case (Cons a list)
      then show ?thesis
      proof -
        obtain lec where "lec \<in> set le_cs'" and
          "Max (lec_max_var ` set (le_cs')) = lec_max_var lec"
          using Gram_Schmidt_2.ex_MAXIMUM Cons List.finite_set set_empty2
          by (metis Collect_mem_eq empty_Collect_eq list.set_intros(1))
        thus ?thesis unfolding max_var_def constraints_max_var_def
          using Cons finite_vars vars_empty_zero by fastforce
      qed
    qed
    hence "constraints_max_var le_cs' \<le> length (var_list cs)" using fav by auto
    thus ?thesis unfolding n_def nn_def by simp
  qed
  have id': "max_cf = max_coeff"
    unfolding max_cf_def le_cs'_def le_cs_def rencs_def max_coeff_def
    using maxcoeffconstraints_renvar_invariant by simp
  have id'': "compute_bound_num_of_vars cs = int (nn + 1) * det_bound_hadamard nn \<lfloor>max_coeff\<rfloor>"
    unfolding compute_bound_num_of_vars_def max_coeff_def nn_def by metis
  have mc0: "floor max_coeff \<ge> 0" unfolding id'[symmetric] max_cf_def max_coeff_constraints_def 
    by simp
  have n0: "n > 0" unfolding n_def by auto
  show ?thesis unfolding id id'' Bnd_def id' using mc0 ineq0 n0 
    by (intro mult_mono det_bound_hadamard_mono, auto)
qed

lemma compute_bound:
  assumes "vl \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs_list, Is)"
  shows "\<exists> v. v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs_list, Is) \<and>
    (\<forall> i \<in> Is. \<bar>v i\<bar> \<le> of_int (compute_bound_num_of_vars cs_list))"
proof -
  define cs where "cs = renvar_constraintlist cs_list (var_list cs_list)"
  have dist: "distinct (var_list cs_list)" unfolding var_list_def by simp
  define v where "v = renvar_valuation vl (var_list cs_list)"
  define I where "I = renvar_index_set Is (var_list cs_list)"
  have v_models: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I)"
    using assms renvar_constraintlist_sat' renvar_valuation_int
    unfolding cs_def v_def I_def
    by (simp, smt distinct_remdups imageE renvar_index_set_def
        renvar_valuation_int var_list_def)

  define le_cs where "le_cs = normalize cs"
  define le_cs' where "le_cs' = map constraint_to_ints le_cs"
  define max_cf where "max_cf = max_coeff_constraints le_cs'"
  define n where "n = 1 + constraints_max_var le_cs'"
  define Bnd where "Bnd = int (n + 1) * det_bound_hadamard n \<lfloor>max_cf\<rfloor>"

  have "compute_bound cs = Bnd"
    unfolding compute_bound_def le_cs_def le_cs'_def
              max_cf_def n_def Bnd_def by metis
  hence ineq: "Bnd \<le> compute_bound_num_of_vars cs_list"
    unfolding cs_def using computebound_leq_computeboundnumofvars by auto

  interpret gram_schmidt_floor n .

  have int: "integral_constraints le_cs'"
    unfolding le_cs'_def integral_constraints_def
    using constraint_to_ints(2) by auto
  hence "max_cf \<in> \<int>"
    unfolding max_cf_def integral_constraints_def
              max_coeff_constraints_def
    using integral_max_coeff Max_in[of "set (0 # map max_coeff le_cs')"]
    by fastforce
  hence max: "max_cf = of_int \<lfloor>max_cf\<rfloor>" using floor_of_int_eq by auto
  have max_cf0: "\<lfloor>max_cf\<rfloor> \<ge> 0" unfolding max_cf_def
    using max_coeff_constraints_0 by simp
  from is_det_bound_ge_zero[OF det_bound_hadamard, OF this, of n]
  have "Bnd \<ge> 0" unfolding Bnd_def by auto


  obtain A b A' b' where matsvecs: "mats_vecs_of_constraints le_cs' = (A, b, A', b')"
    by (rule prod_cases4)
  obtain nr nr' where
    A_dim: "A \<in> carrier_mat nr n" and b_dim: "b \<in> carrier_vec nr" and
    A'_dim: "A' \<in> carrier_mat nr' n" and b'_dim: "b' \<in> carrier_vec nr'"
    using mats_vecs_of_constraints(1)[OF matsvecs n_def] by blast

  from mats_vecs_of_constraints(3-4)[OF matsvecs n_def] int
  have A: "A \<in> \<int>\<^sub>m \<inter> Bounded_mat max_cf"
   and A': "A' \<in> \<int>\<^sub>m \<inter> Bounded_mat max_cf"
   and b: "b \<in> \<int>\<^sub>v \<inter> Bounded_vec max_cf"
   and b': "b' \<in> \<int>\<^sub>v \<inter> Bounded_vec max_cf"
    unfolding max_cf_def by auto
  {
    fix v
    have "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (\<forall> c \<in> set le_cs. v \<Turnstile>\<^sub>l\<^sub>e c)"
      unfolding le_cs_def by (rule normalize_satisfies)
    also have "\<dots> \<longleftrightarrow> (\<forall> c \<in> set le_cs'. v \<Turnstile>\<^sub>l\<^sub>e c)"
      unfolding le_cs'_def using constraint_to_ints(1) by auto
    also have "\<dots> \<longleftrightarrow> (A *\<^sub>v vec n v \<le> b \<and> A' *\<^sub>v vec n v <\<^sub>v b')"
      by (rule mats_vecs_of_constraints(2)[OF matsvecs n_def])
    finally have "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (A *\<^sub>v vec n v \<le> b \<and> A' *\<^sub>v vec n v <\<^sub>v b')"
      by blast
  } note sat_cs = this
  hence Avb: "A *\<^sub>v vec n v \<le> b" and A'vb': "A' *\<^sub>v vec n v <\<^sub>v b'" using v_models by auto
  from v_models have "vec n v \<in> indexed_Ints_vec I"
    unfolding indexed_Ints_vec_def by auto
  from small_mixed_integer_solution[OF det_bound_hadamard A_dim A'_dim b_dim b'_dim _ _ _ _ _ this Avb A'vb',
    of "floor max_cf", folded max, OF A b A' b', folded Bnd_def] max_cf0       
  obtain x where xn: "x \<in> carrier_vec n" and xI: "x \<in> indexed_Ints_vec I"
                       and Axb: "A *\<^sub>v x \<le> b" and A'xb': "A' *\<^sub>v x <\<^sub>v b'"
                       and xBnd: "x \<in> Bounded_vec (of_int Bnd)" by auto


  define v' where "v' = (\<lambda> i. if i < n then x $ i else 0)"
  have "vec n v' = x" unfolding v'_def using xn by fastforce
  hence "v' \<Turnstile>\<^sub>c\<^sub>s set cs"
    using sat_cs Axb A'xb' by presburger
  moreover have "\<forall> i \<in> I. v' i \<in> \<int>"
    using xI xn unfolding v'_def indexed_Ints_vec_def by fastforce
  moreover have "\<forall> i. \<bar>v' i\<bar> \<le> of_int Bnd"
  proof (rule allI, cases)
    fix i assume "i < n"
    thus "\<bar>v' i\<bar> \<le> of_int Bnd"
      using xBnd xn unfolding v'_def Bounded_vec_def by fastforce
  next
    fix i assume "\<not> (i < n)"
    thus "\<bar>v' i\<bar> \<le> of_int Bnd" unfolding v'_def using `Bnd \<ge> 0` by fastforce
  qed
  ultimately have
    "\<exists>v. v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I) \<and> (\<forall>i\<in>I. \<bar>v i\<bar> \<le> rat_of_int (compute_bound_num_of_vars cs_list))"
    using ineq
    by (meson dual_order.trans of_int_le_iff satisfies_mixed_constraints.simps)
  from this obtain tmpv where
    "tmpv \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I) \<and> (\<forall>i\<in>I. \<bar>tmpv i\<bar> \<le> rat_of_int (compute_bound_num_of_vars cs_list))" by auto
  thus ?thesis
    using renvar_valuation_indexset_sat[OF varlist_distinct[of cs_list],
        of cs_list tmpv Is "rat_of_int (compute_bound_num_of_vars cs_list)"]
    unfolding cs_def I_def by simp
qed

definition vars_of_constraints :: "constraint list \<Rightarrow> var list" where
  "vars_of_constraints  cs = remdups (concat (map (vars_list o lec_poly) (normalize cs)))"

lemma vars_of_constraints_cong: assumes "\<And> x. x \<in> set (vars_of_constraints cs) \<Longrightarrow> v x = w x"
  shows "(v \<Turnstile>\<^sub>c\<^sub>s set cs) = (w \<Turnstile>\<^sub>c\<^sub>s set cs)"
  unfolding normalize_satisfies vars_of_constraints_def
proof (intro ball_cong[OF refl], goal_cases)
  case (1 c)
  with assms have "\<forall> x \<in> vars (lec_poly c). v x = w x"
    unfolding vars_of_constraints_def o_def by (auto simp: set_vars_list)
  from valuate_depend[OF this] show ?case by (cases c, auto)
qed

section \<open>Wrapper Lemmas for branch_and_bound using incremental simplex\<close>

definition branch_and_bound
where "branch_and_bound cs Is = (
  let Bnd = compute_bound_num_of_vars cs in
  let (cs', lb_m, ub_m, s) = bnb_state_init cs Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd) in
  case s of Inr s' \<Rightarrow> the (bnb_state_core_p cs' Is lb_m ub_m s')
          | Inl _ \<Rightarrow> None)"

lemma branch_and_bound_unsat:
  assumes "branch_and_bound cs Is = None" "distinct Is"
  shows "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
proof -
  define Bnd where "Bnd = compute_bound_num_of_vars cs"
  obtain cs' lb_m ub_m s where a: "(cs', lb_m, ub_m, s) = bnb_state_init cs Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd)"
    using prod_cases4 by metis
  have aa: "map snd cs' = cs"
    using a unfolding bnb_state_init_def by (auto simp add: Let_def)
  show ?thesis
  proof (cases s)
    case (Inl a)
    have b: "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd) @ cs)"
      using assms a Inl by (intro bnb_state_init'[of _ _ _ _ cs' lb_m ub_m s]) (auto)
    have False if c: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)" for v
    proof -
      obtain v where v: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)" and vBnd: "(\<forall> i \<in> set Is. \<bar>v i\<bar> \<le> of_int Bnd)"
        using c compute_bound unfolding Bnd_def by blast
      have "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is (\<lambda>_. - Bnd) (\<lambda>_. Bnd))"
        using vBnd v  by (subst bounds_to_constraints_sat) auto
      then have "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is (\<lambda>_. - Bnd) (\<lambda>_. Bnd) @ cs)"
        using v by auto
      then show False
        using b by blast
    qed
    then show ?thesis
      by blast
  next
    case (Inr s')
    define lb where "lb = the \<circ> Mapping.lookup lb_m"
    define ub where "ub = the \<circ> Mapping.lookup ub_m"
    have "bnb_state_core_p cs' Is lb_m ub_m s' = Some (bnb_state_core cs' Is lb ub s')"
      unfolding lb_def ub_def apply(rule bnb_state_core_p)
        apply(simp) apply(simp)
      apply(rule bnb_state_init[of _ cs "(\<lambda> _. -Bnd)" "(\<lambda> _. Bnd)" _ _ _ s])
      using assms Inr a by (auto)
    then have b1: "bnb_state_core cs' Is lb ub s' = None"
      using assms unfolding branch_and_bound_def using a Inr unfolding Bnd_def
      by (auto simp add: Let_def split: sum.splits prod.splits)
    have "map (\<lambda>x. snd (the (map_of (map2 (\<lambda>x y. (x, y, f x)) xs ys) x))) xs = map f xs"
      if "length ys = length xs" "distinct xs" for ys::"'c list" and xs and f::"'a \<Rightarrow> 'b"
      using that 
    proof (induction xs arbitrary: ys)
      case (Cons x xs)
      then have "\<exists>y ys'. ys = y # ys'"
        by (metis length_nth_simps(2) list.exhaust list.map(1) list.map(2) list.simps(3) list.size(3) nth_Cons_0 nth_Cons_Suc zip_Nil)
      then obtain y ys' where "ys = y # ys'"
        by blast
      then show ?case
        using Cons by (auto)
    qed simp
    then have 1: "(snd (the (map_of (map2 (\<lambda>x y. (x, y, f x)) xs ys) x))) = f x"
      if "length ys = length xs" "distinct xs" "x \<in> set xs"for ys::"'c list" and x xs and f::"'a \<Rightarrow> 'b"
      using map_eq_conv that by auto
    have False if c: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
    proof -
      have ca: "x \<in> set Is \<Longrightarrow> - Bnd = (snd \<circ> (the \<circ> Mapping.lookup lb_m)) x" for x
        using a 1 assms unfolding bnb_state_init_def  by (auto simp add: Let_def 1 lookup_of_alist)
      have cb: "x \<in> set Is \<Longrightarrow> Bnd = (snd \<circ> (the \<circ> Mapping.lookup ub_m)) x" for x
        using a 1 assms unfolding bnb_state_init_def  by (auto simp add: Let_def 1 lookup_of_alist)
      obtain v where v: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)" and vBnd: "(\<forall> i \<in> set Is. \<bar>v i\<bar> \<le> of_int Bnd)"
        using c compute_bound unfolding Bnd_def by blast
      have "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is (\<lambda>_. - Bnd) (\<lambda>_. Bnd))"
        using vBnd v  by (subst bounds_to_constraints_sat) auto
      then have "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` set cs', set Is)"
        apply(intro bnb_state_core_unsat)
        unfolding i_bounds_to_constraints
      apply(rule bnb_state_init[of _ cs "(\<lambda> _. -Bnd)" "(\<lambda> _. Bnd)" _ _ _ s])
        using assms Inr a b1 apply(auto  simp add: lb_def ub_def)
        apply(subst (asm) bounds_to_constraints_cong[of _ _ "snd \<circ> (the \<circ> Mapping.lookup lb_m)"
           _ "snd \<circ> (the \<circ> Mapping.lookup ub_m)"])
        using ca cb by (auto)
      then show ?thesis
        using v aa by fastforce
    qed
    then show ?thesis
      by blast
  qed
qed

lemma branch_and_bound_sat:
  assumes "branch_and_bound cs Is = Some v" "distinct Is"
  shows "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
proof -
  define Bnd where "Bnd = compute_bound_num_of_vars cs"
  obtain cs' lb_m ub_m s where a: "(cs', lb_m, ub_m, s) = bnb_state_init cs Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd)"
    using prod_cases4 by metis
  have aa: "map snd cs' = cs"
    using a unfolding bnb_state_init_def by (auto simp add: Let_def)
  show ?thesis
  proof (cases s)
    case (Inl a)
    then show ?thesis
      using assms a unfolding branch_and_bound_def Bnd_def
      by (auto simp add: Let_def split: prod.splits sum.splits)
  next
    case (Inr s')
    define lb where "lb = the \<circ> Mapping.lookup lb_m"
    define ub where "ub = the \<circ> Mapping.lookup ub_m"
    have "bnb_state_core_p cs' Is lb_m ub_m s' = Some (bnb_state_core cs' Is lb ub s')"
      unfolding lb_def ub_def apply(rule bnb_state_core_p)
        apply(simp) apply(simp)
      apply(rule bnb_state_init[of _ cs "(\<lambda> _. -Bnd)" "(\<lambda> _. Bnd)" _ _ _ s])
      using assms Inr a by auto
    then have b1: "bnb_state_core cs' Is lb ub s' = Some v"
      using assms unfolding branch_and_bound_def using a Inr unfolding Bnd_def
      by (auto simp add: Let_def split: sum.splits prod.splits)
    then have "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (snd ` (set cs'), set Is)"
      apply(intro bnb_state_core_sat)
      apply(rule bnb_state_init[OF _ a[symmetric]])
      using assms Inr a unfolding lb_def ub_def by auto
    then show ?thesis
      using aa by auto
  qed
qed

definition branch_and_bound_int :: "constraint list \<Rightarrow> int valuation option" where
  "branch_and_bound_int cs = (
    let vs = vars_of_constraints cs
    in case branch_and_bound cs vs of
     None \<Rightarrow> None
   | Some v \<Rightarrow> Some (\<lambda> x. if x \<in> set vs then int_of_rat (v x) else 0))"

lemma vars_of_constraints_distinct: "distinct (vars_of_constraints cs)"
  unfolding vars_of_constraints_def by simp

lemma branch_and_bound_int_sat: assumes "branch_and_bound_int cs = Some v"
  shows "(rat_of_int o v) \<Turnstile>\<^sub>c\<^sub>s set cs"
proof -
  let ?vs = "vars_of_constraints cs"
  from assms obtain w where
    some: "branch_and_bound cs ?vs = Some w" and
    v: "v = (\<lambda> x. if x \<in> set ?vs then int_of_rat (w x) else 0)"
    by (cases "branch_and_bound cs ?vs", auto simp: branch_and_bound_int_def)
  from branch_and_bound_sat[OF some]
  have w: "w \<Turnstile>\<^sub>c\<^sub>s set cs" and int: "\<forall>i\<in>set (vars_of_constraints cs). w i \<in> \<int>"
    using vars_of_constraints_distinct by auto
  moreover have "(w \<Turnstile>\<^sub>c\<^sub>s set cs) = ((rat_of_int o v) \<Turnstile>\<^sub>c\<^sub>s set cs)"
    by (rule vars_of_constraints_cong, unfold v, insert int, auto)
  ultimately show ?thesis by auto
qed

lemma branch_and_bound_int_unsat: assumes "branch_and_bound_int cs = None"
  shows "\<not> (rat_of_int \<circ> v) \<Turnstile>\<^sub>c\<^sub>s set cs"
proof -
  let ?vs = "vars_of_constraints cs"
  from assms have
    none: "branch_and_bound cs ?vs = None"
    by (cases "branch_and_bound cs ?vs", auto simp: branch_and_bound_int_def)
  from branch_and_bound_unsat[OF none, of "rat_of_int o v"] vars_of_constraints_distinct
  show ?thesis by auto
qed

hide_const (open) Var
hide_const (open) max_var
hide_const (open) vars_list

end
