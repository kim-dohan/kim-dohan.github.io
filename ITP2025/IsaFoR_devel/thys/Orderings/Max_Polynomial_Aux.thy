theory Max_Polynomial_Aux
  imports
    Integer_Arithmetic
    Polynomial_Interpolation.Ring_Hom
    "HOL-Algebra.Ring"
    Auxx.Util
begin

section \<open>list arithmetic (sum, product, max/plus)\<close>

subsection \<open>Missing product_lists\<close>

lemma product_lists_eq_Nil_iff [simp]: "product_lists xss = [] \<longleftrightarrow> [] \<in> set xss"
  by (induct xss, auto)

text \<open>
  Clearly the above simp rule is in a good direction. But also
  @{term "product_lists xss = []"} is a good simplification rule.
\<close>

lemma product_lists_Nil[simp]: "[] \<in> set xss \<Longrightarrow> product_lists xss = []" by simp

primrec product_indices where
  "product_indices [] = [[]]"
| "product_indices (n#ns) = concat (map (\<lambda>x. map (Cons x) (product_indices ns)) [0..<n])"

lemma length_product_indices[simp]:
  "length (product_indices ns) = prod_list ns"
  by (induct ns, auto simp: length_concat o_def sum_list_triv)

lemma product_lists_indices:
  "product_lists xss = map (zipf nth xss) (product_indices (map length xss))"
  by (induct xss, auto simp: o_def map_concat intro!: arg_cong[of _ _ concat] nth_equalityI)

lemma length_product_lists' [simp]:
  "length (product_lists xss) = prod_list (map length xss)"
  by (simp add: product_lists_indices)

lemma product_lists_map_map:
  "product_lists (map (map f) xss) = map (map f) (product_lists xss)"
  by (induct xss, auto simp: o_def product_lists_indices)

lemma product_lists_elements:
  "[] \<notin> set xss \<Longrightarrow> \<Union> (set (map set (product_lists xss))) = \<Union> (set (map set xss))"
  by (induct xss, auto)

lemma product_lists_elements2:
  assumes "xs \<in> set (product_lists xss)" and "x \<in> set xs"
  shows "\<exists>xs' \<in> set xss. x \<in> set xs'"
  by (insert assms product_lists_elements, cases "[] \<in> set xss", auto)

lemma in_set_product_lists_nth:
  assumes "ys \<in> set (product_lists xss)"
    and "i < length xss"
  shows "ys ! i \<in> set (xss ! i)"
proof (insert assms, induct xss arbitrary: i ys)
  case (Cons xs xss)
  then show ?case by (cases i, auto)
qed simp

lemma list_all2_indices:
  assumes "[] \<notin> set xss" "list_all2 (\<lambda> x' xs'. x' \<in> set xs') xs xss"
  shows "\<exists> ks. list_all2 (\<lambda> k p. fst p = (snd p) ! k) ks (zip xs xss)"
proof (insert assms, induct xss arbitrary: xs)
  case (Cons ys yss)
  then obtain z zs where "xs = z # zs" unfolding list_all2_iff
    by (meson Cons.prems(2) list_all2_Cons2)
  note [simp] = this
  then obtain ks' where *: "list_all2 (\<lambda> k p. (fst p) = (snd p) ! k) ks' (zip zs yss)" using Cons unfolding list_all2_iff
    by fastforce
  obtain k where "ys ! k = z" using Cons
    by (metis (no_types, lifting) \<open>xs = z # zs\<close> in_set_conv_nth list.rel_inject(2))
  note [simp] = this
  show ?case
    apply (rule exI[of _ "k # ks'"]) using * by auto
qed auto

subsection \<open>Fundamental Results\<close>

lemma prod_list_map_filter: (* MOVE-- a counterpart of sum_list_map_filter *)
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> f x = 1"
  shows "prod_list (map f (filter P xs)) = prod_list (map f xs)"
  using assms by (induct xs, auto)

(*TODO: in SN_Orders -- assumptions could be stated nicer *)
context non_strict_order
begin
lemma antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  using max_comm[of x y] by (auto simp: max_def)
lemma total: "x \<le> y \<or> y \<le> x"
  by (metis max_ge_y max_def)
end

(* TODO: Names conflict *)
hide_class SN_Orders.ordered_semiring_0 SN_Orders.ordered_semiring_1

(* TODO: Propose for distribution *)

context zero_less_one begin

subclass zero_neq_one using zero_less_one by (unfold_locales, blast)

lemma zero_le_one[intro!]: "0 \<le> 1" by (auto simp: le_less)

end

class ordered_semigroup_mult_zero = order + semigroup_mult + mult_zero +
  assumes mult_right_mono: "\<And>a b c. a \<le> b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> a * c \<le> b * c"
  assumes mult_left_mono: "\<And>a b c. a \<le> b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> c * a \<le> c * b"
begin

lemma mult_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
  apply (erule (1) mult_right_mono [THEN order_trans])
  apply (erule (1) mult_left_mono)
  done

lemma mult_mono': "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * d"
  by (rule mult_mono) (fast intro: order_trans)+

lemma mult_nonneg_nonneg [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * b"
  using mult_left_mono [of 0 b a] by simp

lemma mult_nonneg_nonpos: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> a * b \<le> 0"
  using mult_left_mono [of b 0 a] by simp

lemma mult_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> a * b \<le> 0"
  using mult_right_mono [of a 0 b] by simp

text \<open>Legacy -- use @{thm [source] mult_nonpos_nonneg}.\<close>
lemma mult_nonneg_nonpos2: "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> b * a \<le> 0"
  by (drule mult_right_mono [of b 0]) auto

lemma split_mult_neg_le: "(0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b) \<Longrightarrow> a * b \<le> 0"
  by (auto simp add: mult_nonneg_nonpos mult_nonneg_nonpos2)

end

subclass (in Rings.ordered_semiring_0) ordered_semigroup_mult_zero
  by (unfold_locales; fact mult_right_mono mult_left_mono)

class ordered_monoid_mult_zero = ordered_semigroup_mult_zero + monoid_mult + zero_less_one
begin

lemma prod_list_nonneg:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0"
  shows "prod_list xs \<ge> 0"
  using assms by (induct xs, auto)

end


class ordered_semiring_1 = ordered_semiring_0 + monoid_mult + zero_less_one
begin

subclass semiring_1..

lemma prod_list_nonneg:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<ge> 0"
  shows "prod_list xs \<ge> 0"
  using assms by (induct xs, auto)

lemma prod_list_nonneg_nth:
  assumes "\<And>i. i < length xs \<Longrightarrow> xs ! i \<ge> 0"
  shows "prod_list xs \<ge> 0"
  using assms by (auto intro!: prod_list_nonneg simp: in_set_conv_nth)

end

subclass (in linordered_semiring_1) ordered_semiring_1..

instance nat :: linordered_semiring_1..
instance int :: linordered_semiring_1..
instance rat :: linordered_semiring_1..
instance real :: linordered_semiring_1..


definition max_list1 where
  "max_list1 xs \<equiv> if xs = [] then undefined else foldr max (butlast xs) (last xs)"

lemma max_list1_Cons[simp]: "max_list1 (x#xs) = (if xs = [] then x else max x (max_list1 xs))"
  by (auto simp: max_list1_def)

text \<open>@{const max_list1} is @{term "Max \<circ> set"}, but the latter require a total order.\<close>
lemma max_list1_as_Max:
  shows "max_list1 xs = Max (set xs)"
proof (cases "xs = []")
  case True
  then show ?thesis by (auto simp: Max.eq_fold' option.the_def max_list1_def)
next
  case False
  then show ?thesis
  proof (induct xs)
    case (Cons x xs)
    then show ?case by (cases "xs = []", auto simp: max_def)
  qed auto
qed

lemma max_list1_cong: "set xs = set ys \<Longrightarrow> max_list1 xs = max_list1 ys" for xs ys :: "int list"
  using max_list1_as_Max by metis

(* TODO: Replace AFP/Matrix/Utility/max_list *)
definition max_list where
  "max_list xs \<equiv> foldr max xs bot"

lemma max_list_Nil[simp]: "max_list [] = bot"
  and max_list_Cons[simp]: "max_list (x#xs) = max x (max_list xs)"
  by (auto simp: max_list_def)

lemma (in order_bot) max_bot [simp]: (* no need for order *)
  "max bot x = x" "max x bot = x" by (auto simp: max_def)

lemma max_list_as_max_list1_bot:
  shows "max_list xs = max_list1 (xs @ [bot])"
  by (induct xs, auto)

lemma max_list_as_max_list1:
  fixes xs :: "'a :: order_bot list"
  assumes "xs \<noteq> []" shows "max_list xs = max_list1 xs"
  by (insert assms, induct xs, auto)


lemma max_list_append [simp]:
  fixes xs ys :: "'a :: {linorder,order_bot} list"
  shows "max_list (xs @ ys) = max (max_list xs) (max_list ys)"
  by (induct xs arbitrary: ys, auto simp: ac_simps)

lemma max_list_concat:
  fixes xss :: "'a :: {linorder,order_bot} list list"
  shows "max_list (concat xss) = max_list (map max_list xss)"
  by (induct xss, auto)

lemma max_list1_append:
  fixes xs ys :: "'a :: linorder list"
  shows "max_list1 (xs @ ys) = (if xs = [] then max_list1 ys else if ys = [] then max_list1 xs else max (max_list1 xs) (max_list1 ys))"
  by (induct xs arbitrary: ys, auto simp: ac_simps)

lemma max_list1_concat:
  fixes xss :: "'a :: linorder list list"
  assumes "[] \<notin> set xss"
  shows "max_list1 (concat xss) = max_list1 (map max_list1 xss)"
  by (insert assms, induct xss, simp, insert List.last_in_set, force simp: max_list1_append)

lemma max_list1_mem: "xs \<noteq> [] \<Longrightarrow> max_list1 xs \<in> set xs"
proof (induct xs)
  case (Cons x xs)
  then show ?case by (cases xs, auto simp: max_def)
qed auto

lemma max_list_map_filter:
  fixes f :: "_ \<Rightarrow> 'a :: order_bot"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> f x = bot"
  shows "max_list (map f (filter P xs)) = max_list (map f xs)"
  using assms by (induct xs, auto)

lemma max_list_cong:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows "max_list (map f xs) = max_list (map g xs)"
  using assms by (induct xs, auto)

lemma hom_max:
  assumes "f x = f y \<or> (f x \<le> f y \<longleftrightarrow> x \<le> y)"
  shows "f (max x y) = max (f x) (f y)"
  using assms by (auto simp: max_def)

lemma hom_max_list1:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x = f y \<or> (f x \<le> f y \<longleftrightarrow> x \<le> y)" and "xs \<noteq> []"
  shows "f (max_list1 xs) = max_list1 (map f xs)"
proof (insert assms, induct xs)
  case IH: (Cons x xs)
  show ?case
  proof (cases xs)
    case [simp]: (Cons y ys)
    from IH have "max_list1 (map f xs) = f (max_list1 xs)" by auto
    with max_list1_mem[of xs] hom_max[of f, OF IH.prems(1)]
    show ?thesis by auto
  qed auto
qed auto

(* should this really be called ord_hom? *)
locale ord_hom = fixes hom
  assumes ord_hom_condition: "\<And>x y. hom x = hom y \<or> (hom x \<le> hom y \<longleftrightarrow> x \<le> y)"
begin
lemmas hom_max = hom_max[of hom, OF ord_hom_condition]
lemmas hom_max_list1 = hom_max_list1[of _ hom, OF ord_hom_condition]
end

locale ord_hom_strict = fixes hom
  assumes hom_le_hom[simp]: "\<And>x y. hom x \<le> hom y \<longleftrightarrow> x \<le> y"
begin
sublocale ord_hom by (unfold_locales, auto)
end

locale linorder_hom = fixes hom :: "'a :: linorder \<Rightarrow> 'b :: linorder"
  assumes mono: "x \<le> y \<Longrightarrow> hom x \<le> hom y"
begin

sublocale ord_hom using mono by (unfold_locales, auto)

text \<open>@{thm mono_Max_commute} is derivable\<close>
lemma hom_Max:
  assumes finX: "finite X" and X0: "X \<noteq> {}" shows "hom (Max X) = Max (hom ` X)"
proof-
  obtain xs where "set xs = X" using finX finite_list by auto
  with X0 hom_max_list1[unfolded max_list1_as_Max, of xs] show ?thesis by auto
qed

end

interpretation add_hom: ord_hom "\<lambda>y :: 'a :: ordered_ab_semigroup_add_imp_le. x + y"
  by (unfold_locales, auto)

interpretation add_hom_right: ord_hom "\<lambda>x :: 'a :: ordered_ab_semigroup_add_imp_le. x + y"
  by (unfold_locales, auto)

interpretation int_hom: linorder_hom int by (unfold_locales, auto)

lemma sum_list_max_list1:
  fixes xss :: "'a :: {linordered_semiring} list list"
  assumes "[] \<notin> set xss"
  shows "sum_list (map max_list1 xss) = max_list1 (map sum_list (product_lists xss))"
proof (insert assms, induct xss)
  case (Cons xs xss)
  show ?case
  proof (cases "xss = []")
    case False
    have [simp]: "max_list1 (map (\<lambda>xs. x + sum_list xs) (product_lists xss)) = x + sum_list (map max_list1 xss)" for x
    proof-
      have "map (\<lambda>xs. x + sum_list xs) (product_lists xss) = map (\<lambda>y. x + y) (map sum_list (product_lists xss))"
        by auto
      also have "max_list1 \<dots> = x + max_list1 (map sum_list (product_lists xss))"
        apply (rule hom_max_list1[symmetric])
        using False Cons by auto
      also have "\<dots> = x + sum_list (map max_list1 xss)" using Cons by auto
      finally show ?thesis.
    qed
    show ?thesis
      apply (auto simp:map_concat)
      apply (subst max_list1_concat)
      using Cons apply force
      apply (simp add: o_def)
      apply (subst add_hom_right.hom_max_list1) using False Cons.prems by auto
  qed (auto simp: o_def)
qed simp

lemma prod_list_max_list1:
  fixes xss :: "'a :: {linordered_nonzero_semiring,linordered_semiring} list list"
  assumes "[] \<notin> set xss" and "\<And>x. x \<in> \<Union>(set ` set xss) \<Longrightarrow> x \<ge> 0"
  shows "prod_list (map max_list1 xss) = max_list1 (map prod_list (product_lists xss))"
proof (insert assms, induct xss)
  case (Cons xs xss)
  show ?case
  proof (cases "xss = []")
    case False
    { fix x :: 'a assume "x \<in> set xs"
      with Cons.prems have x0: "x \<ge> 0" by auto
      have "map (\<lambda>xs. x * prod_list xs) (product_lists xss) = map (\<lambda>y. x * y) (map prod_list (product_lists xss))"
        by auto
      also have "max_list1 \<dots> = x * max_list1 (map prod_list (product_lists xss))"
        apply (rule hom_max_list1[symmetric])
        using False Cons.prems x0 by (auto intro!: monoI mult_left_mono)
      also have "\<dots> = x * prod_list (map max_list1 xss)" using Cons by auto
      finally have "max_list1 (map (\<lambda>xs. x * prod_list xs) (product_lists xss)) = \<dots>".
    }
    note 1 = map_cong[OF refl this]
    from Cons.prems have "(\<And>x. x \<in> \<Union>(set ` set xss) \<Longrightarrow> x \<ge> 0)" "[] \<notin> set xss" by auto
    then have 2: "prod_list (map max_list1 xss) \<ge> 0"
    proof (induct xss)
      case (Cons xs xss)
      then have "max_list1 xs \<ge> 0" using max_list1_mem[of xs] by auto
      with Cons show ?case by auto
    qed (auto)
    from Cons.prems have 3: "xs \<noteq> []" by auto
    have "max_list1 xs \<ge> 0" using Cons.prems max_list1_mem[of xs] by auto
    show ?thesis
      apply (auto simp:map_concat)
      apply (subst max_list1_concat)
      using Cons.prems apply force
      apply (simp add: o_def)
      apply (subst 1, assumption)
      apply (subst hom_max_list1[of _ "\<lambda>x. x * _"]) using mult_right_mono[OF _2] 3 by auto
  qed (auto simp: o_def)
qed simp

text \<open>extented max: for example, f(x1, x2) = max { 0, 1 * x1 - 1, 0 * x2 + 1 } (note that one can ignore some of xs) \<close>

fun madd :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "madd c d x = c + d * x"

lemma madd_id[simp]: "madd 0 1 = id" by fastforce

lemma madd_weakly_monotone:
  "x \<le> y \<Longrightarrow> madd c d x \<le> madd c d y"
  using times_right_mono by auto

lemma madd_max: "madd c d (max x y) = max (madd c d x) (madd c d y)"
  using madd_weakly_monotone by (smt (verit, del_insts))

lemma madd_max_list1[simp]:
  "xs \<noteq> [] \<Longrightarrow> madd c d (max_list1 xs) = max_list1 (map (madd c d) xs)"
proof (induct xs)
  case *: (Cons x xs)
  then show ?case
  proof (cases xs)
    case (Cons y ys)
    with * have IH: "madd c d (max_list1 xs) = max_list1 (map (madd c d) xs)"
      by blast
    have "madd c d (max_list1 (x # xs)) = max (madd c d x) (madd c d (max_list1 xs))"
      using Cons madd_max by simp
    also have "... = max (madd c d x) (max_list1 (map (madd c d) xs))"
      using IH by presburger
    also have "... = max_list1 (map (madd c d) (x # xs))"
      using calculation by auto
    finally show ?thesis .
  qed auto
qed auto

text \<open>[c_1 + d_1 x_1, ..., c_n + d_n x_n]\<close>

fun madd_list :: "(int \<times> nat) list \<Rightarrow> int list \<Rightarrow> int list" where
  "madd_list _ [] = []" |
  "madd_list [] (x # xs) = (madd 0 1 x) # madd_list [] xs" |
  "madd_list ((c, d) # cds) (x # xs) = (madd c d x) # madd_list cds xs"

lemma madd_list_non_empty[simp]:
  "madd_list bcs (ls @ a # rs) \<noteq> []"
  by (auto elim: madd_list.elims)

lemma madd_list_non_empty'[simp]:
  "madd_list bcs (a # rs) \<noteq> []"
  by (auto elim: madd_list.elims)

(* should have [simp] *)
lemma madd_list_id: "madd_list [] = id"
proof
  fix xs
  show "madd_list [] xs = id xs" by (induct xs, auto)
qed

lemma madd_list_singleton[simp]: "madd_list cds [x] = (if cds = [] then [x] else [fst (hd cds) + int (snd (hd cds)) * x])"
proof (cases "cds = []")
  case False
  then obtain c d cds' where "cds = ((c, d) # cds')"
    by (metis ce_trs.cases neq_Nil_conv)
  then show ?thesis by auto
qed auto

lemma length_madd_list[simp]:
  "length (madd_list cds xs) = length xs"
  by (induction rule: madd_list.induct, auto)

lemma max_madd_max_list1:
  assumes "xs \<noteq> []" "ys \<noteq> []"
  shows "max (madd c d (max_list1 xs)) (max_list1 ys) = max_list1 ((map (madd c d) xs) @ ys)"
proof -
  have "max (madd c d (max_list1 xs)) (max_list1 ys)
    = max (max_list1 (map (madd c d) xs)) (max_list1 ys)"
    by (subst madd_max_list1[OF assms(1)], rule refl)
  also have "\<dots> = max_list1 ((map (madd c d) xs) @ ys)" using max_list1_append assms
    by (metis Nil_is_map_conv)
  finally show ?thesis .
qed

fun max_ext_list' :: "nat \<Rightarrow> (int \<times> nat) list \<Rightarrow> int list \<Rightarrow> int" where
  "max_ext_list' c0 cds xs = max_list1 (c0 # madd_list cds xs)"

lemma max_ext_list'_nat: "max_ext_list' c0 bcs xs \<ge> 0"
  by fastforce

lemma madd_list_index:
  assumes "i < length xs" (* we cannot drop the guard, try nitpick *)
  shows "(madd_list cds xs) ! i = (if i < length cds then fst (cds ! i) + snd (cds ! i) * (xs ! i) else xs ! i)"
proof (insert assms, induction arbitrary: i rule: madd_list.induct)
  case (2 x xs)
  show ?case
  proof (cases "i = 0")
    case False
    then obtain i' where "i = Suc i'"
      using gr0_implies_Suc by blast
    with 2 False show ?thesis by simp
  qed auto
next
  case (3 c d cds x xs)
  show ?case
  proof (cases "i = 0")
    case False
    then obtain i' where "i = Suc i'"
      using gr0_implies_Suc by blast
    with 3 False show ?thesis by simp
  qed auto
qed auto

lemma set_madd_list_cons:
  "y \<in> set (madd_list ((c, d) # cds) (x # xs)) \<Longrightarrow> y \<notin> set (madd_list cds xs) \<Longrightarrow> y = madd c d x"
  by simp

lemma set_madd_list_if:
  "y \<in> set (madd_list cds xs) \<longrightarrow> (\<exists> i< length xs. y = (if i < length cds then fst (cds ! i) + snd (cds ! i) * (xs ! i) else xs ! i))"
proof (induction xs arbitrary: cds y)
  case IH: (Cons x xs')
  show ?case
  proof (intro impI, cases cds)
    case Nil
    note [simp] = this
    assume "y \<in> set (madd_list cds (x # xs'))"
    with madd_list_id have "y \<in> set (x # xs')" by simp   
    then show "\<exists>i<length (x # xs'). y = (if i < length cds then fst (cds ! i) + int (snd (cds ! i)) * (x # xs') ! i else (x # xs') ! i)"
      by (metis in_set_conv_nth list.size(3) local.Nil not_less_zero)
  next
    case (Cons cd cds')
    then obtain c d where "cds = (c, d) # cds'" by fastforce
    note [simp] = this
    assume assm: "y \<in> set (madd_list cds (x # xs'))"
    then show  "\<exists>i<length (x # xs'). y = (if i < length cds then fst (cds ! i) + int (snd (cds ! i)) * (x # xs') ! i else (x # xs') ! i)"
    proof (cases "y \<in> set (madd_list cds' xs')")
      case True
      with IH obtain i
        where *: "i < length xs'" "y = (if i < length cds' then fst (cds' ! i) + snd (cds' ! i) * (xs' ! i) else xs' ! i)"
        by blast
      let ?i = "Suc i"
      have "?i < length (x # xs')" using * by fastforce
      moreover
      have "y = (if ?i < length cds then fst (cds ! ?i) + snd (cds ! ?i) * ((x # xs') ! ?i) else (x # xs') ! ?i)"
        using * by force
      ultimately show ?thesis by fast
    next
      case False
      with set_madd_list_cons assm have "y = madd c d x" by force
      then have "y = (if 0 < length cds then fst (cds ! 0) + int (snd (cds ! 0)) * (x # xs') ! 0 else (x # xs') ! 0)"
        by simp
      then show ?thesis by blast
    qed
  qed
qed auto

lemma set_madd_list_iff:
  "y \<in> set (madd_list cds xs) \<longleftrightarrow> (\<exists> i< length xs. y = (if i < length cds then fst (cds ! i) + snd (cds ! i) * (xs ! i) else xs ! i))"
proof (intro iffI, goal_cases)
  case 1
  then show ?case using set_madd_list_if by blast
next
  case 2
  then obtain i where *: "i < length xs"
    "y = (if i < length cds then fst (cds ! i) + int (snd (cds ! i)) * xs ! i else xs ! i)"
    by blast 
  also have " (madd_list cds xs) ! i  = (if i < length cds then fst (cds ! i) + snd (map (\<lambda>(x, y). (x, int y)) cds ! i) * xs ! i else xs ! i)"
    using madd_list_index[OF *(1), of cds] by simp
  ultimately have "y = (madd_list cds xs) ! i"
    by (simp add: split_beta)
  then show ?case
    using \<open>i < length xs\<close> by auto
qed

lemma max_list1_madd_list_mono':
  assumes "a \<le> b"
  shows "max_list1 (madd_list bcs (a # rs)) \<le> max_list1 (madd_list bcs (b # rs))"
proof (cases bcs)
  case Nil
  then show ?thesis
    using assms list.distinct(1) by auto
next
  case (Cons a list)
  then show ?thesis
    by (smt (verit, del_insts) assms list.distinct(1) list_tail_coinc madd_list.elims madd_weakly_monotone max_def max_list1_Cons prod.inject)
qed

lemma max_list1_madd_list_mono:
  assumes "a \<le> b"
  shows "max_list1 (madd_list bcs (ls @ a # rs)) \<le> max_list1 (madd_list bcs (ls @ b # rs))"
proof (induct ls arbitrary: bcs)
  case Nil
  then show ?case using assms max_list1_madd_list_mono' by auto
next
  case IH: (Cons x xs)
  then show ?case
  proof (cases bcs)
    case Nil
    then show ?thesis
      apply simp
      using max.coboundedI2 IH by blast
  next
    case (Cons bc bcs')
    note [simp] = this
    obtain b c where "bc = (b, c)" by fastforce
    note [simp] = this
    then show ?thesis
      apply simp using max.coboundedI2 IH by blast
  qed
qed

lemma max_ext_list'_weakly_mono:
  assumes "a \<le> b"
  shows "max_ext_list' c0 bcs (ls @ a # rs) \<le> max_ext_list' c0 bcs (ls @ b # rs)"
proof (induct ls arbitrary: bcs)
  case *: Nil
  have "max_list1 (madd_list bcs (a # rs)) \<le> max_list1 (madd_list bcs (b # rs))"
    using assms max_list1_madd_list_mono' by simp
  then show ?case by simp
next
  case *: (Cons y ys)
  show ?case
  proof (cases bcs)
    case Nil
    then show ?thesis
    proof (cases "madd_list [] (ys @ b # rs) = []")
      case True
      then show ?thesis by fastforce
    next
      case False
      have "max_list1 (madd_list [] (ys @ a # rs)) \<le> max (int c0) (max y (max_list1 (madd_list [] (ys @ b # rs))))"
        using assms max_list1_madd_list_mono
        by (meson max.coboundedI2)
      then show ?thesis using * Nil by simp
    qed
  next
    case (Cons x xs)
    note [simp] = this
    then obtain c d where "x = (c, d)" by fastforce
    note [simp] = this
    have "max_ext_list' c0 xs (ys @ a # rs) \<le> max_ext_list' c0 xs (ys @ b # rs)"
      using * by blast
    thus ?thesis by force
  qed
qed

lemma max_list1_madd_list':
  "[] \<notin> set xss \<longrightarrow>
   max_list1 (madd_list cds (map max_list1 xss)) = max_list1 (concat (map (madd_list cds) (product_lists xss)))"
proof (induct xss arbitrary: cds)
  case (Cons xs xss')
  then have IH: "\<And> cds. [] \<notin> set xss' \<Longrightarrow> max_list1 (madd_list cds (map max_list1 xss')) = max_list1 (concat (map (madd_list cds) (product_lists xss')))"
    by blast
  show ?case
  proof (rule impI)
    assume nil_notin: "[] \<notin> set (xs # xss')"
    then have "xs \<noteq> []" by fastforce
    note [simp] = this
    from nil_notin have "[] \<notin> set xss'" by fastforce
    note [simp] = this
    show "max_list1 (madd_list cds (map max_list1 (xs # xss'))) = max_list1 (concat (map (madd_list cds) (product_lists (xs # xss'))))"
    proof (cases xss')
      case Nil
      note [simp] = this
      then show ?thesis
      proof (cases "cds = []")
        case True
        then show ?thesis by (simp add: o_def)
      next
        case False
        then obtain c d cds' where "cds = ((c, d) # cds')"
          by (metis ce_trs.cases neq_Nil_conv)
        note [simp] = this
        have " max_list1 (madd_list cds (map max_list1 (xs # xss'))) = madd c d (max_list1 xs)" by simp
        also have "\<dots> = max_list1 (map (madd c d) xs)"
          using madd_max_list1[OF \<open>xs \<noteq> []\<close>] by simp
        also have "\<dots> = max_list1 (concat (map (madd_list ((c, d) # cds') \<circ> (\<lambda>x. [x])) xs))"
          unfolding o_def using map_eq_conv by fastforce
        also have "\<dots> = max_list1 (concat (map (madd_list cds) (product_lists (xs # xss'))))" by simp
        ultimately show ?thesis by presburger 
      qed 
    next
      case Cons_xss': (Cons xs' xss'')
      then have "madd_list [] (map max_list1 xss') \<noteq> []" by fastforce
      note [simp] = this
      have *: "\<exists>x. length x = length xss' \<and> (\<forall>x\<in>set (zip x xss'). case x of (x, y) \<Rightarrow> x \<in> set y)"
      proof -
        have "product_lists xss' \<noteq> []" using Cons_xss' nil_notin by force
        then obtain x where *: "x = (product_lists xss') ! 0" by blast
        then have  "x \<in> set (product_lists xss')"
          by (meson \<open>product_lists xss' \<noteq> []\<close> in_set_conv_nth length_greater_0_conv)
        then have "length x = length xss'" using in_set_product_lists_length by blast
        moreover
        from in_set_product_lists_nth[OF \<open>x \<in> set (product_lists xss')\<close>]
        have "i < length xss' \<Longrightarrow> x ! i \<in> set (xss' ! i)" for i .
        with in_set_zip have "\<forall>y \<in>set (zip x xss'). fst y \<in> set (snd y)" by metis
        ultimately show ?thesis by fastforce
      qed
      show ?thesis
      proof (cases cds)
        let ?f = "madd_list []"
        case Nil (* NOTE: very similar to Cons case *)
        note [simp] = this
        have "madd_list cds (map max_list1 xss') \<noteq> []"
          by (simp add: Cons_xss')
        note [simp] = this 
        have "max_list1 (madd_list cds (map max_list1 (xs # xss'))) =
          max (max_list1 xs) (max_list1 (concat (map (madd_list cds) (product_lists xss'))))"
          by (simp add: IH)
        also have "... = max (max_list1 (map (madd 0 1) xs)) (max_list1 (concat (map (madd_list cds) (product_lists xss'))))"
          using madd_id by auto
        also have "... =
          max_list1 (((map (madd 0 1) xs)) @ (concat (map (madd_list cds) (product_lists xss'))))"
        proof - (*   *)
          have "concat (map (madd_list cds) (product_lists xss')) \<noteq> []"
            using Cons_xss' nil_notin by auto
          moreover
          have "(map (madd 0 1) xs) \<noteq> []" using \<open>xs \<noteq> []\<close> by simp
          ultimately show ?thesis using max_list1_append by metis
        qed
        also have "... = max_list1 (concat (map (madd_list cds) (product_lists (xs # xss'))))"
          apply (rule max_list1_cong)
          apply (auto simp: product_lists_set list_all2_iff *)
          using \<open>xs \<noteq> []\<close> by blast
        finally show ?thesis .
      next
        case (Cons cd cds') (* essential case *)
        note [simp] = this
        obtain c d where "cd = (c, d)" by fastforce
        note [simp] = this
        have "madd_list cds' (map max_list1 xss') \<noteq> []"
          by (simp add: Cons_xss')
        note [simp] = this 
        have "max_list1 (madd_list cds (map max_list1 (xs # xss'))) =
          max (c + int d * max_list1 xs) (max_list1 (concat (map (madd_list cds') (product_lists xss'))))"
          by (simp add: IH)
        also have "... = max (max_list1 (map (madd c d) xs)) (max_list1 (concat (map (madd_list cds') (product_lists xss'))))"
          by (metis \<open>xs \<noteq> []\<close> madd.elims madd_max_list1)
        also have "... =
          max_list1 (((map (madd c d) xs)) @ (concat (map (madd_list cds') (product_lists xss'))))"
        proof -
          have "concat (map (madd_list cds') (product_lists xss')) \<noteq> []"
            using Cons_xss' nil_notin by auto
          moreover
          have "(map (madd c d) xs) \<noteq> []" using \<open>xs \<noteq> []\<close> by simp
          ultimately show ?thesis using max_list1_append by metis
        qed
        also have "... = max_list1 (concat (map (madd_list cds) (product_lists (xs # xss'))))"
        proof -
          have *: "\<exists>x. length x = length xss' \<and> (\<forall>x\<in>set (zip x xss'). case x of (x, y) \<Rightarrow> x \<in> set y)"
          proof -
            have "product_lists xss' \<noteq> []" using Cons_xss' nil_notin by force
            then obtain x where *: "x = (product_lists xss') ! 0" by blast
            then have  "x \<in> set (product_lists xss')"
              by (meson \<open>product_lists xss' \<noteq> []\<close> in_set_conv_nth length_greater_0_conv)
            then have "length x = length xss'" using in_set_product_lists_length by blast
            moreover
            from in_set_product_lists_nth[OF \<open>x \<in> set (product_lists xss')\<close>]
            have "i < length xss' \<Longrightarrow> x ! i \<in> set (xss' ! i)" for i .
            with in_set_zip have "\<forall>y \<in>set (zip x xss'). fst y \<in> set (snd y)" by metis
            ultimately show ?thesis by fastforce
          qed
          show ?thesis
            apply (rule max_list1_cong)
            apply (auto simp: product_lists_set list_all2_iff *)
            apply fastforce
            done
        qed
        finally show ?thesis .
      qed
    qed
  qed
qed auto

lemma max_list1_madd_list:
  "[] \<notin> set xss \<Longrightarrow>
   max_list1 (madd_list cds (map max_list1 xss)) = max_list1 (concat (map (madd_list cds) (product_lists xss)))"
  using max_list1_madd_list' ..

lemma madd_list_max_list_non_empty:
  assumes "xss \<noteq> []" and "[] \<notin> set xss" 
  shows "madd_list cds (map max_list1 xss) \<noteq> []"
  apply (insert assms) using madd_list.elims by auto

lemma max_ext_list'_max_list1: (* distributive law for max_ext *)
  assumes "[] \<notin> set xss"
  shows "max_ext_list' c0 cds (map max_list1 xss) = max_list1 (c0 # concat (map (madd_list cds) (product_lists xss)))"
proof (cases "xss = []")
  case False
  have "\<exists> xs\<in>set (product_lists xss). madd_list cds xs \<noteq> []"
  proof -
    obtain xs where xs: "xs \<in> set (product_lists xss)" and "xs \<noteq> []"
      using assms False
      by (metis in_set_product_lists_length length_greater_0_conv max_list1_mem product_lists_eq_Nil_iff)
    then have " madd_list cds xs \<noteq> []"
      using madd_list.elims by blast
    with xs show ?thesis by blast
  qed
  then show ?thesis
    apply (simp add: max_list1_madd_list[OF assms] madd_list_max_list_non_empty[OF False assms]) by blast
qed auto

abbreviation max_ext_list
  where "max_ext_list c0 cds xs \<equiv> nat (max_ext_list' c0 cds (map int xs))"

lemma max_ext_list_weakly_mono:
  assumes "a \<le> b"
  shows "max_ext_list c0 cds (ls @ a # rs) \<le> max_ext_list c0 cds (ls @ b # rs)"
  using assms nat_mono max_ext_list'_weakly_mono by force

subsection \<open>IA-related stuff\<close>

(* TODO: Move (to where?) *)
interpretation int_hom: comm_semiring_hom int by (unfold_locales, auto)

instantiation IA.val :: plus
begin
fun plus_val where
  "plus_val (IA.Int x) (IA.Int y) = IA.Int (x + y)"
| "plus_val (IA.Bool x) (IA.Bool y) = IA.Bool (x \<or> y)"
instance..
end

instantiation IA.val :: times
begin
fun times_val where
  "times_val (IA.Int x) (IA.Int y) = IA.Int (x * y)"
| "times_val (IA.Bool x) (IA.Bool y) = IA.Bool (x \<and> y)"
instance..
end


definition listprod where "listprod G xs \<equiv> foldr (mult G) xs (one G)"

lemma listprod_Nil[simp]: "listprod G [] = one G" by (auto simp: listprod_def)

lemma listprod_Cons[simp]: "listprod G (x#xs) = mult G x (listprod G xs)" by (auto simp: listprod_def)

lemma nth_ConsI: "(i = 0 \<Longrightarrow> P x) \<Longrightarrow> (\<And>j. i = Suc j \<Longrightarrow> P (xs!j)) \<Longrightarrow> P ((x#xs)!i)"
  by (cases i, auto)

lemma (in comm_monoid) listprod_as_finprod:
  assumes "set xs \<subseteq> carrier G"
  shows "listprod G xs = finprod G (nth xs) {..<length xs}"
  apply (insert assms, induct xs, auto simp: lessThan_Suc_eq_insert_0)
  apply (subst finprod_insert)
  apply (auto intro!: nth_ConsI[of _ "\<lambda>x. x \<in> carrier G"])
  apply (subst finprod_reindex, auto)
  done

definition listsum where "listsum R \<equiv> listprod \<lparr> carrier = carrier R, mult = add R, one = zero R \<rparr>"

lemma listsum_Nil[simp]: "listsum R [] = zero R" by (auto simp: listsum_def)

lemma listsum_Cons[simp]: "listsum R (x#xs) = add R x (listsum R xs)" by (auto simp: listsum_def)

lemmas (in ring) listsum_as_finsum = add.listprod_as_finprod[folded listsum_def]


context IA_locale begin

definition "ring_Int \<equiv> \<lparr> carrier = range IA.Int, mult = (*), one = IA.Int 1, zero = IA.Int 0, add = (+) \<rparr>"

end

interpretation IA_ring_Int: Ring.ring "IA.ring_Int"
  rewrites [simp]: "carrier IA.ring_Int = range IA.Int"
    and [simp]: "mult IA.ring_Int = (*)"
    and [simp]: "one IA.ring_Int = IA.Int 1"
    and [simp]: "zero IA.ring_Int = IA.Int 0"
    and [simp]: "add IA.ring_Int = (+)"
    and [simp]: "Units IA.ring_Int = { IA.Int 1, IA.Int (-1) }"
  by (unfold_locales, auto simp: IA.ring_Int_def Units_def field_simps zmult_eq_1_iff intro: exI[of _ "-_"])

interpretation IA_Int_hom: plus_hom IA.Int by (unfold_locales, auto)

interpretation IA_Int_hom: ord_hom_strict IA.Int by (unfold_locales, auto)

lemma IA_Int_sum_list: "IA.Int (sum_list xs) = listsum IA.ring_Int (map IA.Int xs)"
  by (induct xs, auto simp:lessThan_Suc_eq_insert_0 IA_Int_hom.hom_add)

lemma listsum_IA:
  assumes "set vs \<subseteq> range IA.Int"
  shows "listsum IA.ring_Int vs = IA.Int (sum_list (map IA.to_int vs))"
  using IA_Int_sum_list[of "map IA.to_int vs"] assms map_idI[of vs "IA.Int \<circ> IA.to_int"] by force

end
