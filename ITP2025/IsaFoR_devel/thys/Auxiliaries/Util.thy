(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Util
imports
  Polynomial_Factorization.Missing_List 
  "HOL-Library.Infinite_Set"
  HOL.Archimedean_Field
  "Abstract-Rewriting.Relative_Rewriting"
  First_Order_Rewriting.FOR_Preliminaries
begin

lemma rtrancl_Id [simp]: "Id\<^sup>* = Id" 
  by (auto elim: rtrancl.induct)

lemma relpow_2 [simp]: "r ^^ 2 = r O r"
  by (metis Suc_1 relpow_1 relpow_Suc)

definition replace :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "replace a bs M \<equiv> if a \<in> M then M - {a} \<union> bs else M"

definition replace_impl :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_impl a bs M \<equiv> if a \<in> set M then bs @ filter (\<lambda> b. b \<noteq> a) M else M"

lemma replace_impl[simp]: "set (replace_impl a bs M) = replace a (set bs) (set M)"
  unfolding replace_impl_def replace_def by auto

declare map_option_cong[fundef_cong]

lemma infinite_inj_on_remove_one:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes inf: "infinite B"
  and inj: "inj_on f A"
  and ran: "range f \<subseteq> B"
  shows "\<exists> g. inj_on g A \<and> range g \<subseteq> B - {b}"
proof -
  from inf have inf: "infinite (B - {b})" by auto
  from infinite_imp_elem[OF inf] obtain b' where b': "b' \<in> B - {b}" by force
  from infinite_countable_subset[OF inf] obtain h :: "nat \<Rightarrow> 'b" where inj_h: "inj h" and ran_h: "range h \<subseteq> B - {b}" by auto
  let ?h = "\<lambda> a. h (Suc (the_inv h (f a)))"
  let ?f = "\<lambda> a. (if f a \<in> range h then ?h a else f a)"
  let ?g = "\<lambda> a. if f a = b then h 0 else if a \<in> A then ?f a else b'"
  show ?thesis
  proof (rule exI[of _ ?g], unfold inj_on_def, intro conjI ballI impI)
    fix a1 a2
    assume a1: "a1 \<in> A" and a2: "a2 \<in> A" and id: "?g a1 = ?g a2"
    show "a1 = a2"
    proof (cases "f a1 = b")
      case True
      with id have id: "?g a2 = h 0" and fa1: "f a1 = b" by auto
      show ?thesis
      proof (cases "f a2 = b")
        case True
        with fa1 id a1 a2 inj show ?thesis unfolding inj_on_def by auto
      next
        case False
        with id a2 have id: "?f a2 = h 0" by auto
        with inj_h show ?thesis unfolding inj_on_def by (cases "f a2 \<in> range h", auto)
      qed
    next
      case False
      with id a1 have id: "?f a1 = ?g a2" by auto
      show ?thesis
      proof (cases "f a2 = b")
        case True
        with id have "?f a1 = h 0" by auto
        with inj_h show ?thesis unfolding inj_on_def by (cases "f a1 \<in> range h", auto)
      next
        case False
        with id a2 have id: "?f a1 = ?f a2" by auto
        have "f a1 = f a2"
        proof (cases "f a1 \<in> range h")
          case True note r1 = this
          with id have id: "?f a2 = ?h a1" by simp
          then have r2: "f a2 \<in> range h" by (cases "f a2 \<in> range h", auto)
          with id have id: "?h a1 = ?h a2" by simp
          from r1 r2 obtain i1 i2 where h: "f a1 = h i1" "f a2 = h i2" by auto
          from id[unfolded h the_inv_f_f[OF inj_h]] have "h (Suc i1) = h (Suc i2)" .
          with inj_h have id: "i1 = i2" unfolding inj_on_def by auto
          with h show "f a1 = f a2" by auto
        next
          case False note r1 = this
          {
            assume "f a2 \<in> range h"
            with id have id: "?f a1 = ?h a2" by simp
            then have "f a1 \<in> range h" by (cases "f a1 \<in> range h", auto)
            with r1 have False by auto
          }
          with r1 id show ?thesis by auto
        qed
        with a1 a2 inj show ?thesis unfolding inj_on_def by auto
      qed
    qed
  next
    show "range ?g \<subseteq> B - {b}" using ran_h ran b' by auto
  qed
qed

lemma infinite_inj_on_finite_remove_finite:
  fixes f :: "'a \<Rightarrow> 'b" and B :: "'b set"
  assumes inf: "infinite B"
    and inj: "inj_on f A"
    and fin: "finite B'"
    and ran: "range f \<subseteq> B"
  shows "\<exists> g. inj_on g A \<and> range g \<subseteq> B - B'"
  using fin
proof (induct B')
  case empty
  show ?case using inj ran by auto
next
  case (insert b B')
  from insert(3) obtain g where inj: "inj_on (g :: 'a \<Rightarrow> 'b) A" and ran: "range g \<subseteq> B - B'" by auto
  from insert(1) inf have "infinite (B - B')" by auto
  from infinite_inj_on_remove_one[OF this inj ran, of b]
  show ?case by auto
qed

section \<open>Auxiliary Lemmas\<close>

lemma down_chain_imp_eq:
  fixes f :: "nat seq"
  assumes "\<forall>i. f i \<ge> f (Suc i)"
  shows "\<exists>N. \<forall>i > N. f i = f (Suc i)"
proof -
  let ?F = "{f i | i. True}"
  from wf_less [unfolded wf_eq_minimal, THEN spec, of ?F]
    obtain x where "x \<in> ?F" and *: "\<forall>y. y < x \<longrightarrow> y \<notin> ?F" by auto
  obtain N where "f N = x" using \<open>x \<in> ?F\<close> by auto
  moreover have "\<forall>i > N. f i \<in> ?F" by auto
  ultimately have "\<forall>i > N. \<not> f i < x" using * by auto
  moreover have "\<forall>i > N. f N \<ge> f i"
    using chainp_imp_rtranclp [of "(\<ge>)" f, OF assms] by simp
  ultimately have "\<forall>i > N. f i = f (Suc i)"
    using \<open>f N = x\<close> by (auto) (metis less_SucI order.not_eq_order_implies_strict)
  then show ?thesis ..
qed


fun max_f :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "max_f f 0 = 0"
| "max_f f (Suc i) = max (f i) (max_f f i)"

lemma max_f: "i < n \<Longrightarrow> f i \<le> max_f f n"
proof (induct n)
  case (Suc n)
  then show ?case by (cases "i = n", auto)
qed simp

lemma sum_list_take [simp]:
  "i < length (xs :: nat list) \<Longrightarrow> sum_list (take i xs) \<le> sum_list xs"
  by (induct xs arbitrary: i) (simp, case_tac i, auto)

lemma Max_le_Max:
  assumes X: "finite X" "X \<noteq> {}" and Y: "finite Y" "Y \<noteq> {}"
  shows "Max X \<le> Max Y \<longleftrightarrow> (\<forall>x\<in>X. \<exists>y\<in>Y. x \<le> y)"
  by (meson Max.boundedE Max_ge_iff Max_in assms)

lemma Max_less_Max:
  assumes X: "finite X" "X \<noteq> {}" and Y: "finite Y" "Y \<noteq> {}"
  shows "Max X < Max Y \<longleftrightarrow> (\<forall>x\<in>X. \<exists>y\<in>Y. x < y)"
  by (meson Max_less_iff assms eq_Max_iff less_le_trans)

lemma upt_append_upt: "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..<j] @ [j..<k] = [i..<k]"
  using upt_add_eq_append[of i j "k - j"] by auto

subsection \<open>size estimations\<close>

lemma size_list_pointwise2: assumes "length xs = length ys"
  and "\<And> i. i < length ys \<Longrightarrow> f (xs ! i) \<le> g (ys ! i)"
  shows "size_list f xs \<le> size_list g ys"
proof -
  have id: "(size_list f xs \<le> size_list g ys) = (sum_list (map f xs) \<le> sum_list (map g ys))"
    unfolding size_list_conv_sum_list assms(1) by auto
  have "map f xs = map f (map ((!) xs) [0..<length xs])" using map_nth[of xs] by simp
  also have "... = map (\<lambda> i. f (xs ! i)) [0..<length xs]" (is "_ = ?xs") by simp
  finally have xs: "map f xs = ?xs" .
  have "map g ys = map g (map ((!) ys) [0..<length ys])" using map_nth[of ys] by simp
  also have "... = map (\<lambda> i. g (ys ! i)) [0..<length xs]" (is "_ = ?ys") using assms by simp
  finally have ys: "map g ys = ?ys" .
  show ?thesis
    unfolding id unfolding xs ys
    by (rule sum_list_mono, insert assms, auto)
qed

lemma size_list_pointwise3: assumes len: "length xs = length ys"
  and xs: "xs \<noteq> []"
  and lt: "\<And> i. i < length ys \<Longrightarrow> f (xs ! i) < g (ys ! i)"
  shows "size_list f xs < size_list g ys"
proof -
  from xs obtain x xs' where xs: "xs = x # xs'" by (cases xs, auto)
  with len obtain y ys' where ys: "ys = y # ys'" by (cases ys, auto)
  have "size_list f xs = f x + 1 + size_list f xs'" by (simp add: xs)
  also have "size_list f xs' \<le> size_list g ys'"
  proof (rule size_list_pointwise2)
    fix i
    assume "i < length ys'"
    then have "Suc i < length ys" unfolding ys by simp
    from lt[OF this]
    show "f (xs' ! i) \<le> g (ys' ! i)" unfolding xs ys by auto
  qed (insert len xs ys, simp)
  also have "f x < g y" using lt[of 0] unfolding xs ys by simp
  also have "g y + 1 + size_list g ys' = size_list g ys" unfolding ys by simp
  finally show ?thesis by arith
qed

subsection \<open>assignments from key-value pairs\<close>

fun enum_vectors :: "'c list \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'c)list list"
where "enum_vectors C [] = [[]]"
    | "enum_vectors C (x # xs) = (let rec = enum_vectors C xs in concat (map (\<lambda> vec. map (\<lambda> c. (x,c) # vec) C) rec))"

definition fun_of :: "('v \<times> 'c) list \<Rightarrow> 'v \<Rightarrow> 'c" where
  [simp]: "fun_of vec x = the (map_of vec x)"

lemma enum_vectors_complete:
  assumes "C \<noteq> []"
  shows "\<exists> vec \<in> set (enum_vectors C xs). \<forall> x \<in> set xs. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c"
proof (induct xs, simp)
  case (Cons x xs)
  from this obtain vec where enum: "vec \<in> set (enum_vectors C xs)" and eq: "\<forall> x \<in> set xs. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c" by auto
  from enum have res: "set (map (\<lambda> c. (x,c) # vec) C) \<subseteq> set (enum_vectors C (x # xs)) " (is "_ \<subseteq> ?res") by auto
  show ?case
  proof (cases "\<alpha> x \<in> set C")
    case False
    from assms have "hd C \<in> set C" by auto
    with res have elem: "(x,hd C) # vec \<in> ?res" (is "?vec \<in> _") by auto
    from eq False have "\<forall> y \<in> set (x # xs). \<forall> c \<in> set C. \<alpha> y = c \<longrightarrow> fun_of ?vec y = c" by auto
    with elem show ?thesis by blast
  next
    case True
    with res have elem: "(x, \<alpha> x) # vec \<in> ?res" (is "?vec \<in> _") by auto
    from eq True have "\<forall> y \<in> set (x # xs). \<forall> c \<in> set C. \<alpha> y = c \<longrightarrow> fun_of ?vec y = c" by auto
    with elem show ?thesis by blast
  qed
qed

lemma enum_vectors_sound:
  assumes "y \<in> set xs" and "vec \<in> set (enum_vectors C xs)"
  shows "fun_of vec y \<in> set C"
  using assms
proof (induct xs arbitrary: vec, simp)
  case (Cons x xs vec)
  from Cons(3) obtain v vecc where vec: "vec = v # vecc" by auto
  note C3 = Cons(3)[unfolded vec enum_vectors.simps Let_def]
  from C3 have vecc: "vecc \<in> set (enum_vectors C xs)" by auto
  from C3 obtain c where v: "v = (x,c)" and c: "c \<in> set C" by auto
  show ?case
  proof (cases "y = x")
    case True
    show ?thesis unfolding vec v True using c by auto
  next
    case False
    with Cons(2) have y: "y \<in> set xs" by auto
    from False have id: "fun_of vec y = fun_of vecc y"
      unfolding vec v by auto
    show ?thesis unfolding id
      by (rule Cons(1)[OF y vecc])
  qed
qed

declare fun_of_def[simp del]

lemma map_of_nth_zip_Some [simp]:
  assumes "distinct vs" and "length vs \<le> length ts" and "i < length vs"
  shows "map_of (zip vs ts) (vs ! i) = Some (ts ! i)"
using assms proof (induct i arbitrary: vs ts)
  case 0 then show ?case by (induct ts) (induct vs, auto)+
next
  case (Suc i) show ?case
  proof (cases ts)
    case Nil with Suc show ?thesis unfolding Nil by simp
  next
    case (Cons t ts')
    note Cons' = this
    show ?thesis
    proof (cases vs)
      case Nil from Suc show ?thesis unfolding Cons' Nil by simp
    next
      case (Cons v vs') from Suc show ?thesis unfolding Cons Cons' by auto
    qed
  qed
qed

lemma fun_of_concat:
  assumes mem: "x \<in> set (map fst (\<tau>s i))"
    and i: "i < n"
    and ident: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> x \<in> set (map fst (\<tau>s i)) \<Longrightarrow> x \<in> set (map fst (\<tau>s j)) \<Longrightarrow> fun_of (\<tau>s i) x = fun_of (\<tau>s j) x"
  shows "fun_of (concat (map \<tau>s [0..<n])) x = fun_of (\<tau>s i) x"
using assms
proof (induct n arbitrary: i \<tau>s)
  case 0
  then show ?case by simp
next
  case (Suc n i \<tau>s) note IH = this
  let ?\<tau>s = "\<lambda>i. \<tau>s (Suc i)"
  have id: "concat (map \<tau>s [0..<Suc n]) = \<tau>s 0 @ concat (map ?\<tau>s [0..<n])" unfolding map_upt_Suc by simp
  let ?l = "map_of (\<tau>s 0) x"
  show ?case
  proof (cases i)
    case 0
    with IH(2) have x: "x \<in> set (map fst (\<tau>s 0))" by auto
    then obtain y where xy: "(x,y) \<in> set (\<tau>s 0)" by auto
    from map_of_eq_None_iff[of "\<tau>s 0" x] xy have "?l \<noteq> None" by force
    then obtain y where look: "?l = Some y" by (cases "\<tau>s 0", auto)
    show ?thesis unfolding 0 fun_of_def id look map_of_append_Some[OF look] by simp
  next
    case (Suc j)
    with IH(3)
    have 0: "0 < i" and j: "j < n" by auto
    show ?thesis
    proof (cases "x \<in> set (map fst (\<tau>s 0))")
      case False
      have l: "?l = None"
      proof (cases "?l")
        case (Some y)
        from map_of_SomeD[OF this] and False show ?thesis by force
      qed simp
      show ?thesis unfolding fun_of_def id map_of_append_None[OF l]
        unfolding fun_of_def[symmetric] Suc
      proof (rule IH(1)[OF _ j])
        show "x \<in> set (map fst (\<tau>s (Suc j)))" using IH(2) unfolding Suc .
      next
        fix i j
        assume "i < n" and "j < n" and "x \<in> set (map fst (\<tau>s (Suc i)))" and "x \<in> set (map fst (\<tau>s (Suc j)))"
        then show "fun_of (\<tau>s (Suc i)) x = fun_of (\<tau>s (Suc j)) x"
          using IH(4)[of "Suc i" "Suc j"] by auto
      qed
    next
      case True
      then obtain y where xy: "(x,y) \<in> set (\<tau>s 0)" by auto
      from map_of_eq_None_iff[of "\<tau>s 0" x] and xy have "?l \<noteq> None" by force
      then obtain y where look: "?l = Some y" by (cases "\<tau>s 0", auto)
      have "fun_of (concat (map \<tau>s [0..<Suc n])) x = fun_of (\<tau>s 0) x"
        unfolding id fun_of_def look
        map_of_append_Some[OF look] by simp
      also have "... = fun_of (\<tau>s i) x"
      proof (rule IH(4)[OF _ IH(3)])
        from xy show "x \<in> set (map fst (\<tau>s 0))" by force
      next
        from IH(2) show "x \<in> set (map fst (\<tau>s i))" by force
      qed simp
      finally show ?thesis .
    qed
  qed
qed

lemma fun_of_concat_part: assumes mem: "x \<in> set (map fst (\<tau>s i))"
  and i: "i < n"
  and partition: "is_partition (map (\<lambda> i. set (map fst (\<tau>s i))) [0..<n])"
  shows "fun_of (concat (map \<tau>s [0..<n])) x = fun_of (\<tau>s i) x"
proof (rule fun_of_concat, rule mem, rule i)
  fix i j
  assume "i < n" and "j < n" and "x \<in> set (map fst (\<tau>s i))" and "x \<in> set (map fst (\<tau>s j))"
  then have "i = j" using partition[unfolded is_partition_alt is_partition_alt_def] by (cases "i = j", auto)
  then show "fun_of (\<tau>s i) x = fun_of (\<tau>s j) x" by simp
qed

lemma fun_of_concat_merge:
  assumes "\<And> i. i < length ts \<Longrightarrow> x \<in> h (ts ! i) \<Longrightarrow> fun_of (f i) x = (g ! i) x"
    and "length ts = length g"
    and "\<And> i. i < length ts \<Longrightarrow> map_of (f i) x \<noteq> None \<longleftrightarrow> x \<in> h (ts ! i)"
    and "x \<in> h (ts ! i)"
    and "i < length ts"
  shows "fun_of (concat (map f [0..<length ts])) x = fun_merge g (map h ts) x"
  using assms
  unfolding fun_merge_def fun_of_def
proof (induct ts arbitrary: i f g)
  case Nil
  then show ?case by simp
next
  case (Cons xy ts)
  let ?p' = "\<lambda> ts i. i < length (map h ts) \<and> x \<in> map h ts ! i"
  let ?p = "?p' (xy # ts)"
  let ?P = "?p' ts"
  let ?L = "LEAST i. ?p i"
  have id: "the (map_of (concat (map f [0..<length (xy # ts)])) x) =
    the (map_of (f 0 @ concat (map (\<lambda> i. f (Suc i)) [0..<length ts])) x)"
    (is "?l = the (map_of ( _ @ ?l') x)")
    by (simp add: map_upt_Suc del: upt_Suc)
  show ?case
  proof (cases "map_of (f 0) x")
    case (Some y)
    from map_of_append_Some[OF Some]
    have ly: "?l = y" unfolding id Some by simp
    have "?p 0" using Cons(4)[of 0] using Some by auto
    then have L0: "?L = 0"
      by (rule Least_equality, simp)
    from Cons(4)[of 0] Some have x: "x \<in> h xy" by auto
    show ?thesis unfolding ly L0 using Cons(2)[of 0, unfolded Some] x by simp
  next
    case None
    from map_of_append_None[OF None]
    have ll: "?l = the (map_of ?l' x)" unfolding id by simp
    from Cons(4)[of 0] None have x: "x \<notin> h xy" by auto
    then have p0: "\<not> ?p 0" by simp
    from Cons(5) Cons(6) have pI: "?p i" unfolding nth_map[OF Cons(6)] by simp
    from Least_Suc[of ?p, OF pI p0] have L: "?L = Suc (LEAST m. ?P m)" by simp
    from Cons(3) obtain a g' where g: "g = a # g'" by (cases g, auto)
    from Cons(5) x obtain j where i: "i = Suc j" by (cases i, auto)
    show ?thesis unfolding ll L g nth_Cons_Suc
    proof (rule Cons(1))
      from g Cons(3) show "length ts = length g'" by auto
    next
      from Cons(5) i show "x \<in> h (ts ! j)" by auto
    next
      from Cons(6) i show "j < length ts" by auto
    next
      fix m
      assume "m < length ts"
      then show "map_of (f (Suc m)) x \<noteq> None \<longleftrightarrow> x \<in> h (ts ! m)"
        using Cons(4)[of "Suc m"] by auto
    next
      fix m
      assume "m < length ts" and "x \<in> h (ts ! m)"
      then show "the (map_of (f (Suc m)) x) = (g' ! m) x"
        using Cons(2)[of "Suc m"] unfolding g by auto
    qed
  qed
qed

context
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R :: "'a rel"
  and R' :: "'b rel"
  assumes simulate: "\<And> s t s'. P s t \<Longrightarrow> (s,s') \<in> R \<Longrightarrow> \<exists> t'. P s' t' \<and> (t,t') \<in> R'"
begin
lemma simulate_conditional_steps_count: assumes steps: "(s,s') \<in> R^^n"
  and P: "P s t"
  shows "\<exists> t'. P s' t' \<and> (t,t') \<in> R'^^n"
  using steps
proof (induct n arbitrary: s')
  case 0
  with P show ?case by auto
next
  case (Suc n s'')
  from Suc(2) obtain s' where ss': "(s,s') \<in> R^^n" and ss'': "(s',s'') \<in> R" by auto
  from Suc(1)[OF ss'] obtain t' where tt': "(t, t') \<in> R' ^^ n" and P: "P s' t'" by auto
  from simulate[OF P ss''] tt' show ?case by auto
qed

lemma simulate_conditional_steps: assumes steps: "(s,s') \<in> R\<^sup>*"
  and P: "P s t"
  shows "\<exists> t'. P s' t' \<and> (t,t') \<in> R'\<^sup>*"
proof -
  from steps obtain n where "(s,s') \<in> R^^n" by auto
  from simulate_conditional_steps_count[OF this P]
  show ?thesis by (blast intro: relpow_imp_rtrancl)
qed
end

context
  fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and R S :: "'a rel"
  and R' S' :: "'b rel"
  assumes simulateR: "\<And> s t s'. P s t \<Longrightarrow> (s,s') \<in> R \<Longrightarrow> \<exists> t'. P s' t' \<and> (t,t') \<in> R'"
  and simulateS: "\<And> s t s'. P s t \<Longrightarrow> (s,s') \<in> S \<Longrightarrow> \<exists> t'. P s' t' \<and> (t,t') \<in> S'"
begin
lemma simulate_conditional_relative_step: assumes step: "(s,s') \<in> relto R S"
  and P: "P s t"
  shows "\<exists> t'. P s' t' \<and> (t,t') \<in> relto R' S'"
proof -
  from step obtain u v where su: "(s,u) \<in> S\<^sup>*" and uv: "(u,v) \<in> R" and vs': "(v,s') \<in> S\<^sup>*" by auto
  have "\<exists> u'. P u u' \<and> (t,u') \<in> S'\<^sup>*"
    by (rule simulate_conditional_steps[of P, OF simulateS su P])
  then obtain u' where P: "P u u'" and tu: "(t,u') \<in> S'\<^sup>*" by blast
  from simulateR[OF P uv] obtain v' where P: "P v v'" and uv: "(u',v') \<in> R'" by auto
  have "\<exists> t'. P s' t' \<and> (v',t') \<in> S'\<^sup>*"
    by (rule simulate_conditional_steps[of P, OF simulateS vs' P])
  then obtain t' where P: "P s' t'" and vt: "(v',t') \<in> S'\<^sup>*" by blast
  from tu uv vt have "(t,t') \<in> relto R' S'" by auto
  with P show ?thesis by auto
qed

lemma simulate_conditional_relative_steps_count: assumes step: "(s,s') \<in> (relto R S)^^n"
  and P: "P s t"
  shows "\<exists> t'. P s' t' \<and> (t,t') \<in> (relto R' S')^^n"
  by (rule simulate_conditional_steps_count[of P, OF simulate_conditional_relative_step step P])
end

locale relative_simulation_image =
  fixes S :: "'a rel" and N :: "'a rel" and B :: "'b rel" and f :: "'a \<Rightarrow> 'b"
  assumes S: "(x,y) \<in> S \<Longrightarrow> (f x, f y) \<in> B^+"
  and N: "(x,y) \<in> N \<Longrightarrow> (f x, f y) \<in> B\<^sup>*"
begin

lemma many_non_strict: "(x,y) \<in> N\<^sup>* \<Longrightarrow> (f x, f y) \<in> B\<^sup>*"
proof (induct rule: rtrancl_induct)
  case (step y z)
  from step(3) N[OF step(2)] show ?case by auto
qed auto

lemma single_relative: assumes step: "(x,y) \<in> relto S N" shows "(f x, f y) \<in> B^+"
proof -
  from step obtain u v where xu: "(x,u) \<in> N\<^sup>*" and uv: "(u,v) \<in> S" and vy: "(v,y) \<in> N\<^sup>*" by blast
  from many_non_strict[OF xu] S[OF uv] many_non_strict[OF vy] show ?thesis by auto
qed

lemma count_relative: "(x,y) \<in> (relto S N)^^n \<Longrightarrow> \<exists> m \<ge> n. (f x, f y) \<in> B^^m"
proof (induct n arbitrary: x y)
  case (Suc n x y)
  let ?R = "relto S N"
  from Suc(2) obtain u where xu: "(x,u) \<in> ?R ^^ n" and uy: "(u,y) \<in> ?R" by auto
  from single_relative[OF uy]
  obtain n1 where n1: "n1 > 0" and uy: "(f u, f y) \<in> B ^^ n1" unfolding trancl_power by blast
  from Suc(1)[OF xu] obtain m where m: "m \<ge> n" and xu: "(f x, f u) \<in> B^^m" by auto
  from xu uy have xy: "(f x, f y) \<in> B^^(m + n1)" unfolding relpow_add by blast
  from m n1 have n: "m + n1 \<ge> Suc n" by auto
  from xy n show ?case by auto
next
  case 0
  then show ?case by (intro exI[of _ 0], auto)
qed
end

lemma rtrancl_map:
  assumes simu: "\<And>x y. (x, y) \<in> r \<Longrightarrow> (f x, f y) \<in> s"
    and steps: "(x, y) \<in> r\<^sup>*"
  shows "(f x, f y) \<in> s\<^sup>*"
  by (rule relative_simulation_image.many_non_strict[of "{}", OF _ steps], unfold_locales, insert simu, auto)

context
begin

private fun simulate :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "simulate R P s 0 = s"
| "simulate R P s (Suc n) = (SOME u. (simulate R P s n,u) \<in> R \<and> P u)"

lemma conditional_steps_imp_not_SN_on: assumes start: "P s"
  and step: "\<And> t. P t \<Longrightarrow> \<exists> u. (t,u) \<in> R \<and> P u"
  shows "\<not> SN_on R {s}"
proof -
  let ?sim = "simulate R P s"
  {
    fix i
    have "P (?sim i) \<and> (i > 0 \<longrightarrow> (?sim (i - 1), ?sim i) \<in> R)"
    proof (induct i)
      case 0 show ?case using start by auto
    next
      case (Suc i)
      then have P: "P (?sim i)" by simp
      from someI_ex[OF step[OF P]]
      show ?case by auto
    qed
  } note main = this
  define g where "g = ?sim"
  have "g 0 = s" unfolding g_def by simp
  {
    fix i
    from main[of "Suc i"]
    have "(g i, g (Suc i)) \<in> R" unfolding g_def by auto
  }
  with \<open>g 0 = s\<close> show ?thesis by auto
qed
end

lemma image_Pair_Un_imp_eq:
  assumes "a \<noteq> b"
    and "Pair a ` A \<union> Pair b ` B = Pair a ` C \<union> Pair b ` D"
  shows "A = C \<and> B = D"
proof (rule ccontr)
  presume "A \<noteq> C \<or> B \<noteq> D"
  then show False
  proof
    assume "A \<noteq> C"
    then obtain x where "x \<in> (A - C) \<or> x \<in> (C - A)" by auto
    then show False by (rule disjE) (insert assms, auto)
  next
    assume "B \<noteq> D"
    then obtain y where "y \<in> (B - D) \<or> y \<in> (D - B)" by auto
    then show False by (rule disjE) (insert assms, auto)
  qed
qed simp

lemma image_Pair_Un_eq[simp]:
  "a \<noteq> b \<Longrightarrow> Pair a ` A \<union> Pair b ` B = Pair a ` C \<union> Pair b ` D \<longleftrightarrow> A = C \<and> B = D"
  using image_Pair_Un_imp_eq[of a b A B C D] by blast

lemma inj_Pair1: "inj (Pair a)" unfolding inj_on_def by auto

lemma Pair_image_diff_simps[simp]:
  "a \<noteq> b \<Longrightarrow> (Pair a ` A \<union> Pair b ` B) - (Pair a ` C) = (Pair a ` A - Pair a ` C) \<union> Pair b ` B"
  "a \<noteq> b \<Longrightarrow> (Pair a ` A \<union> Pair b ` B) - (Pair b ` C) = Pair a ` A \<union> (Pair b ` B - Pair b ` C)"
  "a \<noteq> b \<Longrightarrow> (Pair a ` A \<union> (Pair b ` B - Pair b ` C)) - Pair a ` D =
    (Pair a ` A - Pair a ` D) \<union> (Pair b ` B - Pair b ` C)"
  by auto

lemma Collect_Un: "{x \<in> A \<union> B. P x} = {x \<in> A. P x} \<union> {x \<in> B. P x}" by auto
lemma image_snd_Pair: "snd ` {x \<in> Pair a ` A. P x} = {x \<in> A. P (a, x)}" by force
lemma Collect_nested_conj: "{x \<in> {x \<in> A. P x}. Q x} = {x \<in> A. P x \<and> Q x}" by simp
lemma image_snd_Pair_Un[simp]: "snd ` (Pair x ` A \<union> (Pair y ` B)) = A \<union> B" by force

(*FIXME: move to Map.thy*)
lemma ran_map_upd_Some:
  assumes "m a = Some b"
  shows "ran (m(a \<mapsto> c)) \<subseteq> insert c (ran m)"
proof
  fix x assume "x \<in> ran (m(a \<mapsto> c))"
  then obtain k where upd: "(m(a \<mapsto> c)) k = Some x" by (auto simp: ran_def)
  show "x \<in> insert c (ran m)"
  proof (cases "a = k")
    case True
    from assms and upd have x: "x = c" by (simp add: True)
    then show ?thesis by simp
  next
    case False
    then have m_upd: "(m(a \<mapsto> c)) k = m k" by simp
    from upd[unfolded m_upd] have "x \<in> ran m" by (auto simp: ran_def)
    then show ?thesis by simp
  qed
qed

(*FIXME: move to Map.thy?*)
lemma subset_UNION_ran:
  assumes "m a = Some b"
    and "set b \<subseteq> set c"
  shows "\<Union> (set ` (ran (m(a \<mapsto> c)))) = \<Union> (set ` (insert c (ran m)))" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix x assume "x \<in> ?l"
    then obtain rs where rs: "rs \<in> ran (m(a \<mapsto> c))" and x: "x \<in> set rs" by auto
    from ran_map_upd_Some[of m a b c, OF assms(1)] and rs
      have "rs \<in> insert c (ran m)" by blast
    with x show "x \<in> ?r" by auto
  qed
next
  show "?r \<subseteq> ?l"
  proof
    fix x assume "x \<in> ?r"
    then obtain rs where "rs \<in> insert c (ran m)" and x: "x \<in> set rs" by auto
    then have "c = rs \<or> rs \<in> ran m" by auto
    then show "x \<in> ?l"
    proof
      assume c: "c = rs"
      show ?thesis unfolding c using x by (auto simp: ran_def)
    next
      assume "rs \<in> ran m"
      then obtain k where mk: "m k = Some rs" by (auto simp: ran_def)
      show  ?thesis
      proof (cases "a = k")
        case True
        from assms(1) and mk have rs: "rs = b" by (simp add: True)
        with assms(2) and x show ?thesis by (auto simp: ran_def)
      next
        case False
        with mk have "rs \<in> ran (m(a \<mapsto> c))" by (auto simp: ran_def)
        with x show ?thesis by blast
      qed
    qed
  qed
qed

locale abstract_closure =
  fixes A B C :: "'a rel" and S :: "'a set" and P :: "'a \<Rightarrow> bool"
  assumes S: "\<And> a b. a \<in> S \<Longrightarrow> (a,b) \<in> C\<^sup>* \<Longrightarrow> P b"
  and AC: "A \<subseteq> C\<^sup>*"
  and PAB: "\<And> a b. P a \<Longrightarrow> P b \<Longrightarrow> (a,b) \<in> A \<Longrightarrow> (a,b) \<in> B"
begin

lemma A_steps_imp_P: assumes a: "a \<in> S"
  and rel: "(a,b) \<in> A^^n" shows "P b"
proof -
  from relpow_imp_rtrancl[OF rel] rtrancl_mono[OF AC] have "(a,b) \<in> C\<^sup>*" by auto
  from S[OF a this] show ?thesis .
qed

lemma A_steps_imp_B_steps_count: assumes a: "a \<in> S"
  shows "(a,b) \<in> A^^n \<Longrightarrow> (a,b) \<in> B^^n"
proof (induct n arbitrary: b)
  case (Suc n c)
  from Suc(2) obtain b where ab: "(a,b) \<in> A^^n" and bc: "(b,c) \<in> A" by auto
  from Suc(1)[OF ab] have abB: "(a,b) \<in> B^^n" .
  with PAB[OF A_steps_imp_P[OF a ab] A_steps_imp_P[OF a Suc(2)] bc]
  show ?case by auto
qed auto

lemma A_steps_imp_B_steps: assumes a: "a \<in> S"
  shows "(a,b) \<in> A\<^sup>* \<Longrightarrow> (a,b) \<in> B\<^sup>*"
using A_steps_imp_B_steps_count[OF a, of b] unfolding rtrancl_is_UN_relpow by auto
end

locale abstract_closure_twice = abstract_closure +
  fixes A' B' :: "'a rel"
  assumes AC': "A' \<subseteq> C\<^sup>*"
  and PAB': "\<And> a b. P a \<Longrightarrow> P b \<Longrightarrow> (a,b) \<in> A' \<Longrightarrow> (a,b) \<in> B'"
begin
lemma AA_steps_imp_P: assumes a: "a \<in> S"
  and steps: "(a,b) \<in> (A \<union> A')\<^sup>*" shows "P b"
proof -
  from AC AC' have "A \<union> A' \<subseteq> C\<^sup>*" by auto
  from rtrancl_mono[OF this] steps have "(a,b) \<in> C\<^sup>*" by auto
  from S[OF a this] show ?thesis .
qed

lemma shift_closure: assumes a: "a \<in> S"
  and ab: "(a,b) \<in> (A \<union> A')\<^sup>*"
  shows "abstract_closure_twice A B C {b} P A' B'"
proof -
  {
    fix c
    assume bc: "(b,c) \<in> C\<^sup>*"
    from AC AC' have "(A \<union> A') \<subseteq> C\<^sup>*" by auto
    from ab rtrancl_mono[OF this] have ab: "(a,b) \<in> C\<^sup>*" by auto
    with bc have "(a,c) \<in> C\<^sup>* O C\<^sup>*" by auto
    also have "\<dots> \<subseteq> C\<^sup>*" by regexp
    finally have "P c" by (rule S[OF a])
  } note P = this
  show ?thesis
    by (unfold_locales, insert P AC' PAB' AC PAB, auto)
qed

lemma AA_step_imp_BB_step: assumes a: "a \<in> S"
  and steps: "(a,b) \<in> relto A A'" shows "(a,b) \<in> relto B B'"
proof -
  interpret alt: abstract_closure_twice A' B' C S P A B
    by (unfold_locales, insert S AC' PAB' AC PAB, auto)
  from steps obtain c d where ac: "(a,c) \<in> A'\<^sup>*" and cd: "(c,d) \<in> A" and db: "(d,b) \<in> A'\<^sup>*" by blast
  from alt.A_steps_imp_B_steps[OF a ac] have ac': "(a,c) \<in> B'\<^sup>*" by auto
  from AA_steps_imp_P[OF a] have P: "\<And> b. (a,b) \<in> (A \<union> A')\<^sup>* \<Longrightarrow> P b" .
  have ac: "(a,c) \<in> (A \<union> A')\<^sup>*" using ac by regexp
  have "(a,d) \<in> (A \<union> A')\<^sup>* O A" using ac cd by auto
  also have "\<dots> \<subseteq> (A \<union> A')\<^sup>*" by regexp
  finally have ad: "(a,d) \<in> (A \<union> A')\<^sup>*" .
  from PAB[OF P[OF ac] P[OF ad] cd] have cd': "(c,d) \<in> B" .
  interpret alt2: abstract_closure_twice A' B' C "{d}" P A B
    by (rule alt.shift_closure[OF a], insert ad, simp add: ac_simps)
  from alt2.A_steps_imp_B_steps[OF _ db] have db': "(d,b) \<in> B'\<^sup>*" by simp
  from ac' cd' db' show ?thesis by blast
qed

lemma AA_steps_imp_BB_steps: assumes a: "a \<in> S"
  and steps: "(a,b) \<in> (relto A A')^^n" shows "(a,b) \<in> (relto B B')^^n"
  using steps
proof (induct n arbitrary: b)
  case (Suc n c)
  from Suc(2) obtain b where ab: "(a,b) \<in> (relto A A')^^n" and bc: "(b,c) \<in> relto A A'" by auto
  from Suc(1)[OF ab] have ab': "(a,b) \<in> (relto B B')^^n" by auto
  from relpow_imp_rtrancl[OF ab] have ab: "(a,b) \<in> (A \<union> A')\<^sup>*" by regexp
  interpret alt: abstract_closure_twice A B C "{b}" P A' B'
    by (rule shift_closure[OF a ab])
  from alt.AA_step_imp_BB_step[OF _ bc] have bc: "(b,c) \<in> relto B B'" by simp
  from ab' bc show ?case by auto
qed simp
end

lemma find_distinct:
  assumes "distinct (map f xs)"
  shows "find (\<lambda>x. z = f x) xs = Some x \<longleftrightarrow> z = f x \<and> x \<in> set xs"
        "find (\<lambda>x. z = f x) xs = None   \<longleftrightarrow> z \<notin> f ` set xs"
  using assms by (induct xs) auto

lemma max_list_leI: assumes "\<And> x. x \<in> set xs \<Longrightarrow> x \<le> k"
  shows "max_list xs \<le> k" 
  using assms
  by (induct xs, auto)

lemma remove_map: "j < length xs \<Longrightarrow> remove_nth j (map f xs) = map f (remove_nth j xs)"
  unfolding remove_nth_def by (auto simp: take_map drop_map)

end
