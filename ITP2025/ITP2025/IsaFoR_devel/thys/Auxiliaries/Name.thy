(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Name
imports
  Show.Number_Parser
  "HOL-Library.Infinite_Set"
  Util
  Fresh_Identifiers.Fresh
begin

lemma distinct_mem: assumes "distinct xs"
  shows "length xs - length ys \<le> length (filter (\<lambda> s. \<not> s \<in> set ys) xs)"
using assms 
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  then have dist: "distinct xs" by auto
  show ?case
  proof (cases "x \<in> set ys")
    case False
    from dist Cons have "length xs - length ys \<le> length [s\<leftarrow>xs . \<not> s \<in> set ys]" by auto
    with False show ?thesis by auto
  next
    case True
    let ?ys = "remove1 x ys"
    from True Cons have nomem: "x \<notin> set xs" by auto
    from dist Cons have len1: "length xs - length ?ys \<le> length [s\<leftarrow>xs . \<not> s \<in> set ?ys]" by auto
    from True have len2: "length ys - 1 = length ?ys" by (simp add: length_remove1)
    from True obtain n where "length ys = Suc n" by (cases ys, auto) 
    with len2 have len3: "length ys = Suc (length ?ys)" by auto
    with len1 have len: "length (x # xs) - length ys \<le> length [s\<leftarrow>xs. \<not> s \<in> set ?ys]" by auto
    from nomem have "[s\<leftarrow>xs . \<not> s \<in> set (remove1 x ys)] = [s\<leftarrow>xs . \<not> s \<in> set ys]" 
    proof (induct xs)
      case (Cons xx xs)
      then show ?case by (cases "x = xx", auto)
    qed simp
    with len show ?thesis by auto
  qed
qed simp


section \<open>A Type Class for Name Generators\<close>

class name_gen =
  fixes fresh_name :: "'a set \<Rightarrow> 'a"
  assumes fresh: "finite S \<Longrightarrow> fresh_name S \<notin> S"
begin

fun
  fresh_names :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "fresh_names S 0 = []" |
  "fresh_names S (Suc n) = fresh_name S # fresh_names ({fresh_name S} \<union> S) n"

fun
  fresh_names_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "fresh_names_list used 0 = []" |
  "fresh_names_list used (Suc n) = (
    let new = fresh_name (set used)
    in new # fresh_names_list (new # used) n)"

lemma fresh_names_list_sound: "fresh_names_list xs n = fresh_names (set xs) n"
by (induct n arbitrary: xs) (auto simp: Let_def)

lemma fresh_names_length:
  assumes "finite S" shows "length (fresh_names S n) = n"
using assms by (induct n arbitrary: S) auto

lemma fresh_names_list_length: "length (fresh_names_list used n) = n"
by (induct n arbitrary: used) (auto simp: Let_def)

lemma fresh_names_list_fresh:
  assumes "set xs \<subseteq> set ys"
  shows "set (fresh_names_list ys n) \<inter> set xs = {}"
using assms proof (induct n arbitrary: ys)
  case 0 show ?case by simp
next
  case (Suc n)
  then have IH: "set (fresh_names_list ys n) \<inter> set xs = {}" .
  let ?new = "fresh_name (set ys)"
  let ?ys = "?new # ys"
  have "set ys \<subseteq> set ?ys" by auto
  with Suc have "set (fresh_names_list ?ys n) \<inter> set xs = {}" by simp
  moreover have "fresh_name (set ys) \<notin> set xs"
  proof -
    from fresh[of "set ys"] have "fresh_name (set ys) \<notin> set ys" by simp
    with \<open>set xs \<subseteq> set ys\<close> show ?thesis by blast
  qed
  ultimately show ?case by (simp add: Let_def)
qed

lemma fresh_names_fresh:
  assumes "finite T" and "S \<subseteq> T"
  shows "set (fresh_names T n) \<inter> S = {}"
proof -
  from finite_list[OF assms(1)] obtain ys
    where T: "T = set ys" by auto
  from finite_list[OF finite_subset[OF assms(2) assms(1)]] obtain xs
    where S: "S = set xs" by auto
  from fresh_names_list_fresh and assms[unfolded S T] show ?thesis
    unfolding S T fresh_names_list_sound by simp
qed

lemma fresh_names_list_distinct: "distinct (fresh_names_list xs n)"
proof (induct n arbitrary: xs)
  case 0 show ?case by simp
next
  case (Suc n)
  moreover have "fresh_name (set xs) \<notin> set (fresh_names_list (fresh_name (set xs) # xs) n)"
  proof -
    have "set [fresh_name (set xs)] \<subseteq> set (fresh_name (set xs) # xs)" by simp
    from fresh_names_list_fresh[OF this] show ?thesis by simp
  qed
  ultimately show ?case by (auto simp: Let_def)
qed

lemma fresh_names_dictinct:
  assumes "finite S"
  shows "distinct (fresh_names S n)"
proof -
  from finite_list[OF assms] obtain xs where S: "S = set xs" by auto
  from fresh_names_list_distinct
    show ?thesis unfolding fresh_names_list_sound S .
qed

end

subsection \<open>Name Generators\<close>
text \<open>a fresh name generator for creation
 of rules f(x_1,..,x_n) \<rightarrow> ...
 or for renaming variables apart, 
 etc.
\<close>
definition
  fresh_name_gen :: "('a set \<Rightarrow> nat \<Rightarrow> 'a list) \<Rightarrow> bool"
where
  "fresh_name_gen f \<equiv>
    \<forall>S n. finite S \<longrightarrow> length (f S n) = n \<and> set (f S n) \<inter> S = {} \<and> distinct (f S n)"

text \<open>Every @{term fresh_name_gen} gives rise to a class instance of @{text name_gen}\<close>
lemma fresh_name_gen_class_name_gen:
  fixes f :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list"
  defines "g xs \<equiv> hd (f xs 1)"
  assumes "fresh_name_gen f"
  shows "class.name_gen g"
proof
  fix S::"'a set"
  assume "finite S"
  with assms have len: "length (f S 1) = 1" and inter: "set (f S 1) \<inter> S = {}"
    unfolding fresh_name_gen_def by auto
  from len obtain x where fS1: "f S 1 = [x]" by (cases "f S 1") auto
  with inter have "x \<notin> S" by auto
  then show "g S \<notin> S" unfolding g_def fS1 by simp
qed

definition
  fresh_name_gen_list :: "('a list \<Rightarrow> nat \<Rightarrow> 'a list) \<Rightarrow> bool"
where
  "fresh_name_gen_list f \<equiv>
    \<forall>xs n. length (f xs n) = n \<and> set (f xs n) \<inter> set xs = {} \<and> distinct (f xs n)"

lemma fresh_name_gen_list_sound[simp]:
  fixes f :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list"
  shows "fresh_name_gen_list(f o set) = fresh_name_gen(f)" (is "?A = ?B")
proof
  assume assms: ?A show ?B
  unfolding fresh_name_gen_def o_def
  proof (intro allI impI)
    fix xs::"'a set" and n assume "finite xs"
    from finite_list[OF this]
      obtain ys where ys: "xs = set ys" by auto
    show "length(f xs n) = n \<and> set(f xs n) \<inter> xs = {} \<and> distinct(f xs n)"
      using assms unfolding ys fresh_name_gen_list_def o_def by simp
  qed
next
  assume assms: ?B show ?A
  unfolding fresh_name_gen_list_def
  proof (intro allI)
    fix xs n show "length((f o set) xs n) = n \<and>
      set((f o set) xs n) \<inter> set xs = {} \<and> distinct((f o set) xs n)"
      using assms unfolding fresh_name_gen_def o_def by auto
  qed
qed

definition
  fresh_strings :: "string \<Rightarrow> nat \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> string list"
where
  "fresh_strings name offset used n \<equiv>
     take n (filter (\<lambda>s. s \<notin> used) (map (\<lambda>i. name @ show (i + offset)) [0..< n + card used]))"

definition
  fresh_strings_list :: "string \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> nat \<Rightarrow> string list" 
where
  "fresh_strings_list name offset used n \<equiv>
     take n (filter (\<lambda>s. \<not> s \<in> set (remdups used)) (map (\<lambda>i. name @ show (i + offset)) [0..< n + length(remdups used)]))"

lemma fresh_name_gen_for_strings_list: "fresh_name_gen_list(fresh_strings_list name offset)"
unfolding fresh_name_gen_list_def fresh_strings_list_def
proof (intro allI)
  fix n :: nat and used :: "string list"
  let ?is = "[0 ..< n + length(remdups used)]"
  let ?fun = "\<lambda>i::nat. name @ show (i+offset)"
  let ?filt = "\<lambda>s. \<not> s \<in> set (remdups used)"
  let ?map = "map ?fun ?is"
  let ?fil = "filter ?filt ?map"
  have two: "set(take n ?fil) \<inter> set used = {}" (is "?f \<inter> ?u = {}")
  proof 
    show "{} \<subseteq> ?f \<inter> ?u" by auto
  next
    show "?f \<inter> ?u \<subseteq> {}"
    proof
      fix x
      assume "x \<in> ?f \<inter> ?u"
      then have "x \<in> set ?fil" using set_take_subset[where n = n and xs = ?fil] by blast
      then have "?filt x" by auto
      with \<open>x \<in> ?f \<inter> ?u\<close> have False by (auto)
      then show "x \<in> {}" ..
    qed
  qed
  {
    fix x y :: nat
    assume "show (x + offset) = show (y + offset)"
    with inj_show_nat have "x + offset = y + offset" unfolding inj_on_def by force
    then have "x = y" by auto
  }
  then have mapDist: "distinct ?map" 
    by (simp add: distinct_map inj_on_def)
  then have filDist: "distinct ?fil" by auto
  then have filFresh: "distinct (take n ?fil)" by auto
  have "length ?fil \<ge> n"
    using mapDist distinct_mem[where xs = ?map and ys = "remdups used"] by auto
  then have "length (take n ?fil) = n" by auto
  with filFresh two show "length(take n ?fil) = n \<and> set(take n ?fil) \<inter> set used = {}
    \<and> distinct (take n ?fil)" by blast
qed

definition fresh_string where "fresh_string pre \<equiv> \<lambda> s. hd (fresh_strings_list pre 1 s 1)"

lemma fresh_string: "fresh_string pre ss \<notin> set ss"
  using fresh_name_gen_for_strings_list[unfolded fresh_name_gen_list_def, rule_format, of pre 1 ss 1]
  unfolding fresh_string_def by (cases "fresh_strings_list pre 1 ss 1", auto)

lemma fresh_strings_list_sound[simp]:
  shows "fresh_strings_list name offset = fresh_strings name offset \<circ> set"
proof (intro ext)
  fix xs n show "fresh_strings_list name offset xs n = (fresh_strings name offset \<circ> set) xs n"
    unfolding fresh_strings_def fresh_strings_list_def o_def
    unfolding set_remdups by (simp add: length_remdups_card_conv)
qed

lemma fresh_name_gen_for_strings: "fresh_name_gen (fresh_strings name offset)"
  unfolding fresh_name_gen_list_sound[symmetric]
  unfolding fresh_strings_list_sound[symmetric]
  by (rule fresh_name_gen_for_strings_list)

interpretation string: name_gen "\<lambda>S. hd (fresh_strings [] 0 S 1)"
using fresh_name_gen_class_name_gen[of "fresh_strings [] 0", OF fresh_name_gen_for_strings] .

lemma finite_fresh_names_infinite_univ: fixes xs :: "'a set"
  assumes fin: "finite xs"
  and inf: "infinite (UNIV :: 'a set)"
  shows "\<exists> f g. (\<forall> x \<in> xs. f x \<notin> xs \<and> g (f x) = x)"
proof -
  let ?f = "\<lambda> xs :: 'a set. SOME f. f \<notin> xs"
  interpret name_gen ?f
  proof
    fix xs :: "'a set"
    assume xs: "finite xs"
    show "?f xs \<notin> xs"
      by (rule someI_ex, rule ex_new_if_finite[OF inf xs])
  qed
  from finite_list[OF fin] obtain F' where F': "set F' = xs" by auto
  obtain F where F: "F = remdups F'" by auto
  have distF: "distinct F" unfolding F by auto
  from F F' have F: "set F = xs" by auto
  obtain G where G: "G = fresh_names_list F (length F)" by auto
  from fresh_names_list_fresh[OF subset_refl] have fresh: "set G \<inter> set F = {}" unfolding G .
  from fresh_names_list_length have len: "length G = length F" unfolding G .
  from fresh_names_list_distinct have dist: "distinct G" unfolding G .
  let ?ishp = "\<lambda> f. SOME i. i < length F \<and> F ! i = f"
  let ?shp = "\<lambda> f. G ! ?ishp f"
  let ?iunshp = "\<lambda> g. SOME i. i < length G \<and> G ! i = g"
  let ?unshp = "\<lambda> g. F ! ?iunshp g"
  show ?thesis 
  proof (rule exI[of _ ?shp], rule exI[of _ ?unshp], intro ballI conjI)
    fix f 
    assume "f \<in> xs"
    then have f: "f \<in> set F" unfolding F by simp
    then obtain i where i: "i < length F \<and> F ! i = f" 
      unfolding set_conv_nth by auto
    have "?ishp f < length F \<and> F ! ?ishp f = f"
      by (rule someI, rule i)
    then have "?ishp f < length G" unfolding len by simp
    then have "?shp f \<in> set G" by auto
    with fresh have "?shp f \<notin> set F" by auto
    then show "?shp f \<notin> xs" unfolding F .
  next
    fix f 
    assume "f \<in> xs"
    then have f: "f \<in> set F" unfolding F by force
    then obtain i where i: "i < length F \<and> F ! i = f" 
      unfolding set_conv_nth by auto
    have i': "?ishp f < length F \<and> F ! ?ishp f = f"
      by (rule someI, rule i)
    from nth_eq_iff_index_eq[OF distF, of "?ishp f" i] i i'
    have i': "?ishp f = i" by auto
    from i have "i < length G" unfolding len by simp
    then have mem: "?shp f \<in> set G" unfolding i' by auto
    obtain sf where sf: "sf = ?shp f" by auto
    with mem have "sf \<in> set G" by simp
    then obtain j where j: "j < length G \<and> G ! j = sf" 
      unfolding set_conv_nth by blast
    have j': "?iunshp sf < length G \<and> G ! ?iunshp sf = sf"
      by (rule someI, rule j)
    from nth_eq_iff_index_eq[OF dist, of "?iunshp sf" j] j j'
    have j': "?iunshp sf = j" by auto    
    have "?unshp (?shp f) = ?unshp sf" unfolding sf by simp
    also have "... = F ! j" unfolding j' by simp
    finally have id: "?unshp (?shp f) = F ! j" .
    from j have Gj: "G ! j = sf" and jG: "j < length G" by auto
    from i i' len have iG: "?ishp f < length G" by simp
    from Gj[unfolded sf] have j: "j = ?ishp f"
      unfolding nth_eq_iff_index_eq[OF dist jG iG] .
    with i i' have id': "F ! j = f" by simp
    show "?unshp (?shp f) = f" unfolding id id' ..
  qed
qed

definition (in infinite) fresh_element :: "'a set \<Rightarrow> 'a" where
  "fresh_element A \<equiv> SOME a. a \<notin> A"

lemma (in infinite) finite_fresh_element: "finite A \<Longrightarrow> fresh_element A \<notin> A"
  unfolding fresh_element_def
  using ex_new_if_finite[OF infinite_UNIV, of A, THEN someI_ex] .

text \<open>every infinite type gives rise to a name generator\<close>
sublocale infinite \<subseteq> name_gen fresh_element
  by (unfold_locales) (rule finite_fresh_element)

(* some problem with generated names
text {* a type having a name_gen needs to be infinite *}
subclass (in name_gen) infinite
proof
  show "infinite (UNIV::'a set)"
  proof (rule ccontr)
    presume "finite (UNIV::'a set)"
    from fresh[OF this] have "fresh_name UNIV \<notin> UNIV" by blast
    thus False by simp
  qed simp
qed
*)

definition fresh_lists :: "'a list list \<Rightarrow> ('a list \<Rightarrow> 'a list) \<times> ('a list \<Rightarrow> 'a list)" where
  "fresh_lists xs \<equiv> let n = Suc (max_list (map length xs));
    f = (\<lambda> x. replicate n undefined @ x);
    g = drop n 
    in (f,g)"

lemma fresh_lists: assumes fr: "fresh_lists xs = (f,g)"
  shows "range f \<inter> set xs = {} \<and> g (f x) = x"
proof 
  show "g (f x) = x" using fr[unfolded fresh_lists_def Let_def] by auto
  show "range f \<inter> set xs = {}" 
  proof (rule ccontr) 
    assume "\<not> ?thesis"
    then obtain s where f: "s \<in> range f" and x: "s \<in> set xs" by auto
    from f have long: "length s > max_list (map length xs)" 
      using fr[unfolded fresh_lists_def Let_def] by auto
    from max_list[of "length s" "map length xs"] x 
    have short: "length s \<le> max_list (map length xs)" by auto
    from long short show False by auto
  qed
qed

definition "x\<^sub>1_to_x\<^sub>n = fresh_strings_list ''x'' 1 []"

lemma x\<^sub>1_to_x\<^sub>n[simp]: "length (x\<^sub>1_to_x\<^sub>n n) = n" "distinct (x\<^sub>1_to_x\<^sub>n n)"
  using fresh_name_gen_for_strings_list[folded fresh_strings_list_sound, unfolded fresh_name_gen_list_def,
    rule_format, of "''x''" 1 Nil n] unfolding x\<^sub>1_to_x\<^sub>n_def by auto

definition "inv_x\<^sub>1_to_x\<^sub>n as \<equiv> \<lambda> i. as ! the_inv_into {0 ..< length as} (\<lambda> i. x\<^sub>1_to_x\<^sub>n (length as) ! i) i"

lemma inv_x\<^sub>1_to_x\<^sub>n[simp]: "map (inv_x\<^sub>1_to_x\<^sub>n as) (x\<^sub>1_to_x\<^sub>n (length as)) = as"
proof (rule nth_equalityI, force, unfold length_map x\<^sub>1_to_x\<^sub>n)
  have inj: "inj_on ((!) (x\<^sub>1_to_x\<^sub>n (length as))) {0..<length as}"
    using nth_eq_iff_index_eq[OF x\<^sub>1_to_x\<^sub>n(2)[of "length as"]] unfolding inj_on_def by auto
  fix i
  assume i: "i < length as"
  then have "map (inv_x\<^sub>1_to_x\<^sub>n as) (x\<^sub>1_to_x\<^sub>n (length as)) ! i  = 
    (inv_x\<^sub>1_to_x\<^sub>n as) (x\<^sub>1_to_x\<^sub>n (length as) ! i )" (is "?l = _")
    by simp
  also have "\<dots> = as ! i" unfolding inv_x\<^sub>1_to_x\<^sub>n_def
    by (insert the_inv_into_f_f[of "\<lambda> i. x\<^sub>1_to_x\<^sub>n (length as) ! i", OF inj, of i] i, auto)
  finally show "?l = as ! i" .
qed

end

