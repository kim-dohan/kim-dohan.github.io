(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Map_Choice
imports
  Collections.RBTMapImpl
  Collections.RBTSetImpl
  Deriving.RBT_Compare_Order_Impl
begin 

definition ceta_map_of :: "('a \<times> 'b) list \<Rightarrow> 'a :: compare_order \<Rightarrow> 'b option" where 
  "ceta_map_of ps = rm.\<alpha> (rm.to_map ps)"

lemma ceta_map_of[simp]: "ceta_map_of ps = map_of ps"
  unfolding ceta_map_of_def rm.correct by simp

fun fun_of_map_fun :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where 
  "fun_of_map_fun m d a = (case m a of Some b \<Rightarrow> b | None \<Rightarrow> d a)"

definition precompute_fun :: "('a :: compare_order \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "precompute_fun f as = fun_of_map_fun (ceta_map_of (map (\<lambda> a. (a,f a)) as)) f"

lemma precompute_fun[simp]: "precompute_fun f as = f"
proof (intro ext)
  fix a
  show "precompute_fun f as a = f a" unfolding precompute_fun_def
    using map_of_SomeD by (force split: option.splits)
qed

fun fun_of_map_fun' :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c)" where 
  "fun_of_map_fun' m d f a = (case m a of Some b \<Rightarrow> f b | None \<Rightarrow> d a)"

definition ceta_set_of :: "('a :: compare_order) list \<Rightarrow> 'a \<Rightarrow> bool" where 
  "ceta_set_of ps \<equiv> let tree = rs.from_list ps in (\<lambda> a. rs.memb a tree)"

lemma ceta_set_of[simp]: "ceta_set_of xs = (\<lambda> y. y \<in> set xs)"
  unfolding ceta_set_of_def Let_def
  by (rule ext, simp add: rs.correct)

definition ceta_list_diff :: "('a :: compare_order) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "ceta_list_diff xs ys \<equiv> rs.to_list (foldl (\<lambda> a b. rs.delete b a) (rs.from_list xs) ys)"

lemma ceta_list_diff[simp]: "set (ceta_list_diff xs ys) = set xs - set ys" 
proof -
  {
    fix xs
    have "rs.\<alpha> (foldl (\<lambda> a b. rs.delete b a) xs ys) = rs.\<alpha> xs - set ys"
    proof (induct ys arbitrary: xs)
      case (Cons y ys)
      show ?case unfolding foldl.simps o_def
        unfolding Cons by (auto simp: rs.correct)
    qed simp
  } note main = this
  have id: "\<And> xs. set (rs.to_list xs) = rs.\<alpha> xs" by (simp add: rs.correct)
  show ?thesis
    unfolding ceta_list_diff_def
    unfolding id
    unfolding main
    by (simp add: rs.correct)
qed

end

