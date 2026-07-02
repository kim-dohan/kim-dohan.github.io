theory Misc_Aux
imports "Certification_Monads.Error_Monad"
begin

section \<open>Auxiliary definitions and lemmas\<close>

subsection \<open>Dropping first elements in lists and taking tails of lists\<close>

definition drop_tail where
  "drop_tail n  xs = rev (drop n (rev xs))"

definition take_tail where
  "take_tail n xs = rev (take n (rev xs))"

lemma drop_tail_except_first:
  assumes "k = length fs"
  shows"drop_tail k (f#fs) = [f]"
  using assms by (simp add: drop_tail_def)

lemma take_tail_except_first:
  assumes "k = length fs"
  shows "take_tail k (f#fs) = fs"
  using assms by (simp add: take_tail_def)

lemma take_tail_Cons:
  assumes "k \<le> length xs"
  shows "take_tail k (x#xs) = take_tail k xs"
  using assms unfolding take_tail_def by simp

section \<open>Sum bind split rules\<close>

lemma sum_bind_split: "P (m \<bind> f) = ((\<forall>v. m = Inl v \<longrightarrow> P (Inl v)) \<and> (\<forall>v. m = Inr v \<longrightarrow> P (f v)))"
  by (cases m) (auto)

lemma sum_bind_split_asm: "P (m \<bind> f) = (\<not> ((\<exists>v. m = Inl v \<and> \<not> P (Inl v)) \<or> (\<exists>x. m = Inr x \<and> \<not> P (f x))))"
  by (cases m) (auto)

lemmas sum_bind_splits = sum_bind_split sum_bind_split_asm

section \<open>mapM\<close>

fun mapM_sum :: "('a \<Rightarrow> 'e + 'b) \<Rightarrow> 'a list \<Rightarrow> 'e + 'b list" where
  "mapM_sum _ [] = Inr []"
| "mapM_sum f (x#xs) = do {
      y \<leftarrow> f x;
      ys \<leftarrow> mapM_sum f xs;
      Inr (y # ys)
    }"

lemma mapM_sum:
  assumes "isOK (mapM_sum f xs)" "x \<in> set xs"
  shows "isOK (f x)"
  using assms by (induction xs) auto

lemma sequence_isOK:
  assumes "isOK (sequence xs)" "x \<in> set xs"
  shows "isOK x"
  using assms by (induction xs) auto

end