theory Lexicographic_Extension_More
  imports 
    Knuth_Bendix_Order.Lexicographic_Extension
begin

(* TODO: this content of this file will be part of AFP 2024, so remove in future *)
lemma nstri_lex_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "snd (lex_ext order n ss ts)"
  shows "snd (lex_ext order' n (map f ss) (map f ts))"
  using assms unfolding lex_ext_iff by auto

lemma stri_lex_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "fst (lex_ext order n ss ts)"
  shows "fst (lex_ext order' n (map f ss) (map f ts))"
  using assms unfolding lex_ext_iff by auto

lemma lex_ext_arg_empty: "snd (lex_ext f n [] xs) \<Longrightarrow> xs = []" 
  unfolding lex_ext_iff by auto

lemma lex_ext_co_compat:
  assumes "\<And> s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> snd (order' t s) \<Longrightarrow> False"
    and "\<And> s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> fst (order' t s) \<Longrightarrow> False"
    and "\<And> s t. fst (order s t) \<Longrightarrow> snd (order s t)" 
    and "fst (lex_ext order n ss ts)"
    and "snd (lex_ext order' n ts ss)" 
  shows False
proof -
  let ?ls = "length ss" 
  let ?lt = "length ts"
  define s where "s i = fst (order (ss ! i) (ts ! i))" for i 
  define ns where "ns i = snd (order (ss ! i) (ts ! i))" for i 
  define s' where "s' i = fst (order' (ts ! i) (ss ! i))" for i 
  define ns' where "ns' i = snd (order' (ts ! i) (ss ! i))" for i 
  have co: "i < ?ls \<Longrightarrow> i < ?lt \<Longrightarrow> s i \<Longrightarrow> ns' i \<Longrightarrow> False" for i
    using assms(1) unfolding s_def ns'_def set_conv_nth by auto
  have co': "i < ?ls \<Longrightarrow> i < ?lt \<Longrightarrow> s' i \<Longrightarrow> ns i \<Longrightarrow> False" for i
    using assms(2) unfolding s'_def ns_def set_conv_nth by auto
  from assms(4)[unfolded lex_ext_iff fst_conv, folded s_def ns_def]
  have ch1: "(\<exists> i. i < ?ls \<and> i < ?lt \<and> (\<forall> j<i. ns j) \<and> s i) \<or> (\<forall>i<?lt. ns i) \<and> ?lt < ?ls" (is "?A \<or> ?B") by auto
  from assms(5)[unfolded lex_ext_iff snd_conv, folded s'_def ns'_def]
  have ch2: "(\<exists>i. i < ?ls \<and> i < ?lt \<and> (\<forall>j<i. ns' j) \<and> s' i) \<or> (\<forall>i<?ls. ns' i) \<and> ?ls \<le> ?lt" (is "?A' \<or> ?B'") by auto 
  from ch1 show False
  proof
    assume ?A
    then obtain i where i: "i < ?ls" "i < ?lt" and s: "s i" and ns: "\<And> j. j < i \<Longrightarrow> ns j" by auto
    note s = co[OF i s] 
    have ns: "j < i \<Longrightarrow> s' j \<Longrightarrow> False" for j 
      using i ns[of j] co'[of j] by auto
    from ch2 show False
    proof
      assume ?A'
      then obtain i' where i': "i' < ?ls" "i' < ?lt" and s': "s' i'" and ns': "\<And> j'. j' < i' \<Longrightarrow> ns' j'" by auto
      from s ns'[of i] have "i \<ge> i'" by presburger
      with ns[OF _ s'] have i': "i' = i" by presburger
      from \<open>s i\<close> have "ns i" using assms(3) unfolding s_def ns_def by auto
      from co'[OF i s'[unfolded i'] this] show False .
    next
      assume ?B'
      with i have "ns' i" by auto
      from s[OF this] show False .
    qed
  next
    assume B: ?B
    with ch2 have ?A' by auto
    then obtain i where i: "i < ?ls" "i < ?lt" and s': "s' i" and ns': "\<And> j. j < i \<Longrightarrow> ns' j" by auto
    from co'[OF i s'] B i show False by auto
  qed
qed

lemma lex_ext_irrefl: assumes "\<And> x. x \<in> set xs \<Longrightarrow> \<not> fst (rel x x)"
  shows "\<not> fst (lex_ext rel n xs xs)" 
proof 
  assume "fst (lex_ext rel n xs xs)" 
  then obtain i where "i < length xs" and "fst (rel (xs ! i) (xs ! i))" 
    unfolding lex_ext_iff by auto
  with assms[of "xs ! i"] show False by auto
qed
(* end TODO *)

lemma lex_ext_unbounded_map2:
  assumes S: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> fst (r (ss ! i) (ts ! i)) \<Longrightarrow> fst (q (map f ss ! i) (map f ts ! i))"
  and NS: "\<And> i. i < length ss \<Longrightarrow> i < length ts \<Longrightarrow> snd (r (ss ! i) (ts ! i)) \<Longrightarrow> snd (q (map f ss ! i) (map f ts ! i))"
  shows "(fst (lex_ext_unbounded r ss ts) \<longrightarrow> fst (lex_ext_unbounded q (map f ss) (map f ts)))
    \<and> (snd (lex_ext_unbounded r ss ts) \<longrightarrow> snd (lex_ext_unbounded q (map f ss) (map f ts)))"
  using S NS unfolding lex_ext_unbounded_iff by auto

end