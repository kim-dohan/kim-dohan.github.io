(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Min_Set_Order
imports 
  Weighted_Path_Order.List_Order
begin

definition min_set_s_order :: "'a list_ext" where "min_set_s_order s ns \<equiv> {(as,bs). bs \<noteq> [] \<and> (\<forall> a \<in> set as. \<exists> b \<in> set bs. (a,b) \<in> s)}"

definition min_set_ns_order :: "'a list_ext" where "min_set_ns_order s ns \<equiv> {(as,bs). (\<forall> a \<in> set as. \<exists> b \<in> set bs. (a,b) \<in> ns)}"

context
begin
private fun helper where
  "helper f S 0 = (SOME a . a \<in> set (f (Suc 0)))" |
  "helper f S (Suc n) = (SOME b. (helper f S n, b) \<in> S \<and> b \<in> set (f (Suc (Suc n))))"

lemma min_set_order: "list_order_extension min_set_s_order min_set_ns_order"
proof(intro list_order_extension.intro)
  fix s ns
  assume "SN_order_pair s ns"
  then interpret SN_order_pair s ns .
  let ?S = "min_set_s_order s ns"
  let ?NS = "min_set_ns_order s ns"
  note d = min_set_s_order_def min_set_ns_order_def
  show "SN_order_pair ?S ?NS"
  proof 
    show "refl ?NS" using refl_NS unfolding refl_on_def d by auto
  next
    show "trans ?S" using trans_S unfolding trans_def d by blast
  next
    show "trans ?NS" using trans_NS unfolding trans_def d by blast
  next
    show "?NS O ?S \<subseteq> ?S" using compat_NS_S_point unfolding d by blast
  next
    show "?S O ?NS \<subseteq> ?S" using compat_S_NS_point unfolding d by force
  next
    show "SN ?S"
    proof
      fix f
      assume "\<forall> i. (f i, f (Suc i)) \<in> ?S"
      then have f: "\<And> i. (f i, f (Suc i)) \<in> ?S" by auto
      {
        fix i        
        have "\<exists> x. x \<in> set (f (Suc i))" using f[of i] unfolding d by (cases "f (Suc i)", auto)
      } note ne = this
      obtain h where h: "h = helper f s" by auto
      {
        fix n
        have "(h n, h (Suc n)) \<in> s \<and> h (Suc n) \<in> set (f (Suc (Suc n)))"
        proof (induct n)
          case 0
          from someI_ex[OF ne[of 0]] have "h 0 \<in> set (f (Suc 0))" unfolding h by auto
          with f[of "Suc 0"] have "\<exists> x. (h 0, x) \<in> s \<and> x \<in> set (f (Suc (Suc 0)))"
            unfolding d by auto
          from someI_ex[OF this] show ?case unfolding h by auto 
        next
          case (Suc n)
          with f[of "Suc (Suc n)"] have "\<exists> x. (h (Suc n), x) \<in> s \<and> x \<in> set (f (Suc (Suc (Suc n))))" unfolding d by auto
          from someI_ex[OF this] show ?case unfolding h by auto
        qed
      }
      with SN show False by auto
    qed
  qed
next
  fix S f NS as bs
  assume "\<And> a b. (a,b) \<in> S \<Longrightarrow> (f a,f b) \<in> S" 
    "(as,bs) \<in> min_set_s_order S NS"
  then show "(map f as, map f bs) \<in> min_set_s_order S NS" unfolding min_set_s_order_def by force
next
  fix S f NS as bs
  assume "\<And> a b. (a,b) \<in> NS \<Longrightarrow> (f a,f b) \<in> NS" 
    "(as,bs) \<in> min_set_ns_order S NS"
  then show "(map f as, map f bs) \<in> min_set_ns_order S NS" unfolding min_set_ns_order_def by force
next
  fix as bs :: "'a list" and NS S
  assume "length as = length bs" "\<And> i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> NS"
  then show "(as,bs) \<in> min_set_ns_order S NS" unfolding min_set_ns_order_def set_conv_nth by force
qed
end

end
