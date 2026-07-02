(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Set_Order
imports 
  Weighted_Path_Order.Multiset_Extension2
  Weighted_Path_Order.List_Order
begin

definition set_s_order :: "'a list_ext" where "set_s_order s ns \<equiv> {(as,bs). as \<noteq> [] \<and> (\<forall> b \<in> set bs. \<exists> a \<in> set as. (a,b) \<in> s)}"

definition set_ns_order :: "'a list_ext" where "set_ns_order s ns \<equiv> {(as,bs). (\<forall> b \<in> set bs. \<exists> a \<in> set as. (a,b) \<in> ns)}"

interpretation list_order_extension set_s_order set_ns_order
proof(intro list_order_extension.intro)
  fix s ns
  assume OP: "SN_order_pair s ns"
  then interpret SN_order_pair s ns .
  let ?S = "set_s_order s ns"
  let ?NS = "set_ns_order s ns"
  note d = set_s_order_def set_ns_order_def
  show "SN_order_pair ?S ?NS"
  proof 
    show "refl ?NS" using refl_NS unfolding refl_on_def d by auto
  next
    show "trans ?S" using trans_S unfolding trans_def d by blast
  next
    show "trans ?NS" using trans_NS unfolding trans_def d by blast
  next
    show "?NS O ?S \<subseteq> ?S" using compat_NS_S_point unfolding d by force
  next
    show "?S O ?NS \<subseteq> ?S" using compat_S_NS_point unfolding d by blast
  next
    let ?m = mset
    let ?S' = "{(as,bs). (?m as, ?m bs) \<in> s_mul_ext ns s}"
    from mul_ext_list.extension[OF OP]
    interpret SN_order_pair ?S'
      "{(as,bs). (?m as, ?m bs) \<in> ns_mul_ext ns s}" .
    show "SN ?S"
    proof (rule SN_subset[OF SN])
      show "?S \<subseteq> ?S'"
      proof
        fix as bs
        assume "(as,bs) \<in> ?S"
        then have as: "as \<noteq> []" and bs: "\<And> b. b \<in> set bs \<Longrightarrow> \<exists> a \<in> set as. (a,b) \<in> s" unfolding set_s_order_def by auto
        then have "(?m as, ?m bs) \<in> s_mul_ext ns s" unfolding s_mul_ext_def 
          by (auto intro!: mult2_alt_sI[of _ "{#}" _ _ "{#}"] simp: in_multiset_in_set Bex_def)
        then show "(as,bs) \<in> ?S'" by simp
      qed 
    qed
  qed
next
  fix S f NS as bs
  assume "\<And> a b. (a,b) \<in> S \<Longrightarrow> (f a,f b) \<in> S" 
    "(as,bs) \<in> set_s_order S NS"
  then show "(map f as, map f bs) \<in> set_s_order S NS" unfolding set_s_order_def by force
next
  fix S f NS as bs
  assume "\<And> a b. (a,b) \<in> NS \<Longrightarrow> (f a,f b) \<in> NS" 
    "(as,bs) \<in> set_ns_order S NS"
  then show "(map f as, map f bs) \<in> set_ns_order S NS" unfolding set_ns_order_def by force
next
  fix as bs :: "'a list" and NS S
  assume "length as = length bs" "\<And> i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> NS"
  then show "(as,bs) \<in> set_ns_order S NS" unfolding set_ns_order_def set_conv_nth by force
qed

end
