(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Multiset2
imports
  "HOL-Library.Multiset"
  Weighted_Path_Order.Relations 
  Util
begin

lemma comp_fun_commute_plus[simp]: "comp_fun_commute ((+) :: (('a :: comm_monoid_add) \<Rightarrow> 'a \<Rightarrow> 'a))"
  by (standard, auto simp: ac_simps)

lemma union_commutes:
  "M + {#x#} + N = M + N + {#x#}"
  "M + mset xs + N = M + N + mset xs"
  by (auto simp: ac_simps)

lemma in_mset: assumes "x \<in># mset xs"
  shows "\<exists> bef aft. xs = bef @ x # aft"
proof -
  from assms[unfolded in_multiset_in_set set_conv_nth]
  obtain i where i: "i < length xs" and x: "xs ! i = x" by auto
  from id_take_nth_drop[OF i, unfolded x]
  show ?thesis by auto
qed

lemma in_mset_idx :
  assumes "a \<in># mset as"
  shows "\<exists>i. i < length as \<and> a = as ! i"
  using in_set_idx[of a as] assms by auto

lemma in_mset_eq: assumes "M + {#x#} = mset ys"
  shows "\<exists> bef aft. ys = bef @ x # aft \<and> M = mset (bef @ aft)"
proof -
  from assms[symmetric] have "x \<in># mset ys" by auto
  from in_mset[OF this] obtain bef aft where ys: "ys = bef @ x # aft"
    by auto
  have "M + {#x#} = mset (bef @ aft) + {#x#}"
    unfolding assms ys multiset_eq_iff by auto
  then have "M = mset (bef @ aft)" by auto
  from ys this show ?thesis by auto
qed

lemma mset_concat: assumes "mset xs = mset ys"
  shows "mset (concat xs) = mset (concat ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  let ?m = "mset"
  from in_mset_eq Cons(2)[simplified]
  obtain bef aft where ys: "ys = bef @ x # aft" and xs: "?m xs = ?m (bef @ aft)"
    by force
  from Cons(1)[OF xs] show ?case unfolding ys by (auto simp: multiset_eq_iff)
qed

lemma in_map_mset[intro]:
  "a \<in># A \<Longrightarrow> f a \<in># image_mset f A"
  unfolding in_image_mset by simp

lemma image_mset_Union_mset [simp]:
  "\<Sum>\<^sub># (image_mset f (\<Sum>\<^sub># M)) = \<Sum>\<^sub># (image_mset (\<lambda>N. \<Sum>\<^sub># (image_mset f N)) M)"
  by (induct M) simp_all

lemma in_mset_subset_Union: "M \<in># ms \<Longrightarrow> M \<subseteq># \<Sum>\<^sub># ms"
  using multi_member_split by force

lemma multised_add_singleton[simp]: "{# a #} + M = N + {# a #} \<longleftrightarrow> M = N"
  "M + {# a #} = {# a #} + N \<longleftrightarrow> M = N"
  by (auto simp: ac_simps)

lemma mem_Union_mset[simp]: "x \<in># \<Sum>\<^sub># ms \<longleftrightarrow> x \<in> \<Union> (set_mset ` (set_mset ms))"
  by (induct ms, auto)
  
lemma diff_union_swap_multiset :
  "a \<in># A \<Longrightarrow> A - {#a#} + B = A + B - {#a#}"
  by (intro multiset_eqI) auto

text\<open>In a multiset, there exists a local maxima.\<close>

lemma local_maxima_multiset:
  assumes "locally_trans s A A A" (is "?lt A")
    and "locally_irrefl s A" (is "?li A")
    and A_ne: "A \<noteq> {#}"
  shows "\<exists>a. a \<in># A \<and> (\<forall>b. b \<in># A \<longrightarrow> (b,a) \<notin> s)"
using assms
proof (induct A)
  case empty then show ?case by auto
next
  case (add x A)
  from lt_trans_l \<open>?lt (add_mset x A)\<close> have lt_A: "?lt A" by (metis add_mset_add_single)
  from li_trans_l \<open>?li (add_mset x A)\<close> have li_A: "?li A" by (metis add_mset_add_single)
  note IH = add(1)[OF lt_A li_A]
  show ?case
  proof (cases "A = {#}")
    case True
    with \<open>?li (add_mset x A)\<close>[unfolded locally_irrefl_def, rule_format] show ?thesis
    by simp
  next
    case False
    from IH[OF this]
    obtain a1 where
      a1_in_A: "a1 \<in># A"
      and a1_is_lm: "\<forall>b. b \<in># A \<longrightarrow> (b,a1) \<notin> s" by force
    show ?thesis
    proof (cases "(x,a1) \<in> s")
      case True note sxa1 = this
      have GL: "x \<in># A + {# x #}" by auto
      from add(3)[unfolded locally_irrefl_def]
      have GR1: "(x,x) \<notin> s" by simp
      {
        fix b assume b_in_A: "b \<in># A"
        have "(b,x) \<notin> s"
        proof (cases "(b,x) \<in> s")
          case True
          from b_in_A have b_in: "b \<in># A + {# x #}" by simp
          from a1_in_A have a1_in: "a1 \<in># A + {# x #}" by simp
          from b_in and a1_in and GL and True and sxa1 and
            add(3)[unfolded locally_irrefl_def] and
            add(2)[unfolded locally_trans_def]
          have "(b,a1) \<in> s" by (metis add_mset_add_single)
          with a1_is_lm and b_in_A show ?thesis by auto
        qed 
      }
      then have GR2: "\<forall>b. b \<in># A \<longrightarrow> (b,x) \<notin> s" by simp
      from this and GL and GR1 show ?thesis by auto
    next
      case False
      from this and a1_is_lm
      have GR: "\<forall>b. b \<in># A + {# x #} \<longrightarrow> (b,a1) \<notin> s" by simp
      from a1_in_A have GL: "a1 \<in># A + {# x #}" by simp
      from GL and GR show ?thesis by (metis add_mset_add_single)
    qed
  qed
qed

lemma mult1_ab_a: "({#a#}, {#a,b#}) \<in> mult1 r"
  unfolding mult1_def
proof(rule, unfold split, intro exI conjI)
  show "{#a, b#} = add_mset b {#a#}"
    by (simp add: ac_simps)
next
  show "{#a#} = {# a #} + {#}" by simp
qed simp

lemma mult1_ab_b: "({#b#}, {#a,b#}) \<in> mult1 r"
proof -
  have id: "{#a,b#} = {#b,a#}" by (simp add: ac_simps)
  show ?thesis unfolding id by (rule mult1_ab_a)
qed

declare mult1_union[intro!]

lemma mult1_mono_right[intro!]: assumes "(M,N) \<in> mult1 r"
  shows "((M + T, N + T) \<in> mult1 r)"
  using mult1_union[OF assms, of T] by (simp add: ac_simps)

lemma mult1_singleton[simp]: 
  shows "((M, {# t #}) \<in> mult1 r) = (\<forall> a. a \<in># M \<longrightarrow> (a,t) \<in> r)" (is "?l = ?r")
proof
  assume r: ?r
  show ?l
    unfolding mult1_def
    by (rule, unfold split, rule exI[of _ t], rule exI[of _ "{#}"], 
      rule exI[of _ M], insert r, auto)
next
  assume l: ?l
  from this[unfolded mult1_def]
  obtain a M0 K where id: "{#t#} = M0 + {#a#}"
    "M = M0 + K" and rel: "\<forall> b. b \<in># K \<longrightarrow> (b,a) \<in> r" by auto
  from id(1)[unfolded single_is_union] have "M0 = {#}" by simp
  with id have id: "t = a" "M = K" by auto
  show ?r unfolding id by (rule rel)
qed

inductive_set bounded_mult :: "nat \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel" for b and r where
  bounded_mult: "J \<noteq> {#} \<Longrightarrow> size K \<le> b \<Longrightarrow>
    (\<And> k. k \<in> set_mset K \<Longrightarrow> \<exists>j \<in> set_mset J. (k, j) \<in> r) \<Longrightarrow> (I + K, I + J) \<in> bounded_mult b r"

lemma bounded_mult_into_mult:
  "(M,N) \<in> bounded_mult b r \<Longrightarrow> (M,N) \<in> mult r"
by (induct rule: bounded_mult.induct, intro one_step_implies_mult, auto)

definition bmult_less where "bmult_less b \<equiv> bounded_mult b {(x,y :: nat). x < y}"
definition bound_mset :: "nat \<Rightarrow> nat multiset \<Rightarrow> nat" where
  "bound_mset b \<equiv> \<lambda> M. sum_mset (image_mset (\<lambda> x. (Suc b) ^ x) M)"

declare bound_mset_def[simp]

lemma bound_mset_linear_in_size: 
  assumes ij: "\<And> j. j \<in> set_mset J \<Longrightarrow> j < i"
  shows "bound_mset b J = 0 \<or> (\<exists> x. x < i \<and> bound_mset b J \<le> size J * (Suc b^x))"
  using ij
proof (induct J rule: multiset_induct)
  case (add x J) 
  show ?case
  proof (cases "size J = 0")
    case True
    then show ?thesis using add by (intro disjI2 exI[of _ x], auto)
  next
    case False
    let ?bb = "Suc b"
    let ?bound_mset = "bound_mset b"
    from add(1)[OF add(2)] False obtain y where yi: "y < i" and bound: "?bound_mset J \<le> size J * ?bb ^ y" by (cases J, auto)
    let ?x = "max x y"
    from yi add(2)[of x] have xi: "?x < i" by auto
    have "y \<le> ?x" by simp
    from power_increasing[OF this, of ?bb] 
    have "size J * ?bb ^ y \<le> size J * ?bb ^ ?x" by simp
    with bound have *: "?bound_mset J \<le> size J * ?bb ^ ?x" by arith
    have "x \<le> ?x" by simp
    from power_increasing[OF this, of ?bb] *
    have "?bound_mset (J + {# x #}) \<le> size (J + {# x #}) * ?bb ^ ?x" by simp
    with xi show ?thesis by force
  qed
qed simp

lemma bound_mset_bmult_less: "(M,N) \<in> bmult_less b ^^ k \<Longrightarrow> k \<le> bound_mset b N"
proof (induct k arbitrary: M N)
  case (Suc k)
  let ?bound_mset = "bound_mset b"
  from Suc(2) obtain K where mk: "(M,K) \<in> bmult_less b ^^ k" and kn: "(K,N) \<in> bmult_less b" by auto
  from Suc(1)[OF mk] have k: "k \<le> ?bound_mset K" .
  show ?case using kn unfolding bmult_less_def
  proof (cases)
    case (bounded_mult I J L)
    from bounded_mult(3,5) have "\<exists> i. i \<in> set_mset I \<and> (\<forall> j \<in> set_mset J. i > j)"
    proof (induct J rule: multiset_induct)
      case empty
      then show ?case by (cases I, auto)
    next
      case (add j J)
      from add(3)[of j] obtain i1 where i1: "i1 \<in> set_mset I" and i1j: "i1 > j" by auto
      from add(1)[OF add(2) add(3)] obtain i2 where i2: "i2 \<in> set_mset I" and i2J: "\<And> j. j \<in> set_mset J \<Longrightarrow> i2 > j" by force
      show ?case
      proof (cases "i1 < i2")
        case True
        then show ?thesis
          by (intro exI[of _ i2], insert i2 i2J i1j, auto)
      next
        case False
        {
          fix j
          assume "j \<in> set_mset J"
          from i2J[OF this] False have "i1 > j" by simp
        }
        then show ?thesis
          by (intro exI[of _ i1], insert i1 i1j, auto)
      qed
    qed
    then obtain i where i: "i \<in> set_mset I" and ij: "\<And> j. j \<in> set_mset J \<Longrightarrow> i > j" by blast
    define bb where "bb = Suc b"
    have bb1: "1 \<le> bb" unfolding bb_def by simp
    from i have I: "I = I - {# i #} + {# i #}" by auto
    from arg_cong[OF this, of ?bound_mset] 
    have le: "bb^i \<le> ?bound_mset I" unfolding bb_def by simp
    from bound_mset_linear_in_size[OF ij, of J b]
    have choice: "?bound_mset J = 0 \<or> (\<exists> x. x < i \<and> ?bound_mset J \<le> size J * (bb^x))" unfolding bb_def .
    have "?bound_mset J + 1 \<le> bb^i"
    proof (cases "?bound_mset J = 0")
      case True
      then show ?thesis by (simp add: bb_def)
    next
      case False
      with choice obtain x where xi: "x < i" and bound: "?bound_mset J \<le> size J * bb^x" by auto
      have "size J * bb ^ x \<le> b * bb ^ x" using bound bounded_mult(4) by simp
      with bound have bound: "?bound_mset J \<le> b * bb^x" by arith
      also have "b * bb^x < (b+1) * bb^x" using bb1 by simp
      also have "\<dots> = bb^(x + 1)" unfolding bb_def by simp
      also have "\<dots> \<le> bb^i" by (rule power_increasing[OF _ bb1], insert xi, auto)
      finally show ?thesis by simp
    qed
    with le      
    have "?bound_mset J + 1 \<le> ?bound_mset I" by arith
    then show ?thesis using k unfolding bounded_mult(1-2) 
      by simp
  qed
qed simp

lemma subset_imp_bounded_mult_refl: assumes "B \<subseteq># A"
  shows "(B,A) \<in> (bounded_mult k f)^="
proof -
  from assms[unfolded mset_subset_eq_exists_conv]
  obtain C where A: "A = B + C" by auto
  show ?thesis
  proof (cases "C = {#}")
    case True
    with A show ?thesis by auto
  next
    case False
    have id: "(B,A) = (B + {#}, B + C)" unfolding A by simp
    have "(B,A) \<in> bounded_mult k f" unfolding id
      by (rule bounded_mult, insert False, auto)
    then show ?thesis by simp
  qed
qed

lemma bound_mset_mono: assumes "A \<subseteq># B"
  shows "bound_mset k A \<le> bound_mset k B" 
proof -
  from assms[unfolded mset_subset_eq_exists_conv]
  obtain C where B: "B = A + C" by auto
  show ?thesis unfolding B bound_mset_def by auto
qed

declare bound_mset_def[simp del]

lemma mult_subset_mult:
  assumes "(A, B) \<in> mult r"
  and "B \<subseteq># C"
  shows "(A, C) \<in> mult r"
proof -
  from assms(2) obtain D where D:"B + D = C"
    using mset_subset_eq_exists_conv by metis
  then show ?thesis
  proof (cases "D = {#}")
    case True
    with D assms(1) show ?thesis by auto
  next
    case (False)
    from D one_step_implies_mult[OF False, of "{#}"] have "(B, C) \<in> mult r"
      by auto
    with assms(1) show ?thesis unfolding mult_def by auto
  qed
qed

lemma mset_remove_nth:
  assumes "i < length ss"
  shows "mset (remove_nth i ss) + {#ss ! i#} = mset ss"
by (metis add_mset_add_single assms id_take_nth_drop mset.simps(2) remove_nth_def union_code union_mset_add_mset_right)

lemma remove_nth_mult:
  assumes "i < length ss"
  shows "(mset (remove_nth i ss), mset ss) \<in> mult r"
proof -
  have "mset ss = mset (remove_nth i ss) + {#ss ! i#}"
    using assms mset_remove_nth by force
  with one_step_implies_mult [rule_format, of "{#ss ! i#}" "{#}"]
  show ?thesis by auto
qed

lemma non_empty_empty_mult:
  assumes "A \<noteq> {#}"
  shows "({#}, A) \<in> mult r"
using assms one_step_implies_mult[rule_format, of A "{#}" _ "{#}"]
by auto

lemma mset_concat_union:
  "mset (concat xs) = \<Sum>\<^sub># (mset (map mset xs))"
  by (induct xs, auto simp: union_commute)

lemma pointwise_mult_imp_mult:
  assumes "length Ms = length Ns"
    and "\<forall>i<length Ns. (Ms ! i, Ns ! i) \<in> (mult r)\<^sup>="
    and "trans r"
  shows "(\<Sum>\<^sub>#(mset Ms), \<Sum>\<^sub>#(mset Ns)) \<in> (mult r)\<^sup>="
using assms(1,2)
proof (induct Ms Ns rule: list_induct2)
  case (Cons M Ms N Ns)
  from Cons(3) have "\<forall>i<length Ns. (Ms ! i, Ns ! i) \<in> (mult r)\<^sup>=" by auto
  from Cons(2)[OF this] consider 
    (mult) "(\<Sum>\<^sub># (mset Ms), \<Sum>\<^sub># (mset Ns)) \<in> (mult r)" 
  | (eq) "\<Sum>\<^sub># (mset Ms) = \<Sum>\<^sub># (mset Ns)" 
    by auto
  then show ?case 
  proof (cases)
    case mult
    then obtain I J K where Ns:"\<Sum>\<^sub># (mset Ns) = I + J" and  Ms:"\<Sum>\<^sub># (mset Ms) = I + K" 
      and J:"J \<noteq> {#}" and K:"(\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> r)"
      using mult_implies_one_step assms(3) by metis
    from Cons(3) have "(M, N) \<in> (mult r) \<or> M = N" by auto
    then show ?thesis
    proof
      assume "M = N"
      with one_step_implies_mult[OF J K, of "I + M"] show ?thesis
        by (auto simp: Ms Ns ac_simps)
    next
      assume "(M, N) \<in> (mult r)"
      then obtain I' J' K' where N:"N = I' + J'" and M:"M = I' + K'" 
      and J':"J' \<noteq> {#}" and K':"(\<forall>k\<in>set_mset K'. \<exists>j\<in>set_mset J'. (k, j) \<in> r)"
        using mult_implies_one_step assms(3) by metis
      from J J' have J:"J + J' \<noteq> {#}" by auto
      from K K' have K:"(\<forall>k\<in>set_mset (K + K'). \<exists>j\<in>set_mset (J + J'). (k, j) \<in> r)"
        by auto
      show ?thesis using one_step_implies_mult[OF J K, of "I + I'"]
        by (auto simp: N M Ms Ns ac_simps)
    qed
  next
    case eq
    from Cons(3) have "(M, N) \<in> (mult r) \<or> M = N" by auto
    then show ?thesis
    proof
      assume "(M, N) \<in> (mult r)"
      then obtain I J K where "N = I + J" and "M = I + K" 
      and J:"J \<noteq> {#}" and K:"(\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> r)"
        using mult_implies_one_step assms(3) by metis
      with eq show ?thesis
        using one_step_implies_mult[OF J K, of "I + \<Sum>\<^sub># (mset Ms)"] by (auto simp: ac_simps)
    qed (insert eq, auto)
  qed
qed auto

end
