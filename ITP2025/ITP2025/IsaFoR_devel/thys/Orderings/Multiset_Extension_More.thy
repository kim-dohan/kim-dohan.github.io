theory Multiset_Extension_More
  imports 
    Weighted_Path_Order.Multiset_Extension2
begin

(* TODO: will be part of AFP 2024 *)
lemma mul_ext_arg_empty: "snd (mul_ext f [] xs) \<Longrightarrow> xs = []" 
  unfolding mul_ext_def Let_def by (auto simp: ns_mul_ext_def mult2_alt_def)

lemma s_mul_ext_irrefl: assumes irr: "irrefl_on (set_mset A) S" 
  and S_NS: "S \<subseteq> NS" 
  and compat: "S O NS \<subseteq> S" 
shows "(A,A) \<notin> s_mul_ext NS S" using irr
proof (induct A rule: wf_induct[OF wf_measure[of size]])
  case (1 A)
  show ?case
  proof
    assume "(A,A) \<in> s_mul_ext NS S" 
    from s_mul_extE[OF this]
    obtain A1 A2 B1 B2 where
      A: "A = A1 + A2" 
      and B: "A = B1 + B2"
      and AB1: "(A1, B1) \<in> multpw NS"
      and ne: "A2 \<noteq> {#}" 
      and S: "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> S" 
      by blast
    from multpw_listE[OF AB1] obtain as1 bs1 where
      l1: "length as1 = length bs1" 
      and A1: "A1 = mset as1" 
      and B1: "B1 = mset bs1" 
      and NS: "\<And> i. i<length bs1 \<Longrightarrow> (as1 ! i, bs1 ! i) \<in> NS" by blast
    (* store for later usage *)
    note NSS = NS
    note SS = S
   
    obtain as2 where A2: "A2 = mset as2" by (metis ex_mset)
    obtain bs2 where B2: "B2 = mset bs2" by (metis ex_mset)
    define as where "as = as1 @ as2" 
    define bs where "bs = bs1 @ bs2" 
    have as: "A = mset as" unfolding A A1 A2 as_def by simp
    have bs: "A = mset bs" unfolding B B1 B2 bs_def by simp
    from as bs have abs: "mset as = mset bs" by simp
    hence set_ab: "set as = set bs" by (rule mset_eq_setD)
    let ?n = "length bs" 
    have las: "length as = ?n" 
      using mset_eq_length abs by fastforce
    let ?m = "length bs1" 
    define decr where "decr j i \<equiv> 
       (as ! j, bs ! i) \<in> NS \<and> (i < ?m \<longrightarrow> j = i) \<and> (?m \<le> i \<longrightarrow> ?m \<le> j \<and> (as ! j, bs ! i) \<in> S)" for i j
    define step where "step i j k = 
       (i < ?n \<and> j < ?n \<and> k < ?n \<and> bs ! k = as ! j \<and> decr j i)" 
      for i j k
    {
      fix i
      assume i: "i < ?n" 
      let ?b = "bs ! i" 
      have "\<exists> j. j < ?n \<and> decr j i" 
      proof (cases "i < ?m")
        case False
        with i have "?b \<in> set bs2" unfolding bs_def 
          by (auto simp: nth_append)
        hence "?b \<in># B2" unfolding B2 by auto
        from S[OF this, unfolded A2] obtain a where a: "a \<in> set as2" and S: "(a, ?b) \<in> S" 
          by auto
        from a obtain k where a: "a = as2 ! k" and k: "k < length as2" unfolding set_conv_nth by auto
        have "a = as ! (?m + k)" unfolding a as_def l1[symmetric] by simp
        from S[unfolded this] S_NS False k
        show ?thesis unfolding decr_def
          by (intro exI[of _ "?m + k"], auto simp: las[symmetric] l1[symmetric] as_def)
      next
        case True
        from NS[OF this] i True show ?thesis unfolding decr_def
          by (auto simp: as_def bs_def l1 nth_append)
      qed (insert i NS)
      from this[unfolded set_conv_nth] las
      obtain j where j: "j < ?n" and decr: "decr j i" by auto
      let ?a = "as ! j" 
      from j las have "?a \<in> set as" by auto
      from this[unfolded set_ab, unfolded set_conv_nth] obtain k where
        k: "k < ?n" and id: "?a = bs ! k" by auto
      have "\<exists> j k. step i j k" 
        using j k decr id i unfolding step_def by metis
    }
    hence "\<forall> i. \<exists> j k. i < ?n \<longrightarrow> step i j k" by blast
    from choice[OF this] obtain J' where "\<forall> i. \<exists> k. i < ?n \<longrightarrow> step i (J' i) k" by blast
    from choice[OF this] obtain K' where 
      step: "\<And> i. i < ?n \<Longrightarrow> step i (J' i) (K' i)" by blast
    define I where "I i = (K'^^i) 0" for i 
    define J where "J i = J' (I i)" for i
    define K where "K i = K' (I i)" for i
    from ne have "A \<noteq> {#}" unfolding A by auto
    hence "set as \<noteq> {}" unfolding as by auto
    hence "length as \<noteq> 0" by simp
    hence n0: "0 < ?n" using las by auto
    {
      fix n
      have "step (I n) (J n) (K n)" 
      proof (induct n)
        case 0
        from step[OF n0] show ?case unfolding I_def J_def K_def by auto
      next
        case (Suc n)
        from Suc have "K n < ?n" unfolding step_def by auto
        from step[OF this] show ?case unfolding J_def K_def I_def by auto
      qed
    }
    note step = this
    have "I n \<in> {..<?n}" for n using step[of n] unfolding step_def by auto 
    hence "I ` UNIV \<subseteq> {..<?n}" by auto
    from finite_subset[OF this] have "finite (I ` UNIV)" by simp
    from pigeonhole_infinite[OF _ this] obtain m where 
      "infinite {i. I i = I m}" by auto
    hence "\<exists> m'. m' > m \<and> I m' = I m"
      by (simp add: infinite_nat_iff_unbounded)
    then obtain m' where *: "m < m'" "I m' = I m" by auto
    let ?P = "\<lambda> n. \<exists> m. n \<noteq> 0 \<and> I (n + m) = I m" 
    define n where "n = (LEAST n. ?P n)" 
    have "\<exists> n. ?P n" 
      by (rule exI[of _ "m' - m"], rule exI[of _ m], insert *, auto)
    from LeastI_ex[of ?P, OF this, folded n_def]
    obtain m where n: "n \<noteq> 0" and Im: "I (n + m) = I m" by auto
    let ?M = "{m..<m+n}" 
    {
      fix i j
      assume *: "m \<le> i" "i < j" "j < n + m" 
      define k where "k = j - i" 
      have k0: "k \<noteq> 0" and j: "j = k + i" and kn: "k < n" using * unfolding k_def by auto
      from not_less_Least[of _ ?P, folded n_def, OF kn] k0
      have "I i \<noteq> I j" unfolding j by metis
    } 
    hence inj: "inj_on I ?M" unfolding inj_on_def
      by (metis add.commute atLeastLessThan_iff linorder_neqE_nat)
    define b where "b i = bs ! I i" for i
    have bnm: "b (n + m) = b m" unfolding b_def Im ..
    {
      fix i
      from step[of i, unfolded step_def]
      have id: "bs ! K i = as ! J i" and decr: "decr (J i) (I i)" by auto
      from id decr[unfolded decr_def] have "(bs ! K i, bs ! I i) \<in> NS" by auto
      also have "K i = I (Suc i)" unfolding I_def K_def by auto
      finally have "(b (Suc i), b i) \<in> NS" unfolding b_def by auto
    } note NS = this
    {
      fix i j :: nat
      assume "i \<le> j" 
      then obtain k where j: "j = i + k" by (rule less_eqE)
      have "(b j, b i) \<in> NS^*" unfolding j
      proof (induct k)
        case (Suc k)
        thus ?case using NS[of "i + k"] by auto
      qed auto
    } note NSstar = this
    {
      assume "\<exists> i \<in> ?M. I i \<ge> ?m" 
      then obtain k where k: "k \<in> ?M" and I: "I k \<ge> ?m" by auto
      from step[of k, unfolded step_def]
      have id: "bs ! K k = as ! J k" and decr: "decr (J k) (I k)" by auto
      from id decr[unfolded decr_def] I have "(bs ! K k, bs ! I k) \<in> S" by auto
      also have "K k = I (Suc k)" unfolding I_def K_def by auto
      finally have S: "(b (Suc k), b k) \<in> S" unfolding b_def by auto
      from k have "m \<le> k" by auto
      from NSstar[OF this] have NS1: "(b k, b m) \<in> NS^*" .
      from k have "Suc k \<le> n + m" by auto
      from NSstar[OF this, unfolded bnm] have NS2: "(b m, b (Suc k)) \<in> NS^*" .
      from NS1 NS2 have "(b k, b (Suc k)) \<in> NS^*" by simp
      with S have "(b (Suc k), b (Suc k)) \<in> S O NS^*" by auto
      also have "\<dots> \<subseteq> S" using compat
        by (metis compat_tr_compat converse_inward(1) converse_mono converse_relcomp)
      finally have contradiction: "b (Suc k) \<notin> set_mset A" using 1 unfolding irrefl_on_def by auto
      have "b (Suc k) \<in> set bs" unfolding b_def using step[of "Suc k"] unfolding step_def
        by auto
      also have "set bs = set_mset A" unfolding bs by auto
      finally have False using contradiction by auto
    }
    hence only_NS: "i \<in> ?M \<Longrightarrow> I i < ?m" for i by force
    {
      fix i
      assume i: "i \<in> ?M" 
      from step[of i, unfolded step_def] have *: "I i < ?n" "K i < ?n" 
        and id: "bs ! K i = as ! J i" and decr: "decr (J i) (I i)" by auto
      from decr[unfolded decr_def] only_NS[OF i] have "J i = I i" by auto
      with id have id: "bs ! K i = as ! I i" by auto
      note only_NS[OF i] id
    } note pre_result = this
    {
      fix i
      assume i: "i \<in> ?M" 
      have *: "I i < ?m" "K i < ?m" 
      proof (rule pre_result[OF i])
        have "\<exists> j \<in> ?M. K i = I j" 
        proof (cases "Suc i \<in> ?M")
          case True
          show ?thesis by (rule bexI[OF _ True], auto simp: K_def I_def)
        next
          case False
          with i have id: "n + m = Suc i" by auto
          hence id: "K i = I m" by (subst Im[symmetric], unfold id, auto simp: K_def I_def) 
          with i show ?thesis by (intro bexI[of _ m], auto simp: K_def I_def)
        qed
        with pre_result show "K i < ?m" by auto
      qed
      from pre_result(2)[OF i] * l1 have "bs1 ! K i = as1 ! I i" "K i = I (Suc i)" 
        unfolding as_def bs_def by (auto simp: nth_append K_def I_def)
      with * have "bs1 ! I (Suc i) = as1 ! I i" "I i < ?m" "I (Suc i) < ?m" 
        by auto
    } note pre_identities = this
    define M where "M = ?M" 
    note inj = inj[folded M_def]
    define nxt where "nxt i = (if Suc i = n + m then m else Suc i)" for i
    define prv where "prv i = (if i = m then n + m - 1 else i - 1)" for i
    {
      fix i
      assume "i \<in> M" 
      hence i: "i \<in> ?M" unfolding M_def by auto
      from i n have inM: "nxt i \<in> M" "prv i \<in> M" "nxt (prv i) = i" "prv (nxt i) = i"
        unfolding nxt_def prv_def by (auto simp: M_def)
      from i pre_identities[OF i] pre_identities[of m] Im n
      have nxt: "bs1 ! I (nxt i) = as1 ! I i"  
        unfolding nxt_def prv_def by (auto simp: M_def)
      note nxt inM
    } note identities = this
  
  
    (* next up: remove elements indexed by I ` ?m from both as1 and bs1 
       and apply induction hypothesis *)
    note identities = identities[folded M_def]
    define Drop where "Drop = I ` M" 

    define rem_idx where "rem_idx = filter (\<lambda> i. i \<notin> Drop) [0..<?m]" 
    define drop_idx where "drop_idx = filter (\<lambda> i. i \<in> Drop) [0..<?m]" 
    define as1' where "as1' = map ((!) as1) rem_idx" 
    define bs1' where "bs1' = map ((!) bs1) rem_idx"
    define as1'' where "as1'' = map ((!) as1) drop_idx" 
    define bs1'' where "bs1'' = map ((!) bs1) drop_idx" 
    {
      fix as1 :: "'a list" and D :: "nat set" 
      define I where "I = [0..< length as1]" 
      have "mset as1 = mset (map ((!) as1) I)" unfolding I_def
        by (rule arg_cong[of _ _ mset], intro nth_equalityI, auto)
      also have "\<dots> = mset (map ((!) as1) (filter (\<lambda> i. i \<in> D) I))
          + mset (map ((!) as1) (filter (\<lambda> i. i \<notin> D) I))" 
        by (induct I, auto)
      also have "I = [0..< length as1]" by fact
      finally have "mset as1 = mset (map ((!) as1) (filter (\<lambda>i. i \<in> D) [0..<length as1])) + mset (map ((!) as1) (filter (\<lambda>i. i \<notin> D) [0..<length as1]))" .
    } note split = this
    from split[of bs1 Drop, folded rem_idx_def drop_idx_def, folded bs1'_def bs1''_def]
    have bs1: "mset bs1 = mset bs1'' + mset bs1'" .
    from split[of as1 Drop, unfolded l1, folded rem_idx_def drop_idx_def, folded as1'_def as1''_def]
    have as1: "mset as1 = mset as1'' + mset as1'" .

    (* showing that as1'' = bs1'' *)
    define I' where "I' = the_inv_into M I" 
    have bij: "bij_betw I M Drop" using inj unfolding Drop_def by (rule inj_on_imp_bij_betw)
    from the_inv_into_f_f[OF inj, folded I'_def] have I'I: "i \<in> M \<Longrightarrow> I' (I i) = i" for i by auto
    from bij I'I have II': "i \<in> Drop \<Longrightarrow> I (I' i) = i" for i
      by (simp add: I'_def f_the_inv_into_f_bij_betw)
    from II' I'I identities bij have Drop_M: "i \<in> Drop \<Longrightarrow> I' i \<in> M" for i
      using Drop_def by force
    have M_Drop: "i \<in> M \<Longrightarrow> I i \<in> Drop" for i unfolding Drop_def by auto
    {
      fix x
      assume "x \<in> Drop" 
      then obtain i where i: "i \<in> M" and x: "x = I i" unfolding Drop_def by auto
      have "x < ?m" unfolding x using i pre_identities[of i] unfolding M_def by auto
    } note Drop_m = this
    hence drop_idx: "set drop_idx = Drop" unfolding M_def drop_idx_def set_filter set_upt by auto
    have "mset as1'' = mset (map ((!) as1) drop_idx)" unfolding as1''_def mset_map by auto
    also have "drop_idx = map (I o I') drop_idx" using drop_idx by (intro nth_equalityI, auto intro!: II'[symmetric])
    also have "map ((!) as1) \<dots> = map (\<lambda> i. as1 ! I i) (map I' drop_idx)" by auto
    also have "\<dots> = map (\<lambda> i. bs1 ! I (nxt i)) (map I' drop_idx)" 
      by (rule map_cong[OF refl], rule identities(1)[symmetric], insert drop_idx Drop_M, auto)
    also have "\<dots> = map ((!) bs1) (map (I o nxt o I') drop_idx)" 
      by auto
    also have "mset \<dots> = image_mset ((!) bs1) (image_mset (I o nxt o I') (mset drop_idx))" unfolding mset_map ..
    also have "image_mset (I o nxt o I') (mset drop_idx) = image_mset I (image_mset nxt (image_mset I' (mset drop_idx)))" 
      by (metis multiset.map_comp)
    also have "image_mset nxt (image_mset I' (mset drop_idx)) = image_mset I' (mset drop_idx)" 
    proof -
      have dist: "distinct drop_idx" unfolding drop_idx_def by auto
      have injI': "inj_on I' Drop" using II' by (rule inj_on_inverseI)
      have "mset drop_idx = mset_set Drop" unfolding drop_idx[symmetric]
        by (rule mset_set_set[symmetric, OF dist])
      from image_mset_mset_set[OF injI', folded this]
      have "image_mset I' (mset drop_idx) = mset_set (I' ` Drop)" by auto
      also have "I' ` Drop = M" using II' I'I M_Drop Drop_M by force
      finally have id: "image_mset I' (mset drop_idx) = mset_set M" .
      have inj_nxt: "inj_on nxt M" using identities by (intro inj_on_inverseI)
      have nxt: "nxt ` M = M" using identities by force
      show ?thesis unfolding id image_mset_mset_set[OF inj_nxt] nxt ..
    qed
    also have "image_mset I \<dots> = mset drop_idx" unfolding multiset.map_comp using II' 
      by (intro multiset.map_ident_strong, auto simp: drop_idx)
    also have "image_mset ((!) bs1) \<dots> = mset bs1''" unfolding bs1''_def mset_map ..
    finally have bs1'': "mset bs1'' = mset as1''" ..

    (* showing the remaining identities *)
    let ?A = "mset as1' + mset as2" 
    let ?B = "mset bs1' + mset bs2" 
    from as1 bs1'' have as1: "mset as1 = mset bs1'' + mset as1'" by auto
    have A: "A = mset bs1'' + ?A" unfolding A A1 A2 as1 by auto
    have B: "A = mset bs1'' + ?B" unfolding B B1 B2 bs1 by auto
    from A[unfolded B] have AB: "?A = ?B" by simp
    
    have l1': "length as1' = length bs1'" unfolding as1'_def bs1'_def by auto
    have NS: "(mset as1', mset bs1') \<in> multpw NS" 
    proof (rule multpw_listI[OF l1' refl refl], intro allI impI)
      fix i
      assume i: "i < length bs1'"
      hence "rem_idx ! i \<in> set rem_idx" unfolding bs1'_def by (auto simp: nth_append)
      hence ri: "rem_idx ! i < ?m" unfolding rem_idx_def by auto
      from NSS[OF this] i
      show "(as1' ! i, bs1' ! i) \<in> NS" unfolding as1'_def bs1'_def by (auto simp: nth_append)
    qed
    have S: "(mset as1' + mset as2, ?B) \<in> s_mul_ext NS S"
      by (intro s_mul_extI[OF refl refl NS], unfold A2[symmetric] B2[symmetric], rule ne, rule S)
    have irr: "irrefl_on (set_mset ?B) S" using 1(2) B unfolding irrefl_on_def by simp
    have "M \<noteq> {}" unfolding M_def using n by auto
    hence "Drop \<noteq> {}" unfolding Drop_def by auto
    with drop_idx have "drop_idx \<noteq> []" by auto
    hence "bs1'' \<noteq> []" unfolding bs1''_def by auto
    hence "?B \<subset># A" unfolding B by (simp add: subset_mset.less_le)
    hence "size ?B < size A" by (rule mset_subset_size)
    thus False using 1(1) AB S irr by auto
  qed
qed
  
lemma mul_ext_irrefl: assumes "\<And> x. x \<in> set xs \<Longrightarrow> \<not> fst (rel x x)" 
  and "\<And> x y z. fst (rel x y) \<Longrightarrow> snd (rel y z) \<Longrightarrow> fst (rel x z)"
  and "\<And> x y. fst (rel x y) \<Longrightarrow> snd (rel x y)" 
shows "\<not> fst (mul_ext rel xs xs)" 
  unfolding mul_ext_def Let_def fst_conv
  by (rule s_mul_ext_irrefl, insert assms, auto simp: irrefl_on_def)
(* end TODO *)


end