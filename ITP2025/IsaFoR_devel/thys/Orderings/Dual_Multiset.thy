(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Dual_Multiset
imports 
  Weighted_Path_Order.List_Order
  Auxx.Util
begin
 
abbreviation dms_order_idx_i where "dms_order_idx_i S NS idx ss ts i \<equiv>
     fst (idx i) < length ts \<and>
     (snd (idx i) \<longrightarrow> (ss ! i, ts ! fst (idx i)) \<in> S) \<and>
     (\<not> snd (idx i) \<longrightarrow> (ss ! i, ts ! fst (idx i)) \<in> NS) \<and>
     (\<not> snd (idx i) \<longrightarrow> (\<forall> i' < length ss. fst (idx i) = fst (idx i') \<longrightarrow> i = i'))"

abbreviation dms_order_idx where "dms_order_idx S NS idx ss ts stri \<equiv> (\<forall> i < length ss. dms_order_idx_i S NS idx ss ts i) \<and> (stri \<longrightarrow> (\<exists> j < length ts. (\<forall> i < length ss. idx i \<noteq> (j,False))))"


definition dms_order :: "nat \<Rightarrow> bool \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a list rel"
  where "dms_order n stri S NS \<equiv> { (ss,ts). (length ts \<le> n \<or> length ss = length ts) 
  \<and> (\<exists> idx. dms_order_idx S NS idx ss ts stri)}"

lemma dms_orderI: 
  assumes "length ts \<le> n \<or> length ss = length ts" 
  "\<And> i. i < length ss \<Longrightarrow> dms_order_idx_i S NS idx ss ts i"
  "stri \<Longrightarrow> \<exists> j < length ts. (\<forall> i < length ss. idx i \<noteq> (j,False))"
  shows "(ss,ts) \<in> dms_order n stri S NS"
  using assms unfolding dms_order_def by blast

lemma dms_order_refl: assumes "\<And> s. (s,s) \<in> NS"
  shows "(ss,ss) \<in> dms_order n False S NS"
  by (rule dms_orderI[of ss n ss "\<lambda> i. (i,False)"], insert assms, auto)
  
lemma dms_order_trans: assumes trans: "S O NS \<subseteq> S" "NS O S \<subseteq> S" "trans NS" "trans S"
  and mem1: "(ss1,ss2) \<in> dms_order n stri1 S NS"
  and mem2: "(ss2,ss3) \<in> dms_order n stri2 S NS"
  shows "(ss1,ss3) \<in> dms_order n (stri1 \<or> stri2) S NS"
proof -
  let ?n1 = "length ss1"
  let ?n2 = "length ss2"
  let ?n3 = "length ss3"
  note mem1 = mem1[unfolded dms_order_def] 
  note mem2 = mem2[unfolded dms_order_def]
  from mem1 have n1: "?n2 \<le> n \<or> ?n1 = ?n2" by auto
  from mem2 have n2: "?n3 \<le> n \<or> ?n2 = ?n3" by auto
  have n: "?n3 \<le> n \<or> ?n1 = ?n3" 
    by (cases "?n2 = ?n3", insert n1 n2, auto)
  note mem = dms_orderI[OF n]
  let ?Q = "dms_order_idx_i S NS"
  let ?P = "dms_order_idx S NS"
  from mem1 obtain idx1 where mem1: "?P idx1 ss1 ss2 stri1" by blast
  from mem2 obtain idx2 where mem2: "?P idx2 ss2 ss3 stri2" by blast
  let ?idx = "\<lambda> i. case idx1 i of (i',str) \<Rightarrow> case idx2 i' of (i'',str') \<Rightarrow> (i'',str \<or> str')"
  obtain idx where idx:  "idx = ?idx " by auto
  {
    fix i
    assume i: "i < ?n1"
    obtain i' str1 where idx1: "idx1 i = (i',str1)" by force
    obtain i'' str2 where idx2: "idx2 i' = (i'',str2)" by force
    note mem1i = mem1[THEN conjunct1, rule_format, OF i, unfolded idx1 fst_conv snd_conv]
    from mem1i have i': "i' < ?n2" by simp
    note mem2i = mem2[THEN conjunct1, rule_format, OF i', unfolded idx2 fst_conv snd_conv]
    from mem2i have i'': "i'' < ?n3" by simp
    have "?Q idx ss1 ss3 i" unfolding idx idx1 split idx2 fst_conv snd_conv
    proof(intro conjI impI, rule i'')
      assume one: "str1 \<or> str2"
      show "(ss1 ! i, ss3 ! i'') \<in> S" 
      proof (cases str1)
        case False
        with one have str1: "\<not> str1" and str2: "str2" by auto
        from str1 mem1i have one: "(ss1 ! i, ss2 ! i') \<in> NS" by auto
        from str2 mem2i have two: "(ss2 ! i', ss3 ! i'') \<in> S" by auto
        from trans(2) one two show ?thesis by blast
      next
        case True
        with mem1i have one: "(ss1 ! i, ss2 ! i') \<in> S" by auto        
        show ?thesis
        proof (cases str2)
          case False
          with mem2i have two: "(ss2 ! i', ss3 ! i'') \<in> NS" by auto
          from trans(1) one two show ?thesis by blast    
        next
          case True
          with mem2i have two: "(ss2 ! i', ss3 ! i'') \<in> S" by auto
          from trans(4) one two show ?thesis unfolding trans_def by blast    
        qed
      qed
    next
      assume "\<not> (str1 \<or> str2)"
      then have str1: "\<not> str1" and str2: "\<not> str2" by auto
      from str1 mem1i have one: "(ss1 ! i, ss2 ! i') \<in> NS" by auto
      from str2 mem2i have two: "(ss2 ! i', ss3 ! i'') \<in> NS" by auto
      from trans(3) one two show "(ss1 ! i, ss3 ! i'') \<in> NS" unfolding trans_def by blast
    next
      assume "\<not> (str1 \<or> str2)"
      then have str1: "\<not> str1" and str2: "\<not> str2" by auto
      let ?R = "\<lambda> i'. i'' = fst (?idx i') \<longrightarrow> i = i'"
      show "\<forall> i' < ?n1. ?R i'"
      proof (intro allI impI)
        fix j
        assume j: "j < ?n1" and idx: "i'' = fst (?idx j)"
        obtain j' str1' where idx1': "idx1 j = (j',str1')" by force
        obtain j'' str2' where idx2': "idx2 j' = (j'',str2')" by force
        note mem1j = mem1[THEN conjunct1, rule_format, OF j, unfolded idx1' fst_conv snd_conv]
        from mem1j have j': "j' < ?n2" by simp
        note mem2j = mem2[THEN conjunct1, rule_format, OF i', unfolded idx2' fst_conv snd_conv]
        from mem1i str1 j have one: "i' = fst (idx1 j) \<Longrightarrow> i = j" by auto
        from mem2i str2 j' have two: "i'' = fst (idx2 j') \<Longrightarrow> i' = j'" by auto 
        show "i = j"
          by (rule one, unfold idx1' fst_conv, rule two, unfold idx2',
            unfold idx idx1' split idx2', simp)
      qed
    qed
  } note Q = this
  note mem = mem[of idx]
  show ?thesis
  proof (rule mem, rule Q)
    assume "stri1 \<or> stri2"
    then show "\<exists> j < ?n3. \<forall> i < ?n1. idx i \<noteq> (j, False)"
    proof
      assume stri2
      with mem2 obtain j where j: "j < ?n3" and neq: "\<And> i. i < ?n2 \<Longrightarrow> (idx2 i \<noteq> (j, False))" by auto
      show ?thesis
      proof (intro exI conjI allI impI, rule j)
        fix i
        assume i: "i < ?n1"
        obtain i' str1 where idx1: "idx1 i = (i',str1)" by force
        obtain i'' str2 where idx2: "idx2 i' = (i'',str2)" by force
        note mem1i = mem1[THEN conjunct1, rule_format, OF i, unfolded idx1 fst_conv snd_conv]
        from mem1i have i': "i' < ?n2" by simp
        show "idx i \<noteq> (j, False)" using neq[OF i'] unfolding idx idx1 split idx2 by auto
      qed
    next
      assume stri1
      with mem1 obtain j where j: "j < ?n2" and neq: "\<And> i. i < ?n1 \<Longrightarrow> (idx1 i \<noteq> (j, False))" by auto
      let ?j = "fst (idx2 j)"
      from mem2 j have j': "?j < ?n3" by auto
      show ?thesis
      proof (intro exI conjI allI impI, rule j')
        fix i
        assume i: "i < ?n1"
        obtain i' str1 where idx1: "idx1 i = (i',str1)" by force
        obtain i'' str2 where idx2: "idx2 i' = (i'',str2)" by force
        note mem1i = mem1[THEN conjunct1, rule_format, OF i, unfolded idx1 fst_conv snd_conv]
        from mem1i have i': "i' < ?n2" by simp        
        show "idx i \<noteq> (?j, False)" unfolding idx idx1 split idx2 
        proof (cases "i' = j")
          case True
          show "(i'', str1 \<or> str2) \<noteq> (?j, False)"
            using neq[OF i] unfolding idx1 unfolding True by auto
        next
          case False note ij = this
          show "(i'',str1 \<or> str2) \<noteq> (?j, False)"
          proof (cases "str2")
            case True then show ?thesis by simp
          next
            case False
            with mem2[THEN conjunct1, rule_format, OF i', unfolded idx2 snd_conv fst_conv] 
               have "\<And> j. j < ?n2 \<Longrightarrow> i'' = fst (idx2 j) \<Longrightarrow> i' = j" by blast
            from this[OF j] ij show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
qed    
    
lemma (in order_pair) dms_order_order_pair: "order_pair (dms_order n True S NS) (dms_order n False S NS)" (is "order_pair ?S ?NS")
proof - 
  note trans = dms_order_trans[OF compat_S_NS compat_NS_S trans_NS trans_S, of _ _ n]
  show ?thesis
  proof
    show "refl ?NS" using refl_NS unfolding refl_on_def 
      using dms_order_refl[of NS _ n S] by auto
  next
    show "trans ?S" unfolding trans_def using trans[of _ _ True _ True, simplified] by blast
  next
    show "trans ?NS" unfolding trans_def using trans[of _ _ False _ False, simplified] by blast
  next
    show "?S O ?NS \<subseteq> ?S" using trans[of _ _ True _ False, simplified] by blast
  next
    show "?NS O ?S \<subseteq> ?S" using trans[of _ _ False _ True, simplified] by blast
  qed
qed

context
begin
qualified fun trace where "trace idxs (Suc 0) = 0"
   | "trace idxs (Suc i) = (fst (idxs i (trace idxs i)))"
end

lemma (in SN_order_pair) dms_order_SN_order_pair: "SN_order_pair (dms_order n True S NS) (dms_order n False S NS)" (is "SN_order_pair ?S ?NS")
proof -
  interpret dms_order: order_pair ?S ?NS
    by (rule dms_order_order_pair) 
  show ?thesis
  proof
    let ?b = "\<lambda> (f :: nat \<Rightarrow> 'a list) b. (\<forall> i. length (f i) \<le> b)"
    obtain size where size: "size = (\<lambda> f. LEAST b. ?b f b)" by auto
    {
      fix f
      assume steps: "\<And> i. (f i, f (Suc i)) \<in> ?S"
      from steps have False
      proof (induct f rule: wf_induct[OF wf_measure[of size]])
        case (1 f)
        note steps = 1(2)
        let ?P = "\<lambda> idx i. dms_order_idx S NS idx (f i) (f (Suc i)) True"
        {
          fix i
          from steps[of i, unfolded dms_order_def] have "\<exists> idx. ?P idx i" by blast
        }
        from choice[OF allI[OF this]] have "\<exists> idx. \<forall> i. ?P (idx i) i" .
        then obtain idx where idx: "\<And> i. ?P (idx i) i" by blast
        let ?Q = "\<lambda> i. dms_order_idx_i S NS (idx i) (f i) (f (Suc i))"
        obtain t where t: "t = Dual_Multiset.trace idx" by auto
        obtain s where s: "s = (\<lambda> i. snd (idx i (t i)))" by auto
        {
          fix i
          have "t (Suc i) < length (f (Suc i))"
          proof (induct i)
            case 0
            show ?case using idx[of 0] t by auto
          next
            case (Suc i)
            show ?case using idx[THEN conjunct1, rule_format, OF Suc] t by auto
          qed          
        } note len = this
        {
          fix i
          assume "i > (0 :: nat)"
          then obtain j where i: "i = Suc j" by (cases i, auto)
          from len[of j] have "t i < length (f i)" unfolding i by simp
        } note len = this
        {
          fix i
          assume "i > (0 :: nat)"
          then obtain j where i: "i = Suc j" by (cases i, auto)
          have "idx i (t i) = (t (Suc i), s i)" 
            unfolding i s t by simp
        } note idx_ts = this
        let ?f = "\<lambda> i. f i ! t i"
        obtain g where g: "g = (\<lambda> i. ?f (Suc i))" by auto
        have Suc0: "\<And> i. Suc i > (0 :: nat)" by simp
        {
          fix i
          assume "s (Suc i)"
          then have "(g i, g (Suc i)) \<in> S"
            using idx[THEN conjunct1, rule_format, OF len[OF Suc0[of i]]]
            unfolding idx_ts[OF Suc0] g by simp
        } note stri = this
        {
          fix i
          assume "\<not> s (Suc i)"
          then have "(g i, g (Suc i)) \<in> NS"
            using idx[THEN conjunct1, rule_format, OF len[OF Suc0[of i]]]
            unfolding idx_ts[OF Suc0] g by simp
        } note nstri = this
        from SN have SN_g0: "SN_on S {g 0}" unfolding SN_defs by auto
        from stri nstri have "\<forall> i. (g i, g (Suc i)) \<in> NS \<union> S" by auto
        from non_strict_ending[OF this compat_NS_S, OF SN_g0]
        obtain j where not_stri: "\<And> i. i \<ge> j \<Longrightarrow> (g i, g (Suc i)) \<notin> S" by auto
        {
          fix i
          assume ij: "i > j"
          then have 0: "i > 0" and ij: "i - Suc 0 \<ge> j" by auto
          from not_stri[OF ij] stri[of "i - Suc 0"] have "\<not> s (Suc (i - Suc 0))" by auto
          with 0 have "\<not> s i" by auto
          with idx_ts[OF 0] have "idx i (t i) = (t (Suc i), False)" by simp       
        } note idx_False = this
        let ?j = "Suc j"
        obtain h where h: "h = shift (\<lambda> i. remove_nth (t i) (f i)) ?j" by auto
        obtain idx' where idx': "idx' = shift (\<lambda> i j. 
          (adjust_idx_rev (t (Suc i)) (fst (idx i (adjust_idx (t i) j))), snd (idx i (adjust_idx (t i) j)))) ?j" by auto        
        {
          fix i
          have "t (i + ?j) < length (f (i + ?j))"
            by (rule len, simp)
        } note tlen = this
        {
          fix i
          have "length (f (i + ?j)) = Suc (length (h i))"
            unfolding h shift.simps
            by (rule remove_nth_len[OF tlen])
        } note len = this
        {
          fix i
          let ?ij = "i + ?j"
          let ?i = "t ?ij"
          let ?sij = "Suc i + ?j"
          let ?si = "t ?sij"
          note tleni = tlen[of i]
          {
            fix k
            let ?k = "adjust_idx ?i k"
            assume "k < length (h i)"
            have "idx' i k = (adjust_idx_rev ?si (fst (idx ?ij ?k)), snd (idx ?ij ?k))" unfolding idx' by simp
          } note idx' = this
          { 
            fix k
            assume "k < length (h i)"
            from this[unfolded h, simplified]
            have "k < length (remove_nth ?i (f ?ij))" by simp
            from adjust_idx_length[OF tlen this]
            have alen: "adjust_idx ?i k < length (f ?ij)" .
            from idx[THEN conjunct1, rule_format, OF alen]
            have dms_order: "dms_order_idx_i S NS (idx ?ij) (f ?ij) (f (Suc ?ij)) (adjust_idx ?i k)" .
            note alen dms_order
          } note alen_dms_order = this
          {
            fix k
            let ?k = "adjust_idx ?i k"
            assume klen: "k < length (h i)"
            from idx[of ?ij, THEN conjunct1, rule_format, OF tlen[of i]]
            have dms_order: "dms_order_idx_i S NS (idx ?ij) (f ?ij) (f (Suc ?ij)) ?i" .
            from dms_order[THEN conjunct2]
            have eq: "\<And> i'. \<not> snd (idx ?ij ?i) \<Longrightarrow> i' < length (f ?ij) \<Longrightarrow> fst (idx ?ij ?i) = fst (idx ?ij i') \<Longrightarrow> ?i = i'" by auto
            have "fst (idx ?ij ?k) \<noteq> ?si" 
            proof
              assume "fst (idx ?ij ?k) = ?si"
              then have id: "fst (idx ?ij ?i) = fst (idx ?ij ?k)" unfolding t by simp
              have klen: "k < length (remove_nth ?i (f ?ij))"
                using klen remove_nth_len[OF tlen[of i]] unfolding h by simp
              from idx_False[of ?ij] have "\<not> snd (idx ?ij ?i)" by simp
              note eq = eq[OF this adjust_idx_length[OF tlen klen] id]
              with adjust_idx_i[of ?i k] 
              show False by simp
            qed
          } note neq = this
          have "(h i, h (Suc i)) \<in> ?S"
          proof (rule dms_orderI)
            from len have len: "\<And> i. length (h i) = length (f (i + ?j)) - Suc 0" by simp
            show "length (h (Suc i)) \<le> n \<or> length (h i) = length (h (Suc i))"
              unfolding len using steps[of ?ij, unfolded dms_order_def] by auto
          next            
            fix k
            assume k: "k < length (h i)"
            from alen_dms_order[OF k]
            have alen: "adjust_idx ?i k < length (f ?ij)" 
              and dms_order: "dms_order_idx_i S NS (idx ?ij) (f ?ij) (f (Suc ?ij)) (adjust_idx ?i k)" .
            let ?k = "adjust_idx ?i k"
            have neqk: 
              "fst (idx ?ij ?k) \<noteq> ?si" by (rule neq[OF k])
            show "dms_order_idx_i S NS (idx' i) (h i) (h (Suc i)) k" 
            proof (intro conjI impI allI, 
                unfold idx'[OF k] fst_conv snd_conv h shift.simps adjust_idx_nth[OF tleni] adjust_idx_rev2[OF neqk] adjust_idx_nth[OF tlen[of "Suc i"]])
              assume "snd (idx ?ij ?k)"
              then show "(f ?ij ! ?k, f ?sij ! fst (idx ?ij ?k)) \<in> S"
                using dms_order by auto
            next
              assume "\<not> snd (idx ?ij ?k)"
              then show "(f ?ij ! ?k, f ?sij ! fst (idx ?ij ?k)) \<in> NS"
                using dms_order by auto
            next
              show "adjust_idx_rev ?si (fst (idx ?ij ?k)) < length (remove_nth ?si (f ?sij))"
                by (rule adjust_idx_rev_length, insert dms_order neqk tlen[of "Suc i"], auto)
            next
              fix k'
              assume nstri: "\<not> snd (idx ?ij ?k)"
                and k': "k' < length (remove_nth ?i (f ?ij))"
                and id: "adjust_idx_rev ?si (fst (idx ?ij ?k)) = fst (idx' i k')"
              have k'h: "k' < length (h i)" using k' unfolding h by simp
              let ?k' = "adjust_idx ?i k'"
              from id[unfolded idx'[OF k'h]]
              have id: "adjust_idx_rev ?si (fst (idx ?ij ?k)) = adjust_idx_rev ?si (fst (idx ?ij ?k'))" (is "?l = ?r") by simp
              then have "adjust_idx ?si ?l = adjust_idx ?si ?r" by simp
              from this[unfolded adjust_idx_rev2[OF neqk] adjust_idx_rev2[OF neq[OF k'h]]]
              have id: "fst (idx ?ij ?k) = fst (idx ?ij ?k')" .
              from dms_order[THEN conjunct2]
              have eq: "\<And> k'. \<not> snd (idx ?ij ?k) \<Longrightarrow> k' < length (f ?ij) \<Longrightarrow> fst (idx ?ij ?k) = fst (idx ?ij k') \<Longrightarrow> ?k = k'" by auto
              from eq[OF nstri adjust_idx_length[OF tlen k'] id]
              have "adjust_idx_rev ?i ?k = adjust_idx_rev ?i ?k'" by simp
              then show "k = k'" unfolding adjust_idx_rev1 by simp            
            qed
          next            
            from idx[THEN conjunct2, of "?ij"] obtain k 
              where k: "k < length (f ?sij)"
              and neqk: "\<And> k'. k' < length (f ?ij) \<Longrightarrow> idx ?ij k' \<noteq> (k,False)" by auto
            let ?k = "adjust_idx_rev ?si k"
            from idx_False[of ?ij] have idxi: "idx ?ij ?i = (?si, False)" by simp
            have ksi: "k \<noteq> ?si" 
            proof 
              assume "k = ?si"
              with idxi have "idx ?ij ?i = (k,False)" by simp
              with neqk[OF tlen] show False by simp
            qed            
            have kh: "?k < length (h (Suc i))" unfolding h shift.simps
              by (rule adjust_idx_rev_length[OF tlen k ksi])
            show "\<exists> k < length (h (Suc i)). \<forall> k' < length (h i). idx' i k' \<noteq> (k, False)" 
            proof (intro exI conjI allI impI, rule kh)
              fix k'
              assume k': "k' < length (h i)"
              let ?k' = "adjust_idx ?i k'"
              have ak': "?k' < length (f ?ij)"                
                by (rule adjust_idx_length[OF tlen], insert k', unfold h, simp)
              from neqk[OF ak'] have neqk: "idx ?ij ?k' \<noteq> (k,False)" .
              show "idx' i k' \<noteq> (?k, False)" 
              proof 
                assume id: "idx' i k' = (?k, False)"                
                from this[unfolded idx'[OF k']]
                have id: "adjust_idx_rev ?si (fst (idx ?ij ?k')) =
                      adjust_idx_rev ?si k" (is "?l = ?r") and  nstri: "\<not> snd (idx ?ij ?k')" unfolding t by auto
                from id have "adjust_idx ?si ?l = adjust_idx ?si ?r" by simp
                from this[unfolded adjust_idx_rev2[OF ksi] adjust_idx_rev2[OF neq[OF k']]] have id: "fst (idx ?ij ?k') = k" .
                have "idx ?ij ?k' = (fst (idx ?ij ?k'), snd (idx ?ij ?k'))" by simp
                also have "... = (k, False)" unfolding id using nstri by simp
                also have "... \<noteq> idx ?ij ?k'" using neqk by simp
                finally show False by simp
              qed
            qed
          qed
        } note hsteps = this
        show False
        proof (rule 1(1)[rule_format, of h, OF _ hsteps])
          show "(h,f) \<in> measure size" unfolding in_measure
          proof -
            {
              fix f
              assume steps: "\<And> i. (f i, f (Suc i)) \<in> ?S"
              let ?n = "max n (length (f 0))"
              {
                fix i
                have "length (f i) \<le> ?n"
                proof (induct i)
                  case (Suc i)
                  from steps[of i, unfolded dms_order_def] Suc show ?case by auto
                qed simp
              }
              then have "?b f ?n" by simp
              from LeastI[of "?b f", OF this] have bound: "?b f (size f)" unfolding size .
              have bound2: "\<exists> i. length (f i) = size f"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                then have neq: "\<And> i. length (f i) \<noteq> size f" by auto
                {
                  fix i
                  from neq[of i] bound[rule_format, of i] have "length (f i) < size f" by auto
                  then have "length (f i) \<le> size f - Suc 0" by auto
                }
                from Least_le[of "?b f", OF allI[OF this]] have "size f \<le> size f - Suc 0" unfolding size by simp
                then have "size f = 0" by simp
                with bound[rule_format, of 0] neq[of 0] show False by simp
              qed
              note bound bound2
            } note size = this
            from size(2)[of h, OF hsteps] obtain i where "length (h i) = size h" 
              by blast
            then have "size h = length (h i)" by simp
            also have "... < length (f (i + ?j))" unfolding h
              unfolding remove_nth_len[OF tlen[of i]] by simp
            also have "... \<le> size f" using size(1)[of f, OF steps] by auto
            finally show "size h < size f" .
          qed
        qed
      qed
    }
    then show "SN ?S"  unfolding SN_defs by auto
  qed
qed 

lemma dms_order_map: assumes fS: "\<And>a b. (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S"
  and fNS: "\<And>a b. (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS"
  and mem: "(ss1, ss2) \<in> dms_order n stri S NS"
  shows "(map f ss1, map f ss2) \<in> dms_order n stri S NS"
proof -
  let ?Q = "dms_order_idx_i S NS"
  let ?P = "dms_order_idx S NS"
  note mem = mem[unfolded dms_order_def]
  let ?n1 = "length ss1"
  let ?n2 = "length ss2"
  let ?n1' = "length (map f ss1)"
  let ?n2' = "length (map f ss2)"
  from mem have "?n2' \<le> n \<or> ?n1' = ?n2'" by simp
  note dms_order = dms_orderI[OF this]
  from mem obtain idx where mem: "?P idx ss1 ss2 stri" unfolding dms_order_def by blast
  then have "stri \<Longrightarrow> \<exists> j < ?n2'. (\<forall> i < ?n1'. idx i \<noteq> (j,False))" by auto
  note dms_order = dms_order[OF _ this]
  show ?thesis
  proof (rule dms_order)
    fix i
    assume "i < ?n1'"
    then have i: "i < ?n1" by simp
    with mem have Q: "?Q idx ss1 ss2 i" by simp
    let ?i = "fst (idx i)"
    from Q i have i': "?i < ?n2" by simp
    show "?Q idx (map f ss1) (map f ss2) i"
    proof (intro conjI impI, unfold nth_map[OF i] nth_map[OF i'])
      assume stri: "snd (idx i)"
      show "(f (ss1 ! i), f (ss2 ! ?i)) \<in> S"
        by (rule fS, insert Q i stri, auto)
    next
      assume nstri: "\<not> snd (idx i)"
      show "(f (ss1 ! i), f (ss2 ! ?i)) \<in> NS"
        by (rule fNS, insert Q i nstri, auto)
    qed (insert i' Q, auto)      
  qed
qed

interpretation dms_order: list_order_extension "dms_order n True" "dms_order n False"  
proof -
  let ?S = "dms_order n True"
  let ?NS = "dms_order n False"
  show "list_order_extension ?S ?NS"
  proof (rule list_order_extension.intro[OF _ dms_order_map dms_order_map])
    fix s ns 
    let ?s = "?S s ns"
    let ?ns = "?NS s ns"
    assume "SN_order_pair s ns"
    then interpret SN_order_pair s ns .
    show "SN_order_pair ?s ?ns" by (rule dms_order_SN_order_pair)
  next
    fix as bs :: "'b list" and NS S :: "'b rel"
    let ?n1 = "length as"
    let ?n2 = "length bs"
    assume len: "?n1 = ?n2" and ns: "\<And> i. i < ?n2 \<Longrightarrow> (as ! i, bs ! i) \<in> NS"
    show "(as,bs) \<in> ?NS S NS"
    proof (rule dms_orderI)
      fix i
      assume "i < ?n1"
      then show "dms_order_idx_i S NS (\<lambda> i. (i,False)) as bs i" using ns len by auto
    qed (insert len, auto)
  qed
qed

lemma dms_order_mono:
  assumes ns: "set ss1 \<times> set ss2 \<inter> NS \<subseteq> NS'"
  and s: "set ss1 \<times> set ss2 \<inter> S \<subseteq> S'"
  and mem: "(ss1,ss2) \<in> dms_order n stri S NS"
  shows "(ss1,ss2) \<in> dms_order n stri S' NS'"
proof -
  let ?Q = "dms_order_idx_i S NS"
  let ?Q' = "dms_order_idx_i S' NS'"
  let ?P = "dms_order_idx S NS"
  note mem = mem[unfolded dms_order_def]
  let ?n1 = "length ss1"
  let ?n2 = "length ss2"
  from mem have "?n2 \<le> n \<or> ?n1 = ?n2" by simp
  note dms = dms_orderI[OF this]
  from mem obtain idx where mem: "?P idx ss1 ss2 stri" unfolding dms_order_def by blast
  then have "stri \<Longrightarrow> \<exists> j < ?n2. (\<forall> i < ?n1. idx i \<noteq> (j,False))" by auto
  note dms = dms[OF _ this]
  show ?thesis
  proof (rule dms)
    fix i
    assume i: "i < length ss1"
    then have si: "ss1 ! i \<in> set ss1" by auto    
    from mem i have Q: "?Q idx ss1 ss2 i" by simp
    let ?j = "fst (idx i)"
    from Q i have "?j < length ss2" by auto
    then have sj: "ss2 ! ?j \<in> set ss2" by auto
    show "?Q' idx ss1 ss2 i"
    proof(intro conjI allI impI)
      assume "snd (idx i)"
      with Q si sj s show "(ss1 ! i, ss2 ! ?j) \<in> S'" by auto
    next
      assume "\<not> snd (idx i)"
      with Q si sj ns show "(ss1 ! i, ss2 ! ?j) \<in> NS'" by auto
    qed (insert Q, auto)
  qed
qed
  
end
