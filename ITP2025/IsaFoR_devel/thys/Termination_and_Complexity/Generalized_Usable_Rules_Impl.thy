(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  Makarius Wenzel <makarius@sketis.net> (2013)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generalized_Usable_Rules_Impl
imports 
  Generalized_Usable_Rules
  "Transitive-Closure-II.RTrancl"
  TRS.Q_Restricted_Rewriting_Impl
begin

fun rel_dep_prod :: "bool \<Rightarrow> dependance \<Rightarrow> bool list" (infix "***" 52) where
  "_ *** Ignore = []"
| "b *** Increase = [b]"
| "b *** Decrease = [\<not> b]"
| "_ *** Wild = [True,False]"

text \<open>usable_rules_gen1 t is a list which contains (r,b) if U(t) \<supseteq> U(r)^b for some right hand side r of a rule,
  where U(r)^True = U(r), and U(r)^False = U(r)^-1, cf. usable_rules_gen2\<close>
fun usable_rules_gen1 :: "'f dep \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)term \<times> bool \<Rightarrow> (('f,'v)term \<times> bool)list" where 
  "usable_rules_gen1 \<pi> R (Var _,_) = []"
| "usable_rules_gen1 \<pi> R (Fun f ts, b) =  (let n = length ts in [ (r,b) . (l,r) <- R, compat_root l (Fun f ts)] @
     [(ts ! i, d). i <- [0 ..< n], d <- b *** \<pi> (f,n) i])" 

fun usable_rules_gen2 :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<times> bool \<Rightarrow> ('f,'v)rules" where
  "usable_rules_gen2 R (t, b) = (let RR = [(l,r) . (l,r) <- R, compat_root l t] in (if b then RR else map (\<lambda> (l,r). (r,l)) RR))"


text \<open>the usable rules of P are computed by taking (t,True) for all rhs t of P, then take the 
  reflexive transitive closure w.r.t. usable_rules_gen1, and afterward expand the entries (r,b) via usable_rules_gen2\<close>

definition usable_rules_pre_gen :: "'f dep \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules" where
  "usable_rules_pre_gen \<pi> R P \<equiv> remdups (concat (map (usable_rules_gen2 R) 
    (mk_rtrancl_list (=) (usable_rules_gen1 \<pi> R) (map (\<lambda> (s,t). (t,True)) P))))"

lemma (in fixed_trs_dep) usable_rules_pre_gen: assumes RR: "set RR = R"
  shows "set (usable_rules_pre_gen \<pi> RR P) = gen_usable_rules_pairs (set P)"
proof -
  let ?U1 = "usable_rules_gen1 \<pi> RR"
  let ?U2 = "usable_rules_gen2 RR"
  {
    fix t b
    have "{ba. ((t, b), ba) \<in> {(a, b). b \<in> set (?U1 a)}^*} \<subseteq> {(s,d) | s u d. u \<in> set (t # map snd RR) \<and> u \<unrhd> s}" (is "?A \<subseteq> ?B")
    proof
      fix s c
      assume "(s,c) \<in> ?A"
      then have "((t, b), s, c) \<in> {(a, b). b \<in> set (?U1 a)}^*" by simp      
      then show "(s,c) \<in> ?B"
      proof (induct)
        case base
        show ?case by auto
      next
        case (step sc ud)
        obtain s c where sc: "sc = (s,c)" by force
        obtain u d where ud: "ud = (u,d)" by force
        from step(2)[unfolded sc ud]
        have mem: "(u, d) \<in> set (?U1 (s, c))" by auto
        from mem obtain f ss where s: "s = Fun f ss" by (cases s, auto)
        from mem[unfolded s]
        have  "(\<exists>l. (l, u) \<in> set RR \<and> compat_root l (Fun f ss) \<and> d = c) \<or>
          (\<exists> i. i <length ss \<and> (u, d) \<in> Pair (ss ! i) ` set (c *** \<pi> (f, length ss) i))" (is "?l \<or> ?i") by (force simp: Let_def)
        then show ?case
        proof
          assume ?l
          then obtain l where "(l, u) \<in> set RR" by auto
          then have "u \<in> set (t # map snd RR) \<and> u \<unrhd> u" by force
          then show ?thesis unfolding ud by blast
        next
          assume ?i
          then obtain i where "i < length ss" and u: "u = ss ! i" by auto
          then have su: "s \<unrhd> u" unfolding s by auto
          from step(3)[unfolded sc] obtain v where v: "v \<in> set (t # map snd RR)" and vs: "v \<unrhd> s" by auto
          from supteq_trans[OF vs su] v show ?thesis unfolding ud by auto
        qed
      qed
    qed
    also have "... = set [(s,d) . u <- t # map snd RR, s <- supteq_list u, d <- [True,False]]" (is "_ = ?B")
      by auto
    finally have "?A \<subseteq> ?B" .
    from finite_subset[OF this finite_set] have "finite ?A" .
  } note finite = this          
  interpret relation_subsumption_list ?U1 "(=)"
    by (unfold_locales, insert finite, auto)
  let ?UU1 = "{(a, b). b \<in> set (?U1 a)}"
  have id: "set (usable_rules_pre_gen \<pi> RR P) = 
    \<Union> ((\<lambda> tc. set (?U2 tc)) ` ?UU1^* `` {(t,True) | t. t \<in> rhss (set P)})" (is "?A1 = ?A2")
    unfolding usable_rules_pre_gen_def by (force simp: mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl]])
  have "gen_usable_rules_pairs (set P) = \<Union>(gen_usable_rules ` rhss (set P))" (is "?B1 = ?B2")
    unfolding gen_usable_rules_pairs_def ..
  also have "?B2 = ?A2" 
  proof 
    show "?A2 \<subseteq> ?B2"
    proof (rule subsetI)    
      define dc where "dc = (\<lambda> c. if c then Increase else Decrease)"
      {
        fix t s c
        assume "((t,True),(s,c)) \<in> ?UU1^*"
        from rtrancl_imp_UN_relpow[OF this] obtain n where 
          "((t,True),(s,c)) \<in> ?UU1 ^^ n" by auto
        then have "gen_usable_rules s ^^^ dc c \<subseteq> gen_usable_rules t"
        proof (induction n arbitrary: s c)
          case 0
          then show ?case unfolding dc_def by auto
        next
          case (Suc n s c)
          from Suc.prems[unfolded relpow.simps]
          obtain u d where steps: "((t,True),(u,d)) \<in> ?UU1 ^^ n" and step: "(s,c) \<in> set (?U1 (u,d))" by force
          from step obtain f us where u: "u = Fun f us" by (cases u, auto)
          from step[unfolded u]
          have "(\<exists>l. (l,s) \<in> R \<and> compat_root l (Fun f us) \<and> c = d) \<or>
                (\<exists>i < length us. s = us ! i \<and> c \<in> set (d *** \<pi> (f, length us) i))" by (force simp: RR Let_def)
          then obtain l i where "(l,s) \<in> R \<and> compat_root l (Fun f us) \<and> c = d \<or> 
            i < length us \<and> s = us ! i \<and> c \<in> set (d *** \<pi> (f, length us) i)" (is "?l \<or> ?i") by blast
          then have "gen_usable_rules s ^^^ dc c \<subseteq> gen_usable_rules u ^^^ dc d" (is "?left \<subseteq> ?right")
          proof
            assume l: ?l
            then obtain ls where "l = Fun f ls" and "length ls = length us" and "(Fun f ls,s) \<in> R" and "c = d" by (cases l, auto)
            then have "gen_usable_rules s \<subseteq> \<Union> { gen_usable_rules r | ls r. (Fun f ls,r) \<in> R \<and> length ls = length us}" by auto
            also have "... \<subseteq> gen_usable_rules u" unfolding u gen_usable_rules_Fun by blast
            finally show ?thesis unfolding \<open>c = d\<close>
              by (rule rel_dep_mono)
          next
            assume i: ?i
            {
              fix s :: "('f,'v)trs" and b1 b2 d
              assume "b1 \<in> set (b2 *** d)"
              then have "s ^^^ dc b1 \<subseteq> (s ^^^ d) ^^^ dc b2"
                unfolding dc_def
                by (cases b1 rule: bool.exhaust, cases b2, cases d, auto, cases d, auto, cases d, auto, cases d, auto)
            } note dep_prod = this
            have "gen_usable_rules s ^^^ dc c \<subseteq>
              (gen_usable_rules s ^^^ \<pi> (f,length us) i) ^^^ dc d" 
              by (rule dep_prod, insert i, auto)
            also have "... \<subseteq> gen_usable_rules u ^^^ dc d"
              by (rule rel_dep_mono, unfold u gen_usable_rules_Fun, insert i, auto)
            finally show ?thesis .
          qed
          also have "... \<subseteq> gen_usable_rules t" by (rule Suc.IH[OF steps])
          finally show ?case .
        qed
      } note main = this
      fix lr
      assume "lr \<in> ?A2"      
      then obtain t s c where U2: "lr \<in> set (?U2 (s,c))" and U1: "((t,True),(s,c)) \<in> {(a, b). b \<in> set (?U1 a)}^*" 
        and P: "t \<in> rhss (set P)" by force
      obtain l r where lr: "lr = (l,r)" by force
      have "(l,r) \<in> gen_usable_rules s ^^^ dc c"
      proof (cases c)
        case True
        with U2 lr have "(l,r) \<in> set RR" and "compat_root l s" by auto
        from in_R[OF this[unfolded RR]] True show ?thesis unfolding gen_usable_rules_def dc_def by auto
      next
        case False
        with U2 lr have "(r,l) \<in> set RR" and "compat_root r s" by auto
        from in_R[OF this[unfolded RR]] False show ?thesis unfolding gen_usable_rules_def dc_def by auto
      qed
      also have "gen_usable_rules s ^^^ dc c \<subseteq> ?B2" using main[OF U1] P by auto
      finally
      show "lr \<in> ?B2" unfolding lr .
    qed
  next
    show "?B2 \<subseteq> ?A2"
    proof
      fix l r
      assume "(l,r) \<in> ?B2"
      then obtain t where gen: "gen_usable_rule t (l,r)" and t: "t \<in> rhss (set P)"
        using gen_usable_rules_def by blast
      from gen have "\<exists> s d. ((t,True),(s,d)) \<in> ?UU1^* \<and> (l,r) \<in> set (?U2 (s,d))"
      proof (induct)
        case (in_R l r t)
        show ?case
          by (rule exI[of _ t], rule exI[of _ True], insert in_R, auto simp: RR)
      next
        case (in_U l r t lr')
        from in_U(4) obtain s d where steps: "((r,True),(s,d)) \<in> ?UU1^*" and lr': "lr' \<in> set (?U2 (s,d))" by blast
        from in_U(1-2) have "((t,True),(r,True)) \<in> ?UU1" by (cases t, auto simp: RR Let_def)
        from this steps have "((t,True),(s,d)) \<in> ?UU1^*" by (rule converse_rtrancl_into_rtrancl)
        with lr' show ?case by auto
      next
        case (in_arg i ts lr lr' f)
        from in_arg(3) obtain s d where steps: "((ts ! i,True),(s,d)) \<in> ?UU1^*" and mem: "lr \<in> set (?U2 (s,d))" by blast
        obtain l r where lr: "lr = (l,r)" by force
        from mem lr have imem: "(r,l) \<in> set (?U2 (s,\<not> d))" by (auto simp: Let_def)
        {
          fix t b s c
          assume "((t,b),(s,c)) \<in> ?UU1^*"
          from rtrancl_imp_UN_relpow[OF this] obtain n 
            where "((t,b),(s,c)) \<in> ?UU1^^n" by blast
          then have "((t,\<not> b),(s,\<not> c)) \<in> ?UU1^*"
          proof (induction n arbitrary: t b s c)
            case 0 then show ?case by auto
          next
            case (Suc n t b s c)
            from Suc.prems obtain u d 
              where steps: "((t,b),(u,d)) \<in> ?UU1^^n" and step: "(s,c) \<in> set (?U1 (u,d))" by force
            from Suc.IH[OF steps] have IH: "((t,\<not> b), (u,\<not> d)) \<in> ?UU1^*" .
            {              
              from step obtain f us where u: "u = Fun f us" by (cases u, auto)
              with step have "(\<exists>a\<in>set RR. \<exists>l. (l, s) = a \<and> compat_root l (Fun f us) \<and> c = d) \<or>
                (\<exists>i < length us. s = us ! i \<and> c \<in> set (d *** \<pi> (f, length us) i))" (is "?l \<or> ?i") by (auto simp: Let_def)
              then have "(s,\<not> c) \<in> set (?U1 (u,\<not> d))"
              proof
                assume ?l then show ?thesis unfolding u by (auto simp: Let_def)
              next
                assume ?i
                then obtain i where i: "i < length us" and s: "s = us ! i" and c: "c \<in> set (d *** \<pi> (f, length us) i)" by auto
                let ?pi = "\<pi> (f,length us) i"
                from c have "(\<not> c) \<in> set ((\<not> d) *** ?pi)" by (cases ?pi, auto)
                with i s show ?thesis unfolding u by (auto simp: Let_def)
              qed
            }
            with IH have "((t,\<not> b),(s,\<not> c)) \<in> ?UU1 ^* O ?UU1" by auto
            then show ?case by regexp
          qed
        } note invert = this
        from in_arg(1) have i: "i < length ts" .
        from in_arg(4) have lr': "lr' \<in> {lr} ^^^ \<pi> (f, length ts) i" .
        from invert[OF steps] have "((ts ! i, False), s, \<not> d) \<in> ?UU1^*" by simp
        note isteps = converse_rtrancl_into_rtrancl[OF _ this]
        note steps = converse_rtrancl_into_rtrancl[OF _ steps]
        show ?case 
        proof (cases "\<pi> (f,length ts) i")
          case Ignore
          with lr' show ?thesis by auto
        next
          case Increase
          with lr' have lr': "lr' = lr" by auto
          from Increase i have "((Fun f ts, True), (ts ! i, True)) \<in> ?UU1" by (force simp: Let_def)
          from steps[OF this] show ?thesis using mem lr' by auto
        next
          case Decrease
          with lr' lr have lr': "lr' = (r,l)" by auto
          from Decrease i have "((Fun f ts, True), (ts ! i, False)) \<in> ?UU1" by (force simp: Let_def)
          from isteps[OF this] imem lr' show ?thesis by force
        next
          case Wild
          from lr' have "lr' = (l,r) \<or> lr' = (r,l)" unfolding lr Wild by auto
          then show ?thesis
          proof
            assume lr': "lr' = (l,r)"
            from Wild i have "((Fun f ts, True), (ts ! i, True)) \<in> ?UU1" by (force simp: Let_def)
            from steps[OF this] show ?thesis using mem lr lr' by auto
          next
            assume lr': "lr' = (r,l)"
            from Wild i have "((Fun f ts, True), (ts ! i, False)) \<in> ?UU1" by (force simp: Let_def)
            from isteps[OF this] imem lr' show ?thesis by force
          qed
        qed
      qed
      then show "(l,r) \<in> ?A2" using t by blast
    qed
  qed
  finally show ?thesis unfolding id by simp
qed

text \<open>in the previous version we removed duplicates of all entries (r,True). However,
  for usable_rules_gen2, only the root symbol of r is relevant. Therefore, we now develop
  a slightly more efficient version, where r is replaced by its root, so that more duplicates
  can be removed\<close>
fun compat_root' where 
  "compat_root' _ None = False"
| "compat_root' (Var _) _ = False"
| "compat_root' fls gn = (root fls = gn)"

lemma compat_root'[simp]: "compat_root' l (root t) = compat_root l t"
  by (cases l, (cases t, auto)+)

fun usable_rules_gen2' :: "('f,'v)rules \<Rightarrow> ('f \<times> nat)option \<times> bool \<Rightarrow> ('f,'v)rules" where
  "usable_rules_gen2' R (fn, b) = (let RR = [(l,r) . (l,r) <- R, compat_root' l fn] in (if b then RR else map (\<lambda> (l,r). (r,l)) RR))"

definition usable_rules_gen :: "'f dep \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules" where
  "usable_rules_gen \<pi> R P \<equiv> concat (map (usable_rules_gen2' R) 
    (remdups (map (\<lambda> (t,b). (root t,b)) (mk_rtrancl_list (=) (usable_rules_gen1 \<pi> R) (map (\<lambda> (s,t). (t,True)) P)))))"

lemma (in fixed_trs_dep) usable_rules_gen: assumes RR: "set RR = R"
  shows "set (usable_rules_gen \<pi> RR P) = gen_usable_rules_pairs (set P)"
proof -
  {
    fix t b
    have "set (usable_rules_gen2' RR (root t,b)) = set (usable_rules_gen2 RR (t,b))"
      by (auto simp: Let_def)
  }
  then show ?thesis
    unfolding usable_rules_pre_gen[OF RR, symmetric]
    unfolding usable_rules_gen_def usable_rules_pre_gen_def
    by force
qed
end

