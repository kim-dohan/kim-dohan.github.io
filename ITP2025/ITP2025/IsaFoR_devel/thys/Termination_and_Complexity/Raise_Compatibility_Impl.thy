(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Raise_Compatibility_Impl
imports 
  Raise_Compatibility
  Auxx.Map_Choice
begin

context
  fixes f_rules :: "'f \<times> nat \<Rightarrow> ('q,'f \<times> nat)ta_rule list"
  and fh_rules :: "('f \<times> nat) \<times> nat \<Rightarrow> ('q,'f \<times> nat)ta_rule list"
  and sig :: "('f \<times> nat) list"
  and bot :: 'q
  and k :: nat
begin
definition k_f_rules :: "'f \<times> nat \<Rightarrow> ('q,'f \<times> nat)ta_rule list list" where
  [code_unfold]: "k_f_rules f \<equiv> generate_lists k (f_rules f)"

definition "generate_entries qs as n fh ps_ts \<equiv>
  let ps = map fst ps_ts;
      pre_ts = map snd ps_ts;
      ts = map (\<lambda> (ai,i). Fun (fst fh, ai) (map (\<lambda> j. pre_ts ! j ! i) [0..< n])) (zip as [0..<k]);
      q_s = [ (qs, r_rhs rl, ts) . rl <- fh_rules (fh,n), r_lhs_states rl = ps]          
    in if q_s = [] then [(qs, bot,ts)] else q_s"

fun decompose_ta_rules where
  "decompose_ta_rules (TA_rule (_,ai) pi qi # rls) = (
    let (as, pis, qs) = decompose_ta_rules rls
    in (ai # as, pi # pis, qi # qs))"
| "decompose_ta_rules [] = ([],[],[])"

definition deduce ::
 "('q list \<Rightarrow> ('q \<times> ('f \<times> nat,'q)term list)list) \<Rightarrow>
  ('q,'f \<times> nat)ta_rule list \<Rightarrow>  
  ('q list \<times> 'q \<times> ('f \<times> nat,'q)term list)list"  where
  "deduce lookup rls = (let 
    (as,pis,qs) = decompose_ta_rules rls;
    n = length (hd pis);
    pps = map (\<lambda> j. (map (\<lambda> p_is. p_is ! j) pis)) [0..< n];
    ps_ts = concat_lists (map lookup pps);
    fh = ((fst o fst o r_sym o hd) rls, max_list as);
    q_ts = remdups_gen (\<lambda> (qs,q,_). (qs,q)) (concat (map (generate_entries  qs as n fh) ps_ts))
    in q_ts)"

definition "all_rlss = concat (map k_f_rules sig)"

function same_base_wit_impl'_main :: "('q list \<times> 'q)set 
  \<Rightarrow> ('q list \<times> 'q \<times> ('f \<times> nat,'q)term list)list
  \<Rightarrow> ('q list \<times> 'q \<times> ('f \<times> nat,'q)term list)list" where
  "same_base_wit_impl'_main have current = (let
      lookup = (\<lambda> qs. [ (q,ts) . (qs',q,ts) <- current, qs = qs']);
      deduced = concat (map (deduce lookup) all_rlss);
      new1 = [ (qs,q,ts) <- deduced . (qs,q) \<notin> have ];
      new2 = remdups_gen (\<lambda> (qs,q,_). (qs,q)) new1
    in if new2 = [] then current else 
     let 
       new_have = have \<union> set (map (\<lambda> (qs,q,_). (qs,q)) new2);
       new_current = new2 @ current
     in same_base_wit_impl'_main new_have new_current)"
  by pat_completeness auto

lemma decompose_ta_rules: assumes "\<And> i. i < k \<Longrightarrow> rls ! i = ((f, ai i) (psi i) \<rightarrow> qi i)"
  and "length rls = k"
  shows "decompose_ta_rules rls = (map ai [0..<k], map psi [0..<k], map qi [0..<k])"
  using assms
proof (induct k arbitrary: rls ai psi qi)
  case (Suc k rls ai psi qi)
  from Suc(3) obtain rl rls' where rls: "rls = rl # rls'" and len: "length rls' = k" by (cases rls, auto)              
  from Suc(2)[of 0] rls have 0: "rl = (f, ai 0) psi 0 \<rightarrow> qi 0" by simp              
  let ?ai = "\<lambda> i. ai (Suc i)"
  let ?psi = "\<lambda> i. psi (Suc i)"
  let ?qi = "\<lambda> i. qi (Suc i)"
  let ?k = "[0 ..< k]"
  {
    fix i
    assume "i < k"
    with Suc(2)[of "Suc i"] rls have "rls' ! i = (f, ?ai i) (?psi i) \<rightarrow> ?qi i" by auto
  }
  from Suc(1)[OF this len] have IH: "decompose_ta_rules rls' = (map ?ai ?k, map ?psi ?k, map ?qi ?k)" by simp
  show ?case unfolding rls map_upt_Suc 0
    by (simp add: IH)
qed simp

lemma k_f_rules[simp]: "set (k_f_rules f) = { rls. length rls = k \<and> set rls \<subseteq> set (f_rules f)}"
  unfolding k_f_rules_def Let_def by (auto split: if_splits)

termination
proof -
  let ?as = "\<lambda> rls. (\<lambda> (as,_,_). as) (decompose_ta_rules rls)"
  let ?pis = "\<lambda> rls. (\<lambda> (_,pis,_). pis) (decompose_ta_rules rls)"
  let ?qs = "\<lambda> rls. (\<lambda> (_,_,qs). qs) (decompose_ta_rules rls)"
  let ?n = "\<lambda> rls. length (hd (?pis rls))"
  let ?fh = "\<lambda> rls. ((fst o fst o r_sym o hd) rls, max_list (?as rls))"
  let ?fh_rules = "\<lambda> rls. fh_rules (?fh rls, ?n rls)"
  define out_rules where "out_rules = concat (map ?fh_rules all_rlss)"
  let ?out = "bot # map r_rhs out_rules"
  define qs_b where "qs_b = map ?qs all_rlss"
  define bound where "bound = { (qs,q). qs \<in> set qs_b \<and> q \<in> set ?out}"
  let ?m = "\<lambda> (have, curr). card (bound - have)"
  show ?thesis
  proof
    fix "have" current xa xb xc xd xe xf
    assume xa: "xa = (\<lambda> qs. [ (q,ts) . (qs',q,ts) <- current, qs = qs'])"
    and xb: "xb = concat (map (deduce xa) all_rlss)"
    and xc: "xc = [(qs, q, ts)\<leftarrow>xb . (qs, q) \<notin> have]"
    and xd: "xd = remdups_gen (\<lambda>(qs, q, _). (qs, q)) xc"
    and ne: "xd \<noteq> []"
    and xe: "xe = have \<union> set (map (\<lambda>(qs, q, uu). (qs, q)) xd)"
    have "bound - xe \<subseteq> bound - have" unfolding xe by auto
    from ne obtain qs_q where xd_mem: "qs_q \<in> set xd" by (cases xd, auto)
    from remdups_gen_elem_imp_elem[OF this[unfolded xd]] have "qs_q \<in> set xc" .
    with xc obtain qs q ts where qs_q: "qs_q = (qs,q,ts)" 
      and mem: "(qs,q,ts) \<in> set xb" 
      and nmem: "(qs,q) \<notin> have"
      by (cases qs_q, auto)
    from nmem xe qs_q xd_mem have "(qs,q) \<in> xe - have" by force
    moreover from mem[unfolded xb] obtain rls where mem: "(qs,q,ts) \<in> set (deduce xa rls)"
      and rls: "rls \<in> set all_rlss" by auto
    from mem[unfolded deduce_def Let_def, simplified]
    obtain qs' pis as
     where decomp: "(as, pis, qs') = decompose_ta_rules rls"
     and mem: "(qs, q, ts)
     \<in> set (remdups_gen  (\<lambda> (qs,q,_). (qs,q)) (concat
                (map (generate_entries qs' as (length (hd pis))
                     (fst (fst (r_sym (hd rls))), max_list as))
                  (concat_lists (map (\<lambda>x. xa (map (\<lambda>p_is. p_is ! x) pis)) [0..<length (hd pis)])))))"
      by blast
    note decomp = decomp[symmetric]
    from remdups_gen_elem_imp_elem[OF mem] obtain ps
    where len: "length ps = length (hd pis)"
      and mem1: "(\<forall>i<length (hd pis). ps ! i \<in> set (xa (map (\<lambda>p_is. p_is ! i) pis)))"
      and mem2: "(qs, q, ts)
      \<in> set (generate_entries qs' as (length (hd pis)) (fst (fst (r_sym (hd rls))), max_list as) ps)" by auto
    note mem2 = mem2[unfolded generate_entries_def Let_def, simplified]
    from mem2 have qs': "qs' = qs" by (auto split: if_splits)
    with decomp rls have qs: "qs \<in> set qs_b" unfolding qs_b_def by force
    have "q \<in> set (bot # map r_rhs out_rules)"
    proof (cases "q = bot")
      case False
      with mem2 obtain rl where 
      rl: "rl \<in> set (fh_rules ((fst (fst (r_sym (hd rls))), max_list as), length (hd pis)))"
      and q: "q = r_rhs rl" by (auto split: if_splits)
      have "rl \<in> set out_rules" using rl unfolding out_rules_def
        by (auto intro!: bexI[OF _ rls] simp: decomp)
      then show ?thesis using q by auto
    qed auto
    with qs have "qs \<in> set qs_b \<and> q \<in> set (bot # map r_rhs out_rules)" by auto
    then have "(qs,q) \<in> bound" unfolding bound_def by auto
    ultimately have "bound - xe \<subset> bound - have" unfolding xe by blast
    moreover have "finite bound" unfolding bound_def using finite_set by auto
    then have "finite (bound - have)" by auto
    ultimately have "card (bound - xe) < card (bound - have)" using psubset_card_mono by blast
    then show "((xe, xf), have, current) \<in> measure ?m"
      by simp
  qed simp
qed

definition same_base_wit_impl' :: "('q list \<times> 'q \<times> ('f \<times> nat,'q)term list)list" where
  "same_base_wit_impl' = same_base_wit_impl'_main {} []"

context
fixes 
  TA :: "('q,'f \<times> nat)ta"
  assumes fh_rules: "\<And> fh. set (fh_rules fh) = { rl \<in> ta_rules TA. r_sym rl = fh }"
  and f_rules: "\<And> f n. set (f_rules (f,n)) = { rl \<in> ta_rules TA. \<exists> h. r_sym rl = ((f,h),n)}"
  and k: "k > 0"
begin
abbreviation "same_base_witt \<equiv> same_base_wit TA bot k"

lemma same_base_wit_impl'_sound: "set same_base_wit_impl' \<subseteq> same_base_witt"
proof -
  {
    fix "have" current
    have "set current \<subseteq> same_base_witt \<Longrightarrow> set (same_base_wit_impl'_main have current) \<subseteq> same_base_witt"
    proof (induct "have" current rule: same_base_wit_impl'_main.induct)
      case (1 "have" current)
      note current = 1(2)
      note IH = 1(1)
      let ?impl = "same_base_wit_impl'_main"
      let ?lookup = "\<lambda>qs. concat (map (\<lambda>(qs', q, ts). if qs = qs' then [(q, ts)] else []) current)"
      let ?deduced = "concat (map (deduce ?lookup) local.all_rlss)"
      define deduced where "deduced = ?deduced" 
      let ?new1 = "[(qs, q, ts)\<leftarrow>deduced . (qs, q) \<notin> have]"
      let ?to_q = "\<lambda> (qs, q, _). (qs, q)"
      let ?new2 = "remdups_gen ?to_q ?new1"
      define new2 where "new2 = ?new2" 
      let ?new_have = "have \<union> set (map ?to_q new2)"
      let ?new_curr = "new2 @ current"
      let ?res = "if new2 = [] then current 
            else ?impl ?new_have ?new_curr"
      have id: "?impl have current = ?res"
        unfolding same_base_wit_impl'_main.simps[of "have"] Let_def deduced_def new2_def by (rule refl)
      show ?case
      proof (cases "new2 = []")
        case True
        show ?thesis unfolding id True using current by auto
      next
        case False
        then have id: "?impl have current = ?impl ?new_have ?new_curr" unfolding id by simp
        have deduced: "deduced = ?deduced" unfolding deduced_def by simp
        have new2: "new2 = ?new2" unfolding new2_def by simp
        show ?thesis unfolding id
        proof (rule IH[OF refl deduced refl new2 False refl refl])
          {
            fix qs q ts
            assume "(qs,q,ts) \<in> set new2" (is "?triple \<in> _")
            from remdups_gen_elem_imp_elem[OF this[unfolded new2]]
            have "?triple \<in> set deduced" by auto
            from this[unfolded deduced]
            obtain rls where rls: "rls \<in> set all_rlss" and 
              deduce: "?triple \<in> set (deduce ?lookup rls)" by auto
            from rls[unfolded all_rlss_def]
            obtain f_n where len_rls: "length rls = k" and rls: "set rls \<subseteq> set (f_rules f_n)" by auto
            obtain f n where f_n: "f_n = (f,n)" by force            
            {
              fix i
              assume i: "i < k"
              then have "rls ! i \<in> set (f_rules (f,n))" using len_rls rls f_n by auto
              from this[unfolded f_rules] obtain h where mem: "rls ! i \<in> ta_rules TA" and rsym: "r_sym (rls ! i) = ((f,h),n)" by auto
              then obtain ps q where "rls ! i = TA_rule (f,h) ps q" and len: "length ps = n" by (cases "rls ! i", auto)
              then have "\<exists> h ps q. rls ! i = TA_rule (f,h) ps q \<and> length ps = n \<and> TA_rule (f,h) ps q \<in> ta_rules TA" using mem by auto
            }
            then have "\<forall> i. \<exists> h ps q. i < k \<longrightarrow> (rls ! i = TA_rule (f,h) ps q \<and> length ps = n \<and> TA_rule (f,h) ps q \<in> ta_rules TA)" by blast
            from choice[OF this] obtain ai where "\<forall> i. \<exists> ps q. i < k \<longrightarrow> (rls ! i = TA_rule (f,ai i) ps q \<and> length ps = n \<and> TA_rule (f,ai i) ps q \<in> ta_rules TA)" by blast
            from choice[OF this] obtain psi where "\<forall> i. \<exists> q. i < k \<longrightarrow> (rls ! i = TA_rule (f,ai i) (psi i) q \<and> length (psi i) = n \<and> TA_rule (f,ai i) (psi i) q \<in> ta_rules TA)" by blast
            from choice[OF this] obtain qi where rls: "\<And> i. i < k \<Longrightarrow> rls ! i = TA_rule (f,ai i) (psi i) (qi i)"
              and len_psi: "\<And> i. i < k \<Longrightarrow> length (psi i) = n"
              and ta_rules: "\<And> i. i < k \<Longrightarrow> TA_rule (f,ai i) (psi i) (qi i) \<in> ta_rules TA" by blast
            let ?k = "[0 ..< k]"
            let ?ai = "map ai ?k"
            let ?psi = "map psi ?k"
            let ?qi = "map qi ?k"
            from rls len_rls have decomp: "decompose_ta_rules rls = (?ai,?psi,?qi)"
              by (rule decompose_ta_rules)
            from len_psi[OF k] have [simp]: "length (hd ?psi) = n" using k by (cases k, auto simp only: map_upt_Suc, auto)
            from rls[OF k] len_rls have [simp]: "hd rls = (f, ai 0) psi 0 \<rightarrow> qi 0" using k by (cases rls, auto)
            from remdups_gen_elem_imp_elem[OF deduce[unfolded deduce_def decomp Let_def split], 
              simplified] obtain ps_ts where 
              len_ps_ts: "length ps_ts = n"
              and all_j: "\<forall> j. \<exists> ts' q'. j < n \<longrightarrow> ((map (\<lambda>x. psi x ! j) ?k, q', ts') \<in> set current
                \<and> ps_ts ! j = (q', ts'))"
              and gen: "(qs, q, ts) \<in> set (generate_entries ?qi ?ai n (f, max_list ?ai) ps_ts)"
              by force
            from choice[OF all_j] obtain ts' where 
              "\<forall> j. \<exists> q'. j < n \<longrightarrow> ((map (\<lambda>x. psi x ! j) ?k, q', (ts' j)) \<in> set current
                \<and> ps_ts ! j = (q', (ts' j)))" by blast
            from choice[OF this] obtain p where 
               in_curr: "\<And> j. j < n \<Longrightarrow> (map (\<lambda>x. psi x ! j) ?k, p j, (ts' j)) \<in> set current"
              and ps_ts: "\<And> j. j < n \<Longrightarrow> ps_ts ! j = (p j, (ts' j))" by blast
            let ?n = "[0 ..< n]"
            let ?ps_ts = "map (\<lambda> j. (p j, ts' j)) ?n"
            have ps_ts: "ps_ts = ?ps_ts" using ps_ts len_ps_ts by (intro nth_equalityI, auto)
            let ?ps = "map p ?n"
            from rls ta_rules have 1: "\<forall>i<k. (f, ?ai ! i) ?psi ! i \<rightarrow> ?qi ! i \<in> ta_rules TA" by auto
            have 2: "\<forall>i<k. length (?psi ! i) = n" using len_psi by simp
            have 3: "length ?ps = n" "length ?ai = k" "length ?psi = k" "length ?qi = k" by simp_all
            have 4: "\<forall>j<n. (map (\<lambda>p_is. p_is ! j) ?psi, ?ps ! j, ts' j) \<in> same_base_witt"
            proof (intro allI impI)
              fix j
              assume j: "j < n"
              show "(map (\<lambda>p_is. p_is ! j) ?psi, ?ps ! j, ts' j) \<in> same_base_witt"
                by (rule set_mp[OF current], insert in_curr[OF j] j, auto simp: o_def)
            qed
            note same_base = same_base_wit[of k f ?ai ?psi ?qi TA n ?ps ts' bot q, OF 1 2 3 k 4]
            define a where "a = max_list ?ai"
            have [simp]: "max_list ?ai = a" unfolding a_def ..
            have [simp]: "zip ?ai ?k = map (\<lambda> i. (ai i, i)) ?k"
              by (rule nth_equalityI, auto)
            have [simp]: "\<And> x. map (\<lambda>j. map ts' ?n ! j ! x) ?n =  map (\<lambda>j. ts' j ! x) ?n"
              by auto
            note o_def[simp] fh_rules[simp]            
            let ?ts = "map (\<lambda>x. Fun (f, ai x) (map (\<lambda>j. ts' j ! x) ?n)) ?k"
            let ?rls = "{rl \<in> ta_rules TA. r_sym rl = ((f, a), n)}"
            let ?cond = "\<forall>xs\<in>(\<lambda>rl. [(map qi [0..<k], r_rhs rl, ?ts)]) `
                     (?rls \<inter> {rl. r_lhs_states rl = ?ps}) \<union>
                     (\<lambda>rl. []) ` (?rls \<inter> {rl. r_lhs_states rl \<noteq> ?ps}). xs = []"
            from gen[unfolded ps_ts generate_entries_def, simplified] 
            have mem: "(qs, q, ts) \<in> set (if ?cond
             then [(?qi, bot, ?ts)]
             else concat
                   (map (\<lambda>rl. if r_lhs_states rl = ?ps then [(?qi, r_rhs rl, ?ts)] else [])
                     (fh_rules ((f, a), n))))" by (simp add: Let_def)
            from mem have id: "qs = ?qi" "ts = ?ts" by (auto split: if_splits)
            have idd: "map (\<lambda>i. Fun (f, ?ai ! i) (map (\<lambda>j. ts' j ! i) ?n)) ?k = ?ts"
              by simp
            have 6: "(f, max_list ?ai) ?ps \<rightarrow> q \<in> ta_rules TA \<or>
              \<not> (\<exists>q. (f,  max_list ?ai) ?ps \<rightarrow> q \<in> ta_rules TA) \<and> q = bot"
            proof (cases ?cond)
              case False
              then have "?cond = False" by simp
              from mem[unfolded this] obtain rl
              where mem: "rl \<in> ta_rules TA" 
              and rl: "r_sym rl = ((f, a), n)" "r_lhs_states rl = ?ps" "q = r_rhs rl"
                by auto
              then show ?thesis unfolding a_def by (cases rl, auto)
            next
              case True
              then have "?cond = True" by simp
              from mem[unfolded this] have q: "q = bot" by simp
              show ?thesis unfolding a_def[symmetric]
              proof (intro disjI2 conjI[OF _ q] notI)
                assume "\<exists>q. (f, a) ?ps \<rightarrow> q \<in> ta_rules TA"
                then obtain q where "(f, a) ?ps \<rightarrow> q \<in> ta_rules TA" by auto
                then have "(f,a) ?ps \<rightarrow> q \<in> ?rls \<inter> {rl. r_lhs_states rl = ?ps}" by auto
                with True show False by blast
              qed
            qed
            have "?triple \<in> same_base_witt" unfolding id
              by (rule same_base[unfolded idd, OF 6])
          }
          with current show "set (new2 @ current) \<subseteq> same_base_witt" by auto
        qed
      qed
    qed
  } note main = this
  show ?thesis unfolding same_base_wit_impl'_def 
    by (rule main, auto)
qed

lemma same_base_wit_impl'_complete: assumes sig: "\<And> f h n. ((f,h),n) \<in> ta_syms TA \<Longrightarrow> (f,n) \<in> set sig"
  and mem: "(qs,q,ss) \<in> same_base_witt"
  shows "\<exists> ss'. (qs,q,ss') \<in> set same_base_wit_impl'"
proof -
  let ?lookup = "\<lambda> curr. (\<lambda> qs. [ (q,ts) . (qs',q,ts) <- curr, qs = qs'])"
  let ?deduced = "\<lambda> curr. concat (map (deduce (?lookup curr)) all_rlss)"
  let ?new1 = "\<lambda> have curr. [ (qs,q,ts) <- ?deduced curr. (qs,q) \<notin> have ]"
  let ?new2 = "\<lambda> have curr. remdups_gen (\<lambda> (qs,q,_). (qs,q)) (?new1 have curr)"
  {
    fix "have" :: "('q list \<times> 'q) set" and current :: "('q list \<times> 'q \<times> ('f \<times> nat, 'q)term list) list"
    assume "have = {(qs,q) . \<exists> t. (qs,q,t) \<in> set current}"
    then have "\<exists> ss'. (qs, q, ss') \<in> set (same_base_wit_impl'_main have current)"
    proof (induct "have" current rule: same_base_wit_impl'_main.induct)
      case (1 have' current)
      note have' = 1(2)
      note IH = 1(1)
      note simp = same_base_wit_impl'_main.simps[of have'] Let_def
      show ?case
      proof (cases "?new2 have' current = []")
        case True note new2 = this
        have id: "same_base_wit_impl'_main have' current = current"
          unfolding simp True by simp
        from mem show ?thesis unfolding id
        proof (induct rule: same_base_wit.induct)
          case (same_base_wit f as pis qs n ps ts q)
          note * = this
          note rules = *(1)[rule_format]
          note len = *(2-6)[rule_format]
          note k = *(7)
          note IH = *(8)[rule_format]
          note q = *(9)
          show ?case
          proof (cases "(qs,q) \<in> have'")
            case True
            with have' show ?thesis by auto
          next
            case False
            from new2 have new1: "?new1 have' current = []" by (cases "?new1 have' current", auto)
            {
              fix j
              assume j: "j < n"
              from IH[OF j] len have "\<exists> ss. (map (\<lambda>p_is. p_is ! j) pis, ps ! j, ss) \<in> set current" by auto
            }
            then have "\<forall> j. \<exists> ss. j < n \<longrightarrow> (map (\<lambda>p_is. p_is ! j) pis, ps ! j, ss) \<in> set current" by blast
            from choice[OF this] obtain ss where 
              rec: "\<And> j. j < n \<Longrightarrow> (map (\<lambda>p_is. p_is ! j) pis, ps ! j, ss j) \<in> set current" 
              by auto      
            let ?n = "[0 ..< n]"
            let ?k = "[0 ..< k]"
            let ?ss = "map ss ?n"
            let ?rls = "map (\<lambda> i. (f, as ! i) (pis ! i) \<rightarrow> qs ! i) ?k"
            from rules[OF k] len(1)[OF k] have "((f,as ! 0),n) \<in> ta_syms TA" 
              by (force simp: ta_syms_def)
            from sig[OF this] have fn: "(f,n) \<in> set sig" .
            have "?rls \<in> set (k_f_rules (f,n))" unfolding k_f_rules f_rules using len(1) rules by auto
            then have in_all: "?rls \<in> set all_rlss" unfolding all_rlss_def using fn by auto
            let ?ts = "map (\<lambda> i. Fun (f,as ! i) (map (\<lambda> j. ss j ! i) ?n)) ?k"
            have "decompose_ta_rules (map (\<lambda>i. (f, as ! i) pis ! i \<rightarrow> qs ! i) ?k) = 
              (map (\<lambda> j. as ! j) ?k, map (\<lambda> j. pis ! j) ?k, map (\<lambda> j. qs ! j) ?k)"
              by (rule decompose_ta_rules, auto)
            also have "\<dots> = (as,pis,qs)" using len
              by (auto intro: nth_equalityI)
            finally have decomp: "decompose_ta_rules (map (\<lambda>i. (f, as ! i) pis ! i \<rightarrow> qs ! i) ?k) = (as,pis,qs)" by auto
            have [simp]: "\<And> f. hd (map f ?k) = f 0" using k by (cases k, auto simp only: map_upt_Suc, auto)
            have [simp]: "length (hd pis) = n" using k len(4) len(1)[of 0] by (cases pis, auto)
            let ?ps_ts = "map (\<lambda> i. (ps ! i, ss i)) ?n"
            have wit: "\<exists> a. length a = n \<and>
              (\<forall>i<n. \<exists>ts ps. (map (\<lambda>p_is. p_is ! i) pis, ps, ts) \<in>set current \<and> a ! i = (ps, ts)) \<and>
              (qs, q, ?ts) \<in> set (generate_entries qs as n (f, max_list as) a)"
            proof (rule exI[of _ ?ps_ts], intro conjI allI impI, force)
              fix j
              assume j: "j < n"
              show "\<exists>ts psa.
                  (map (\<lambda>p_is. p_is ! j) pis, psa, ts) \<in> set current \<and>
                  ?ps_ts ! j = (psa, ts)"
                by (rule exI[of _ "snd (?ps_ts ! j)"], rule exI[of _ "fst (?ps_ts ! j)"], 
                insert rec[OF j] j, auto)
            next
              have [simp]: "map (\<lambda>(ai, i). Fun (f, ai) (map (\<lambda>j. map ss ?n ! j ! i) ?n)) (zip as ?k)
               = map (\<lambda> i. Fun (f, as ! i) (map (\<lambda>j. ss j ! i) ?n)) ?k"
                using len(3) by (intro nth_equalityI, auto)
              have [simp]: "\<And> as bs. (\<forall>xs\<in> as \<union> (\<lambda>rl. []) ` bs . xs = []) = (\<forall> xs \<in> as. xs = [])" by auto
              have [simp]: "map ((!) ps) ?n = ps" using len(2) by (intro nth_equalityI, auto)
              define ts where "ts = ?ts" 
              have ts: "ts = map (\<lambda>i. Fun (f, as ! i) (map (\<lambda>j. ss j ! i) ?n)) ?k" unfolding ts_def by simp            
              let ?cond = "\<forall>xs. r_sym xs = ((f, max_list as), n) \<longrightarrow> xs \<in> ta_rules TA \<longrightarrow> r_lhs_states xs \<noteq> ps"
              have gen: "set (generate_entries qs as n (f, max_list as) ?ps_ts) =
                set (let ts' = ts
                  in if ?cond then [(qs, bot, ts')] else 
                  concat (map (\<lambda>rl. if r_lhs_states rl = ps then [(qs, r_rhs rl, ts')] else [])
                             (fh_rules ((f, max_list as), n))))"
                unfolding generate_entries_def ts_def
                by (simp add: fh_rules o_def)        
              show "(qs, q, ?ts) \<in> set (generate_entries qs as n (f, max_list as) ?ps_ts)"
                using q
              proof 
                assume mem: "(f, max_list as) ps \<rightarrow> q \<in> ta_rules TA" (is "?rl \<in> _")
                then have c: "?cond = False" by (auto intro: exI[of _ ?rl] simp: len)
                show ?thesis unfolding ts_def[symmetric] gen Let_def c if_False
                  unfolding gen Let_def using mem
                  by (auto intro: bexI[of _ ?rl] simp: fh_rules len)
              next
                assume *: "\<not> (\<exists>q. (f, max_list as) ps \<rightarrow> q \<in> ta_rules TA) \<and> q = bot"
                {
                  assume "?cond = False"
                  then obtain rl where "r_sym rl = ((f, max_list as), n)" "rl \<in> ta_rules TA" "r_lhs_states rl = ps"
                    by auto
                  with len(2) * have False by (cases rl, auto)
                } then have c: "?cond = True" by auto
                from * have q: "q = bot" by simp
                show ?thesis unfolding ts_def[symmetric] gen Let_def c if_True q by simp
              qed
            qed
            have "\<exists> wit \<in> set (deduce (?lookup current) ?rls).  (\<lambda> (qs,q,_). (qs,q)) (qs,q,?ts) =  (\<lambda> (qs,q,_). (qs,q)) wit"
              unfolding deduce_def Let_def decomp split[of _ as] split[of _ pis] o_def
              by (rule elem_imp_remdups_gen_elem, insert wit, force)
            then obtain wit where wit: "wit \<in> set (deduce (?lookup current) ?rls)" and id: "(qs,q) = (\<lambda> (qs,q,_). (qs,q)) wit" by auto
            obtain a b c where wit_id: "wit = (a,b,c)" by (cases wit, auto)
            from wit wit_id id obtain ts where "(qs,q,ts) \<in> set (deduce (?lookup current) ?rls)" by auto
            then have "(qs,q,ts) \<in> set (?deduced current)" using in_all by auto
            then have "(qs,q,ts) \<in> set (?new1 have' current)" using False by auto
            with new1 have False by auto
            then show ?thesis ..
          qed
        qed
      next
        case False
        then have id: "(?new2 have' current = []) = False" by simp
        show ?thesis unfolding simp id if_False
          by (rule IH[OF refl refl refl refl False refl refl], force simp: have')
      qed
    qed
  } note main = this
  from this[of "{}" Nil] show ?thesis unfolding same_base_wit_impl'_def by auto
qed

end
end

definition same_base_wit_impl 
  :: "'q \<Rightarrow> ('q, ('f :: compare_order) \<times> nat)ta_rule list \<Rightarrow> nat \<Rightarrow> ('q list \<times> 'q \<times> ('f \<times> nat,'q)term list)list" where
  "same_base_wit_impl b ta k \<equiv> let 
     sig = remdups (map ((\<lambda> ((f,h),n). (f,n)) o r_sym) ta);
     sig_fh = remdups (map r_sym ta);
     fh_rules = precompute_fun (\<lambda> f. filter (\<lambda> rl. r_sym rl = f) ta) sig_fh;
     f_rules = precompute_fun (\<lambda> f. filter (\<lambda> rl. (\<lambda> ((g,h),n). (g,n)) (r_sym rl) = f) ta) sig
   in (if k = 0 then [] else same_base_wit_impl' f_rules fh_rules sig b k)"

lemma same_base_wit_impl: assumes ta: "set ta = ta_rules TA"
  shows 
    "set (same_base_wit_impl b ta k) \<subseteq> same_base_wit TA b k"
    "(qs,q,ss) \<in> same_base_wit TA b k \<Longrightarrow> \<exists> ts. (qs,q,ts) \<in> set (same_base_wit_impl b ta k)"
proof -
  note d = same_base_wit_impl_def Let_def if_True if_False
  show "set (same_base_wit_impl b ta k) \<subseteq> same_base_wit TA b k" 
  proof (cases "k = 0")
    case True show ?thesis unfolding d True by auto
  next
    case False
    then have k: "(k = 0) = False" and k0: "k > 0" by auto
    show ?thesis unfolding d k
      by (rule same_base_wit_impl'_sound[of _ TA _ k _ b, OF _ _ k0], 
        auto simp: ta split: prod.splits, (case_tac x, auto)+)
  qed
  assume mem: "(qs,q,ss) \<in> same_base_wit TA b k"
  then have k0: "k > 0" by (cases, auto)
  then have k: "(k = 0) = False" by auto
  show "\<exists> ts. (qs,q,ts) \<in> set (same_base_wit_impl b ta k)" unfolding d k
    by (rule same_base_wit_impl'_complete[OF _ _ k0 _ mem],
    auto simp: ta ta_syms_def split: prod.splits, ((case_tac x, auto)+)[2], 
    case_tac x, force simp: o_def)
qed

definition "same_base_impl b ta k = map (\<lambda> (q,qs,_). (q,qs)) (same_base_wit_impl b ta k)"

lemma same_base_impl: assumes ta: "set ta = ta_rules TA"
  shows "set (same_base_impl b ta k) = same_base TA b k"
  using same_base_wit_impl[OF ta, where k = k and b = b]
  unfolding same_base_impl_def same_base_def
  by force

definition "remark_42 \<equiv>
 [
      (''f'',0) [0,0] \<rightarrow> 2,
      (''f'',0) [1,0] \<rightarrow> 3,
      (''f'',0) [1,1] \<rightarrow> 2,
      (''a'',0) [] \<rightarrow> 0,
      (''a'',1) [] \<rightarrow> 1
 ] :: (int, string \<times> nat)ta_rule list"
    
definition "ex_54 \<equiv>
 [
      (''f'',0) [1] \<rightarrow> 1,
      (''f'',1) [2] \<rightarrow> 1,
      (''g'',0) [1] \<rightarrow> 1,
      (''g'',1) [1] \<rightarrow> 2,
      (''c'',0) [] \<rightarrow> 1,
      (''h'',0) [1,1] \<rightarrow> 1,
      (''i'',0) [1,1] \<rightarrow> 1,
      (''i'',1) [1,1] \<rightarrow> 1
 ] :: (int, string \<times> nat)ta_rule list"

definition "ex_55 \<equiv>
 [
      (''f'',0) [1,1] \<rightarrow> 1,
      (''f'',1) [2,1] \<rightarrow> 1,
      (''a'',0) [] \<rightarrow> 1,
      (''a'',1) [] \<rightarrow> 2
 ] :: (int, string \<times> nat)ta_rule list"

value(code) "same_base_impl 666 remark_42 2" 
value(code) "same_base_wit_impl 666 ex_54 2" 
value(code) "same_base_wit_impl 666 ex_55 2"

end
