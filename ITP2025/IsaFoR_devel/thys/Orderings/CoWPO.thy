(* Dohan Kim,
   Akihisa Yamada,
   René Thiemann *)
theory CoWPO
  imports
    Weighted_Path_Order.WPO
    Term_Order
    Lexicographic_Extension_More
begin

locale pre_order_pair' = 
  fixes S :: "'a rel"
    and NS :: "'a rel"
  assumes refl_NS: "refl NS"
    and irrefl_S: "irrefl S"
    and trans_NS: "trans NS"
    and S_imp_NS: "S \<subseteq> NS"
begin
lemma refl_NS_point: "(s, s) \<in> NS" using refl_NS unfolding refl_on_def by blast
end

locale order_pair' = pre_order_pair' S NS + compat_pair S NS 
  for S NS :: "'a rel"
begin
sublocale order_pair S NS
proof
  show "refl NS" by (rule refl_NS)
  show "trans NS" by (rule trans_NS)
  show "trans S" using compat_S_NS S_imp_NS unfolding trans_def by auto
qed
end

(* Definition 7 *)
fun co_compatible :: "('a rel \<times> 'a rel) \<Rightarrow> ('a rel \<times> 'a rel) \<Rightarrow> bool" where
  "co_compatible (R1, R2) (R3, R4) = ((R1 \<inter> (R4)^-1 = {}) \<and> (R2 \<inter> (R3)^-1 = {}))"

(* Proposition 3 *)
lemma co_comp_itself:
  assumes o_pair:"order_pair' R2 R1"
  shows "co_compatible (R1, R2) (R1, R2)"
proof (rule ccontr)
  assume asm:"\<not> ?thesis"
  hence ctr: "((R1 \<inter> (R2)^-1 \<noteq> {}) \<or> (R2 \<inter> (R1)^-1 \<noteq> {}))" by simp
  then obtain a b c d where ab:"(a, b) \<in> R1" and cd:"(c, d) \<in> R2" 
    and o1: "((a, b) \<in> R1 \<and> (d, c) \<in> R2) \<or> ((c, d) \<in> R2 \<and> (b, a) \<in> R1)"
    using compat_pair.compat_S_NS_point converseE disjoint_iff o_pair order_pair'_def by metis
  from cd have "(c, d) \<in> R1" using o_pair
    by (meson in_mono order_pair'.axioms(1) pre_order_pair'_def)
  then have ndc: "(d, c) \<notin> R2" 
    by (meson compat_pair.compat_NS_S_point irrefl_def o_pair order_pair'_def pre_order_pair'_def)
  with o1 have "(c, d) \<in> R2 \<and> (b, a) \<in> R1" by simp
  from ab have nba: "(b, a) \<notin> R1" using compat_pair.compat_NS_S_point converseE ctr disjoint_iff irrefl_def o_pair 
      order_pair'.axioms pre_order_pair'.irrefl_S by (smt (verit, ccfv_threshold))
  from o1 ndc nba show False by simp
qed


locale prc_compat' = 
  fixes gt_prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
    and ge_prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
  assumes prc_compat1: "gt_prc f g \<Longrightarrow> ge_prc g h \<Longrightarrow> gt_prc f h"
    and prc_compat2: "ge_prc f g \<Longrightarrow> gt_prc g h \<Longrightarrow> gt_prc f h"
    and trans_ge_prc: "ge_prc f g \<Longrightarrow> ge_prc g h \<Longrightarrow> ge_prc f h" 
  

locale cowpo = 
  fixes n :: nat
    and \<pi> :: "'f status"
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and nleA nltA :: "('f, 'v) term rel"
    and S NS :: "('f, 'v) term rel"
    and nle_prc nlt_prc:: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
    and gt_prc ge_prc:: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
begin
sublocale co: wpo n nleA nltA "(\<lambda> f g. (nle_prc f g, nlt_prc f g))" "(\<lambda> _. False)" \<pi> c False "(\<lambda> _. False)" .
sublocale essential: wpo n S NS "(\<lambda> f g. (gt_prc f g, ge_prc f g))" "(\<lambda> _. False)" \<pi> c False "(\<lambda> _. False)" .

abbreviation cowpo_s (infix "\<sqsupset>" 50) where "s \<sqsupset> t \<equiv> fst (co.wpo s t)"
abbreviation cowpo_ns (infix "\<sqsupseteq>" 50) where "s \<sqsupseteq> t \<equiv> snd (co.wpo s t)"
abbreviation cowpo_inv_s (infix "\<sqsubset>" 50) where "s \<sqsubset> t \<equiv> t \<sqsupset> s"
abbreviation cowpo_inv_ns (infix "\<sqsubseteq>" 50) where "s \<sqsubseteq> t \<equiv> t \<sqsupseteq> s"

abbreviation wpo_s (infix "\<succ>" 50) where "s \<succ> t \<equiv> fst (essential.wpo s t)"
abbreviation wpo_ns (infix "\<succeq>" 50) where "s \<succeq> t \<equiv> snd (essential.wpo s t)"
abbreviation wpo_inv_s (infix "\<prec>" 50) where "s \<prec> t \<equiv> t \<succ> s"

abbreviation "COWPO_S \<equiv> {(s,t). s \<sqsupset> t}"
abbreviation "COWPO_NS \<equiv> {(s,t). s \<sqsupseteq> t}"
abbreviation "COWPO_INV_S \<equiv> {(s,t). s \<sqsubset> t}"
abbreviation "COWPO_INV_NS \<equiv> {(s,t). s \<sqsubseteq> t}"

abbreviation "WPO_S \<equiv> {(s,t). s \<succ> t}"
abbreviation "WPO_NS \<equiv> {(s,t). s \<succeq> t}"

lemma cowpo_s_imp_ns: "s \<sqsupset> t \<Longrightarrow> s \<sqsupseteq> t"
  by (rule wpo.wpo_s_imp_ns)

end

locale cowpo_with_assms = order_pair' + cowpo + irrefl_precedence "\<lambda> f g. (gt_prc f g, ge_prc f g)" "\<lambda> f. False" +
  constrains S :: "('f, 'v) term rel" and NS :: _
    and n :: nat
    and \<pi> :: "'f status"
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and nleA  :: "('f, 'v) term rel" and nltA :: _
    and nle_prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool" and nlt_prc :: _
    and gt_prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool" and ge_prc :: _
  assumes subst_S: "(s,t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S"
    and subst_NS: "(s,t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS"
    and nleA: "nleA = {(s,t). \<forall> \<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> NS}"
    and nltA: "nltA = {(s,t). \<forall> \<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> S}"
    and gt_prc_comp: "nlt_prc u v = (\<not> gt_prc v u)"
    and ge_prc_comp: "nle_prc w z = (\<not> ge_prc z w)"
begin

lemma subst_nltA: assumes "(s,t) \<in> nltA" 
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> nltA"
  unfolding nltA
proof (clarify, goal_cases)
  case (1 \<delta>)
  from assms[unfolded nltA, simplified, rule_format, of "\<sigma> \<circ>\<^sub>s \<delta>"] 1
  show ?case by simp
qed

lemma subst_nleA: assumes "(s,t) \<in> nleA" 
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> nleA"
  unfolding nleA
proof (clarify, goal_cases)
  case (1 \<delta>)
  from assms[unfolded nleA, simplified, rule_format, of "\<sigma> \<circ>\<^sub>s \<delta>"] 1
  show ?case by simp
qed

lemma neg_nleA: "(s,t) \<in> nleA \<Longrightarrow> (t,s) \<notin> NS" 
  unfolding nleA by (auto dest: spec[of _ Var] )

lemma neg_nltA: "(s,t) \<in> nltA \<Longrightarrow> (t,s) \<notin> S" 
  unfolding nltA by (auto dest: spec[of _ Var] )

lemma  ge_prc_refl: "ge_prc f f = True"
    and gt_prc_irrefl: "gt_prc f f = False"
    and incl_gt_ge_prc: "gt_prc x y \<Longrightarrow> ge_prc x y"
  using prc_refl[of f] prc_stri_imp_nstri[of x y] by auto


sublocale essential: wpo_with_basic_assms n S NS "(\<lambda> f g. (gt_prc f g, ge_prc f g))" "(\<lambda> _. False)" \<pi> c False "(\<lambda> _. False)"
  by ((unfold_locales; (intro S_imp_NS irrefl_S subst_S subst_NS)?), 
      auto simp: ge_prc_refl gt_prc_irrefl incl_gt_ge_prc)  

lemma refl_nltA_point: "(s, s) \<in> nltA" unfolding nltA using irrefl_S irrefl_def by fastforce
lemma irrefl_nle_prc: "nle_prc f f = False" by (simp add: ge_prc_comp ge_prc_refl)
lemma refl_nlt_prc: "nlt_prc f f = True" by (simp add: gt_prc_comp gt_prc_irrefl)
lemma nleA_imp_nltA: "nleA \<subseteq> nltA" using S_imp_NS unfolding nleA nltA by auto

lemmas \<pi>E = essential.\<sigma>E

lemma nltA_arg: 
  assumes i: "strictly_simple_status \<pi> nltA"
    and "i \<in> set (status \<pi> (f,length ts))"
  shows "(Fun f ts, ts ! i) \<in> nltA" 
  using assms unfolding simple_arg_pos_def strictly_simple_status_def by simp

lemmas nleA_imp_cowpo_s = co.S_imp_wpo_s

lemma cowpo_ns_imp_nltA: "s \<sqsupseteq> t \<Longrightarrow> (s, t) \<in> nltA"
  using nleA_imp_nltA
  by (cases s, auto simp: co.wpo.simps[of _ t] , cases t, 
      auto simp: refl_nltA_point split: if_splits)

lemma cowpo_s_imp_gta: "s \<sqsupset> t \<Longrightarrow> (s, t) \<in> nltA"
  by (rule cowpo_ns_imp_nltA[OF cowpo_s_imp_ns])

lemma cowpo_ns_refl:
  assumes ss:"strictly_simple_status \<pi> nltA"
  shows "s \<sqsupseteq> s"
proof (induct s)
  case (Var x)
  then show ?case using co.wpo.simps[of s s]
    by (simp add: refl_nltA_point wpo.wpo.simps)
next
  case (Fun f ss)
  let ?f = "(f,length ss)" 
  {
    fix i
    assume si: "i \<in> set (status \<pi> ?f)"
    have ns:"(Fun f ss, ss ! i) \<in> nltA"
      using nltA_arg [OF ss si] by blast
    have "Fun f ss \<sqsupset> ss ! i" using si ns co.wpo.simps[of "Fun f ss" "ss ! i"]
      using Fun status_aux by fastforce
  } note cowpo_s = this
  let ?ss = "map (\<lambda> i. ss ! i) (status \<pi> ?f)"
  have rec_lex: "snd (lex_ext co.wpo n ?ss ?ss)" 
    by (rule all_nstri_imp_lex_nstri, insert \<pi>E[of _ f ss], auto simp: Fun)
  have rec_mul: "snd (mul_ext co.wpo ?ss ?ss)" 
    by (rule all_nstri_imp_mul_nstri, insert \<pi>E[of _ f ss], auto simp: Fun)
  have "nlt_prc ?f ?f" using gt_prc_comp using gt_prc_irrefl by blast
  with rec_lex rec_mul show ?case using refl_nltA_point cowpo_s co.wpo.simps[of "Fun f ss" "Fun f ss"] Fun 
    by (cases "c ?f"; simp add: Let_def)
qed

lemma wpo_ns_pre_mono: 
  fixes f and bef aft :: "('f,'v)term list"
  defines "\<pi>f \<equiv> (status \<pi>) (f, Suc (length bef + length aft))"
  assumes rel: "s \<succeq> t"
    and ss: "strictly_simple_status \<pi> NS"
    and ctxt_NS: "(s,t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS" 
  shows "(\<forall>j\<in>set \<pi>f. Fun f (bef @ s # aft) \<succ> (bef @ t # aft) ! j)
    \<and> (Fun f (bef @ s # aft), (Fun f (bef @ t # aft))) \<in> NS
    \<and> (\<forall> i < length \<pi>f. ((map ((!) (bef @ s # aft)) \<pi>f) ! i) \<succeq> ((map ((!) (bef @ t # aft)) \<pi>f) ! i))"
    (is "_ \<and> _ \<and> ?three")
  unfolding \<pi>f_def
  by (rule essential.wpo_ns_pre_mono'[OF ss ctxt_NS rel]) 

lemma WPO_NS_ctxt: 
  assumes ss: "strictly_simple_status \<pi> NS"
    and ctxt_NS: "(s,t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS" 
  shows"(s,t) \<in> WPO_NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> WPO_NS" 
  using essential.wpo_ns_mono'[OF ss] ctxt_NS by blast

lemma ssimple_status: assumes pisimple: "strictly_simple_status \<pi> NS"
shows "strictly_simple_status \<pi> nltA"
  unfolding strictly_simple_status_def
proof (intro allI impI)
  fix f and ts :: "('f,'v)term list" and  i
  assume i: "i \<in> set (essential.\<sigma> (f,length ts))" 
  show "(Fun f ts, ts ! i) \<in> nltA" 
    unfolding nltA
  proof (clarify)
    fix \<sigma>
    assume tsi:"( ts ! i \<cdot> \<sigma>, Fun f ts \<cdot> \<sigma>) \<in> S"
    from i pisimple have ftsi:"(Fun f ts, ts ! i) \<in> NS" unfolding strictly_simple_status_def by simp
    hence ftsi: "(Fun f ts \<cdot> \<sigma>, ts ! i \<cdot> \<sigma>) \<in> NS" by (rule subst_NS)
    have "order_pair' S NS" ..
    with ftsi tsi show False
      by (meson compat_pair.compat_NS_S_point irrefl_def order_pair'_def pre_order_pair'.irrefl_S)
  qed
qed

(* Lemma 4 *)
lemma cowpo_stable:
  fixes \<delta> :: "('f,'v)subst"
  assumes ss:"strictly_simple_status \<pi> nltA"
  shows "(s \<sqsupset> t \<longrightarrow> s \<cdot> \<delta> \<sqsupset> t \<cdot> \<delta>) \<and> (s \<sqsupseteq> t \<longrightarrow> s \<cdot> \<delta> \<sqsupseteq> t \<cdot> \<delta>)"
    (is "?p s t")
proof (induct "(s,t)" arbitrary:s t rule: wf_induct[OF wf_measure[of "\<lambda> (s,t). size s + size t"]])
  case (1 s t)
  from 1
  have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> ?p s' t'" by auto
  note IH = this[rule_format]
  let ?s = "s \<cdot> \<delta>"
  let ?t = "t \<cdot> \<delta>"
  note simps = co.wpo.simps[of s t] co.wpo.simps[of ?s ?t]
  show "?case"
  proof (cases "((s,t) \<in> nleA \<or> (?s,?t) \<in> nleA) \<or> ((s,t) \<notin> nltA \<or> \<not> s \<sqsupseteq> t)")
    case True
    then show ?thesis
    proof
      assume "(s,t) \<in> nleA \<or> (?s,?t) \<in> nleA"
      with subst_nleA[of s t \<delta>] have "(?s,?t) \<in> nleA" by auto
      from nleA_imp_cowpo_s[OF this] have "?s \<sqsupset> ?t" .
      then show ?thesis by (simp add: cowpo_s_imp_ns)
    next
      assume "(s,t) \<notin> nltA \<or> \<not> cowpo_ns s t"
      with cowpo_ns_imp_nltA have st: "\<not> s \<sqsupseteq> t" by auto
      with cowpo_s_imp_ns have "\<not> s \<sqsupset> t" by auto
      with st show ?thesis using "1.prems" by blast
    qed
  next
    case False
    then have not: "((s,t) \<in> nleA) = False" "((?s,?t) \<in> nleA) = False" 
      and stA: "(s,t) \<in> nltA" and ns: "cowpo_ns s t" by auto
    from subst_nltA[OF stA] have sstsA: "(?s,?t) \<in> nltA" by auto
    from stA sstsA have id: "((s,t) \<in> nltA) = True" "((?s,?t) \<in> nltA) = True" by auto
    note simps = simps[unfolded id not if_False if_True]
    show ?thesis
    proof (cases s)
      case (Var x) note s = this
      show ?thesis
      proof (cases t)
        case (Var y) note t = this
        then show ?thesis unfolding simps using s t cowpo_ns_refl[OF ss] 
          using simps(2) by (smt (z3) Pair_inject Term.term.simps(5) prod.collapse)
      next
        case (Fun g ts) note t = this
        let ?g = "(g,length ts)"
        show ?thesis
        proof (cases "\<delta> x")
          case (Var y)
          then show ?thesis unfolding simps unfolding s t
            using "1.prems" s simps(1) by force
        next
          case (Fun f ss)
          let ?f = "(f, length ss)"
          show ?thesis unfolding simps unfolding s t using "1.prems" s simps(1) Fun by auto
        qed
      qed
    next
      case (Fun f ss) note s = this
      let ?f = "(f,length ss)"
      let ?ss = "set (status \<pi> ?f)"
      {
        fix i
        assume i: "i \<in> ?ss" and ns: "(ss ! i) \<sqsupseteq> t"
        from IH[of "ss ! i" t] \<pi>E[OF i] ns have "(ss ! i \<cdot> \<delta>) \<sqsupseteq> ?t" using s by (auto simp: size_simps)
        then have "?s \<sqsupset> ?t" unfolding simps unfolding s using i sstsA set_status_nth by fastforce
        with cowpo_s_imp_ns[OF this] have ?thesis by blast
      } note si_arg = this        
      show ?thesis
      proof (cases t)
        case t: (Var y) 
        show ?thesis
        proof (cases "\<exists>i\<in>?ss. (ss ! i) \<sqsupseteq> t")
          case True
          then obtain i
            where si: "i \<in> ?ss" and ns: "(ss ! i) \<sqsupseteq> t" 
            unfolding s t by auto
          from si_arg[OF this] show ?thesis .
        next
          case False
          from False s t not 
          have "\<not> s \<sqsupset> t" unfolding simps by auto
          moreover          
          have "?s \<sqsupseteq> ?t" 
          proof (cases "\<delta> y")
            case (Var z)
            show ?thesis unfolding co.wpo.simps[of ?s ?t] not id 
              unfolding s t using Var
              using False ns s simps(1) t by fastforce
          next
            case (Fun g ts)
            then show ?thesis using s t simps 
              using False ns by force 
          qed
          ultimately show ?thesis by blast
        qed
      next
        case (Fun g ts) note t = this
        let ?g = "(g,length ts)"
        let ?ts = "set (status \<pi> ?g)"
        note ns = ns[unfolded simps, unfolded s t term.simps split]
        show ?thesis
        proof (cases "\<exists> i \<in> ?ss. (ss ! i) \<sqsupseteq> t")
          case True
          with si_arg show ?thesis by blast
        next
          case False
          then have id: "(\<exists> i \<in> ?ss. (ss ! i) \<sqsupseteq> (Fun g ts)) = False" unfolding t by auto
          note ns = ns[unfolded this if_False]
          let ?mss = "map (\<lambda> s . s \<cdot> \<delta>) ss"
          let ?mts = "map (\<lambda> t . t \<cdot> \<delta>) ts"
          from ns have s_tj: "\<And> j. j \<in> ?ts \<Longrightarrow> (Fun f ss) \<sqsupset> (ts ! j)" and gtprnc:"nlt_prc ?f ?g"
            by (auto split: if_splits)
          {
            fix j
            assume j: "j \<in> ?ts"
            from \<pi>E[OF this]
            have "size s + size (ts ! j) < size s + size t" unfolding t by (auto simp: size_simps)
            from IH[OF this] s_tj[OF j, folded s] have cowpo: "?s \<sqsupset> (ts ! j \<cdot> \<delta>)" by auto
            from j have "j < length ts" by (simp add: set_status_nth)
            with cowpo have "?s \<sqsupset> (?mts ! j)" by auto
          } note ss_ts = this
          note \<pi>E = \<pi>E[of _ f ss] \<pi>E[of _ g ts]
          show ?thesis
          proof (cases "nle_prc ?f ?g")
            case True
            with ss_ts sstsA have "?s \<sqsupset> ?t" unfolding simps unfolding s t using gtprnc by simp
            with cowpo_s_imp_ns[OF this] show ?thesis by blast
          next
            case False
            let ?mmss = "map ((!) ss) (status \<pi> ?f)"
            let ?mmts = "map ((!) ts) (status \<pi> ?g)"
            let ?Mmss = "map ((!) ?mss) (status \<pi> ?f)"
            let ?Mmts = "map ((!) ?mts) (status \<pi> ?g)"
            have id_map: "?Mmss = map (\<lambda> t. t \<cdot> \<delta>) ?mmss" "?Mmts = map (\<lambda> t. t \<cdot> \<delta>) ?mmts"
              unfolding map_map o_def by (auto simp: set_status_nth)
            let ?ls = "length (status \<pi> ?f)"
            let ?lt = "length (status \<pi> ?g)"
            {
              fix si tj
              assume *: "si \<in> set ?mmss" "tj \<in> set ?mmts" 
              have "(si \<sqsupset> tj \<longrightarrow> (si \<cdot> \<delta>) \<sqsupset> (tj \<cdot> \<delta>)) \<and> (si \<sqsupseteq> tj \<longrightarrow> (si \<cdot> \<delta>) \<sqsupseteq> (tj \<cdot> \<delta>))" 
              proof (intro IH add_strict_mono)
                from *(1) have "si \<in> set ss" using set_status_nth[of _ _ _ \<pi>] by auto
                then show "size si < size s" unfolding s by (auto simp: termination_simp)
                from *(2) have "tj \<in> set ts" using set_status_nth[of _ _ _ \<pi>] by auto
                then show "size tj < size t" unfolding t by (auto simp: termination_simp)
              qed
              hence "si \<sqsupset> tj \<Longrightarrow> (si \<cdot> \<delta>) \<sqsupset> (tj \<cdot> \<delta>)"
                "si \<sqsupseteq> tj \<Longrightarrow> (si \<cdot> \<delta>) \<sqsupseteq> (tj \<cdot> \<delta>)" by blast+
            } note IH = this
            have mmconv: "?Mmss = map (\<lambda>t. t \<cdot> \<delta>) ?mmss" "?Mmts = map (\<lambda>t. t \<cdot> \<delta>) ?mmts"  
              using set_status_nth[OF refl, of _ \<pi> f ss] set_status_nth[OF refl, of _ \<pi> g ts] by auto
            {
              assume "snd (mul_ext co.wpo ?mmss ?mmts)"
              hence "snd (mul_ext co.wpo ?Mmss ?Mmts)" unfolding mmconv
                by (intro nstri_mul_ext_map, insert IH, auto)
            } note snd_mul = this
            {
              assume "snd (lex_ext co.wpo n ?mmss ?mmts)"
              hence "snd (lex_ext co.wpo n ?Mmss ?Mmts)" unfolding mmconv
                by (intro nstri_lex_ext_map, insert IH, auto)
            } note snd_lex = this
            {
              assume "fst (mul_ext co.wpo ?mmss ?mmts)"
              hence "fst (mul_ext co.wpo ?Mmss ?Mmts)" unfolding mmconv
                by (intro stri_mul_ext_map, insert IH, auto)
            } note fst_mul = this
            {
              assume "fst (lex_ext co.wpo n ?mmss ?mmts)"
              hence "fst (lex_ext co.wpo n ?Mmss ?Mmts)" unfolding mmconv
                by (intro stri_lex_ext_map, insert IH, auto)
            } note fst_lex = this
            consider (Lex) "c ?f = Lex" "c ?g = Lex" | (Mul) "c ?f = Mul" "c ?g = Mul" | (Diff) "c ?f \<noteq> c ?g" 
              by (cases "c ?f"; cases "c ?g", auto)
            thus ?thesis
            proof cases
              case Lex
              from Lex False ns have "snd (lex_ext co.wpo n ?mmss ?mmts)" by (auto split: if_splits)
              from snd_lex[OF this] have snd: "snd (lex_ext co.wpo n ?Mmss ?Mmts)" .
              with Lex ss_ts sstsA gtprnc have nsm: "?s \<sqsupseteq> ?t" unfolding simps unfolding s t 
                by (auto split: if_splits)
              show ?thesis
              proof (intro conjI impI nsm)
                assume "t \<sqsubset> s" 
                from this[unfolded simps, unfolded t s term.simps id]
                  Lex False ns have "fst (lex_ext co.wpo n ?mmss ?mmts)" by (auto split: if_splits)
                from fst_lex[OF this] have fst: "fst (lex_ext co.wpo n ?Mmss ?Mmts)" .
                with ss_ts sstsA gtprnc Lex show "?s \<sqsupset> ?t" unfolding simps unfolding s t 
                  by (auto split: if_splits)
              qed
            next
              case Mul
              from Mul False ns have "snd (mul_ext co.wpo ?mmss ?mmts)" by (auto split: if_splits)
              from snd_mul[OF this] have snd: "snd (mul_ext co.wpo ?Mmss ?Mmts)" .
              with Mul ss_ts sstsA gtprnc have nsm: "?s \<sqsupseteq> ?t" unfolding simps unfolding s t 
                by (auto split: if_splits)
              show ?thesis
              proof (intro conjI impI nsm)
                assume "t \<sqsubset> s" 
                from this[unfolded simps, unfolded t s term.simps id]
                  Mul False ns have "fst (mul_ext co.wpo ?mmss ?mmts)" by (auto split: if_splits)
                from fst_mul[OF this] have fst: "fst (mul_ext co.wpo ?Mmss ?Mmts)" .
                with ss_ts sstsA gtprnc Mul show "?s \<sqsupset> ?t" unfolding simps unfolding s t 
                  by (auto split: if_splits)
              qed
            next
              case Diff
              from Diff False ns have "?mmts = []" by (cases "c ?f"; cases "c ?g", auto split: if_splits)
              hence "?Mmts = []" by simp
              with Diff ss_ts sstsA gtprnc have nsm: "?s \<sqsupseteq> ?t" unfolding simps unfolding s t 
                by (cases "c ?f"; cases "c ?g", auto split: if_splits)
              show ?thesis
              proof (intro conjI impI nsm)
                assume "t \<sqsubset> s" 
                from this[unfolded simps, unfolded t s term.simps id] Diff False ns 
                have "?mmss \<noteq> [] \<and> ?mmts = []" by (cases "c ?f"; cases "c ?g", auto split: if_splits)
                hence "?Mmss \<noteq> []" "?Mmts = []" by auto
                with ss_ts sstsA gtprnc Diff show "?s \<sqsupset> ?t" unfolding simps unfolding s t 
                  by (cases "c ?f"; cases "c ?g", auto split: if_splits)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed
  
(* Lemma 6 *)
lemma co_comp_wpo_cowpo:
  assumes ss:"strictly_simple_status \<pi> NS"
    and prc_compat: "prc_compat' gt_prc ge_prc"
    and cLex: "c = (\<lambda> _. Lex)" 
  shows "co_compatible (WPO_NS, WPO_S) (COWPO_NS, COWPO_S)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain s t where ost: "(s \<succeq> t \<and> s \<sqsubset> t) \<or> (s \<succ> t \<and> s \<sqsubseteq> t)"  by auto
  then show False
  proof (induct "(s, t)" arbitrary:s t rule: wf_induct[OF wf_measure[of "\<lambda> (s,t). size s + size t"]])
    case 1
    from 1
    have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> (s' \<succeq> t' \<longrightarrow> \<not> s' \<sqsubset> t')" by auto
    note IH1 = this[rule_format]
    have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> (s' \<succ> t' \<longrightarrow> \<not> s' \<sqsubseteq> t')" using "1.hyps" by auto
    note IH2 = this[rule_format]
    have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> (s' \<sqsubset> t' \<longrightarrow> \<not> s' \<succeq> t')" using IH1 by blast
    note IH3 = this[rule_format]
    have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> (s' \<sqsubseteq> t' \<longrightarrow> \<not> s' \<succ> t')" using "1.hyps" by auto
    note IH4 = this[rule_format]
    {
      fix f ss g ts si tj
      assume s: "s = Fun f ss" and t: "t = Fun g ts" 
      let ?f = "(f,length ss)"
      let ?ss = "map (\<lambda> i. ss ! i) (status \<pi> ?f)"
      let ?g = "(g,length ts)"
      let ?ts = "map (\<lambda> i. ts ! i) (status \<pi> ?g)"
      assume "si \<in> set ?ss" "tj \<in> set ?ts"
      hence *: "si \<in> set ss" "tj \<in> set ts" using set_status_nth[OF refl, of _ \<pi> g ts] set_status_nth[OF refl, of _ \<pi> f ss]
        by auto
      from *(1) have "size si < size s" unfolding s by (auto simp: size_simps)
      moreover from *(2) have "size tj < size t" unfolding t by (auto simp: size_simps)
      ultimately have "size si + size tj < size s + size t" by simp
      note IH1[OF this] IH2[OF this] IH3[OF this] IH4[OF this]
    } note IH = this
    have "s \<succeq> t \<longrightarrow> \<not> s \<sqsubset> t"
    proof (rule impI)
      assume assm:"s \<succeq> t"
      show "\<not> s \<sqsubset> t"
      proof (rule notI)
        assume asm:"s \<sqsubset> t"
        hence stg:"(s, t) \<in> nltA^-1" using cowpo_s_imp_gta[of t s] by simp
        from neg_nltA[OF stg[simplified]] have stg: "(s, t) \<notin> S" by auto
        with asm show False
        proof (cases "(s,t) \<in> S  \<or> ((s,t) \<notin> NS \<or> \<not> s \<succeq> t)")
          case True
          then show ?thesis
          proof
            assume sts: "(s, t) \<in> S"
            hence "(s, t) \<in> NS" using S_imp_NS by blast
            with stg show ?thesis using sts by auto
          next
            assume "((s,t) \<notin> NS \<or> \<not> s \<succeq> t)"
            with essential.wpo_ns_imp_NS[of s t] have 1: "\<not> s \<succeq> t" by blast
            with assms show ?thesis using assm by force 
          qed
        next
          case False
          hence not: "((s,t) \<in> S) = False" and stA: "(s,t) \<in> NS" and ns: "s \<succeq> t" by auto
          show ?thesis
          proof (cases s)
            case (Var x) note s = this
            show ?thesis
            proof (cases t)
              case (Var y) note t = this
              show ?thesis unfolding s t using t asm co.wpo.simps neg_nleA
                by (smt (z3) Compl_iff Term.term.simps(5) converseI prod.exhaust_sel prod.inject stA)
            next
              case (Fun g ts) note t = this
              show ?thesis unfolding s t using s t ns using False essential.wpo.simps by auto
            qed
          next
            case (Fun f ss) note s = this
            let ?f = "(f,length ss)"
            let ?ss = "set (status \<pi> ?f)"
            show ?thesis
            proof (cases t)
              case (Var y) note t = this
              then show ?thesis unfolding s t using s t ns using asm co.wpo.simps
                by (smt (z3) ComplD neg_nleA Term.term.simps(5) converseI prod.exhaust_sel prod.inject stA)
            next
              case (Fun g ts) note t = this
              let ?g = "(g,length ts)"
              let ?ts = "set (status \<pi> ?g)"
              show ?thesis
              proof (cases "\<exists> i \<in> ?ss. (ss ! i) \<succeq> t")
                case True 
                obtain i where ssit:"ss ! i \<succeq> t" and i:"i \<in> ?ss" using True by blast
                let ?s = "Fun f ss"
                from s have s: "s = ?s" by simp
                let ?t = "Fun g ts"
                from t have t: "t = ?t" by simp
                from s have "\<forall> s' \<in> set ss. size s' < size s" by (auto simp: size_simps)
                with \<pi>E[OF i] have "size (ss ! i) <  size s" unfolding s using s by simp
                with ssit have nssit:"\<not> ss ! i \<sqsubset> t" unfolding s t using True IH1[of "ss ! i" t] s t size_simps by simp
                hence ssit:"ss ! i \<sqsubset> t = False" by simp
                from asm have stnltA: "(s, t) \<in> nltA^-1" using not stA 
                  using cowpo_s_imp_gta by force
                from asm have stnnleA: "(s, t) \<notin> nleA^-1" using stA neg_nleA by blast  
                have "\<exists> j \<in> ?ts. s \<sqsubseteq> (ts ! j)" 
                proof(cases "nle_prc ?g ?f")
                  case True
                  from ssit asm stnltA stnnleA True show ?thesis unfolding s t using s t co.wpo.simps[of "Fun g ts" "Fun f ss"] 
                    by (smt (verit) Term.term.simps(6) asm case_prod_conv converseI i nssit snd_conv stnnleA wpo.wpo_s_imp_ns)
                next
                  case False
                  from ssit asm stnltA stnnleA False show ?thesis unfolding s t using s t co.wpo.simps[of "Fun g ts" "Fun f ss"]
                    by (smt (verit) Term.term.simps(6) asm case_prod_beta converseI fst_conv i nssit stnnleA)
                qed 
                then obtain j where j:"j \<in> ?ts" and stsj:"s \<sqsubseteq> (ts ! j)" by blast
                from t have sts:"\<forall> t' \<in> set ts. size t' < size t" by (auto simp: size_simps)
                with \<pi>E[OF j] have "size (ts ! j) <  size t" unfolding t using t by simp
                with stsj have nstsj:"\<not> s \<succ> (ts ! j)" using True IH4[of s "ts ! j"] size_simps by simp
                have 1:"s \<succ> (ss ! i)" unfolding strictly_simple_status_def s ss using 
                    essential.wpo.simps[of s "ss ! i"] i s ss strictly_simple_status_def essential.wpo_ns_refl' by fastforce
                have 2:"ss ! i \<succeq> t" by fact
                have 3:"t \<succ> (ts ! j)" unfolding strictly_simple_status_def s ss using 
                    essential.wpo.simps[of t "ts ! j"] j t ss strictly_simple_status_def essential.wpo_ns_refl' by fastforce
                from 1 2 3 have "s \<succ> ts ! j" using essential.wpo_compat wpo.wpo_s_imp_ns using prc_compat by blast
                with nstsj show ?thesis by simp
              next 
                case False note False1 = this
                let ?s = "Fun f ss"
                from s have s: "s = ?s" by simp
                let ?t = "Fun g ts"
                from t have t: "t = ?t" by simp
                hence ssfalse: "(\<exists> i \<in> ?ss. (ss ! i) \<succeq> (Fun g ts)) = False" unfolding t using False1 t by fastforce
                with not ns stA  have stsi: "\<And>i. i \<in> ?ts \<Longrightarrow> (Fun f ss) \<succ> (ts ! i)" using False essential.wpo.simps[of "Fun f ss" "Fun g ts"] 
                  by (smt (verit) Pair_inject Term.term.simps(6) prod.exhaust_sel s split_beta t) 
                from t have sts:"\<forall> t' \<in> set ts. size t' < size t" by (auto simp: size_simps)
                with \<pi>E have "\<forall>i \<in> ?ts. size (ts ! i) <  size t" unfolding t using t by blast
                with stsi have nstsi:"\<forall>i \<in> ?ts. \<not> (Fun f ss) \<sqsubseteq> (ts ! i)" unfolding s t using False size_simps IH2 
                  by (simp add: \<open>\<forall>i\<in>set (status \<pi> (g, length ts)). size (ts ! i) < size t\<close> s)
                from asm have stnltA: "(Fun g ts, Fun f ss) \<in> nltA" using not stA 
                  using cowpo_s_imp_gta s t by blast
                from asm have stnnleA: "(Fun g ts, Fun f ss) \<notin> nleA" using stA neg_nleA using s t by fastforce  
                hence ssit: "\<And>i. i \<in> ?ss \<Longrightarrow> (ss ! i) \<sqsubset> (Fun g ts)" using asm nstsi stnltA co.wpo.simps[of "Fun g ts" "Fun f ss"] 
                  by (smt (verit) False1 Term.term.simps(6) prod.exhaust_sel s split_beta t essential.wpo_s_imp_ns)
                let ?ss = "map (\<lambda> i. ss ! i) (status \<pi> (f,length ss))"
                let ?ts = "map (\<lambda> i. ts ! i) (status \<pi> (g,length ts))"
                from ssit asm show ?thesis
                proof(cases "ge_prc ?f ?g")
                  case True note True1 = this
                  then show ?thesis
                  proof(cases "gt_prc ?f ?g")
                    case True
                    hence ngtprnc: "\<not> nlt_prc ?g ?f" 
                      by (simp add: gt_prc_comp)
                    from True have "ge_prc ?f ?g" using incl_gt_ge_prc by simp
                    with True have ngeprnc:"\<not> nle_prc ?g ?f" using ge_prc_comp by simp 
                    have "nle_prc ?g ?f" using asm stnltA stnnleA nstsi ssit co.wpo.simps[of t s]
                      by (simp add: ngtprnc s t) 
                    then show ?thesis using ngeprnc by blast 
                  next
                    case False
                    from True1 have ngeprnc:"\<not> nle_prc ?g ?f" using False by (simp add: ge_prc_comp)
                    consider (Lex) "c ?f = Lex" "c ?g = Lex" | (Mul) "c ?f = Mul" "c ?g = Mul" | (Diff) "c ?f \<noteq> c ?g" 
                      by (cases "c ?f"; cases "c ?g", auto)
                    thus ?thesis
                    proof cases
                      case Lex
                      have lexext:"snd(lex_ext essential.wpo n ?ss ?ts)" using assm ssfalse stsi True1 essential.wpo.simps[of "Fun f ss" "Fun g ts"]
                        using not s stA t Lex False by force
                      have colexext:"\<not> fst(lex_ext co.wpo n ?ts ?ss)"
                      proof 
                        assume asmlex:"fst(lex_ext co.wpo n ?ts ?ss)"
                        show False
                          by (rule lex_ext_co_compat[OF _ _ cowpo_s_imp_ns asmlex lexext], insert IH[OF s t], auto) 
                      qed
                      have "nle_prc ?g ?f" using lexext asm stnltA stnnleA nstsi ssit co.wpo.simps[of t s] colexext False 
                        using Lex s t by (auto split: if_splits)
                      with ngeprnc show ?thesis by auto 
                    next
                      case Diff
                      have ts:"?ts = []" using assm ssfalse stsi True1 essential.wpo.simps[of s t]
                        using not s stA t Diff False by (cases "c ?f"; cases "c ?g"; force)
                      have "nle_prc ?g ?f" using ts asm stnltA stnnleA nstsi ssit co.wpo.simps[of t s] False 
                        using Diff s t by (cases "c ?f"; cases "c ?g", auto split: if_splits)
                      with ngeprnc show ?thesis by auto 
                    next
                      case Mul
                      have mulext:"snd(mul_ext essential.wpo ?ss ?ts)" using assm ssfalse stsi True1 essential.wpo.simps[of s t]
                        using not s stA t Mul False by force                      
                      have comulext:"\<not> fst(mul_ext co.wpo ?ts ?ss)" 
                        using Mul cLex (* here the real proof is missing to get rid of the cLex assumption *) 
                        by simp
                      have "nle_prc ?g ?f" using mulext asm stnltA stnnleA nstsi ssit co.wpo.simps[of t s] comulext False 
                        using Mul s t by (auto split: if_splits)
                      with ngeprnc show ?thesis by auto 
                    qed
                  qed
                next
                  case False
                  with assm False1 stsi False show ?thesis using essential.wpo.simps[of s t] s t not
                    by (auto split: if_splits)
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    moreover have "s \<succ> t \<longrightarrow> \<not> s \<sqsubseteq> t"
    proof (rule impI)
      assume assm:"s \<succ> t"
      show "\<not> s \<sqsubseteq> t"
      proof (rule notI)
        assume asm: "s \<sqsubseteq> t"
        hence stg:"(s, t) \<in> nltA^-1" using cowpo_ns_imp_nltA[of t s] by simp
        with asm show False
        proof (cases "(s,t) \<in> S  \<or> ((s,t) \<notin> NS \<or> \<not> s \<succ> t)")
          case True
          then show ?thesis
          proof
            assume sts: "(s, t) \<in> S"
            hence "(s, t) \<in> NS" using S_imp_NS by blast
            with stg show ?thesis using neg_nleA neg_nltA sts by blast
          next
            assume "((s,t) \<notin> NS \<or> \<not> s \<succ> t)"
            with essential.wpo_ns_imp_NS[of s t] have 1: "\<not> s \<succ> t"
              using wpo.wpo_s_imp_ns by blast
            with assms show ?thesis using assm by force 
          qed
        next
          case False
          hence not: "((s,t) \<in> S) = False" and stA: "(s,t) \<in> NS" and st: "s \<succ> t" by auto
          show ?thesis
          proof (cases s)
            case (Var x) note s = this
            show ?thesis
            proof (cases t)
              case (Var y) note t = this
              show ?thesis unfolding s t using t asm co.wpo.simps[of t s] 
                essential.wpo.simps not s st stA by fastforce
            next
              case (Fun g ts) note t = this
              show ?thesis unfolding s t using s t asm co.wpo.simps[of t s]
                by (smt (z3) False Term.term.simps(5) eq_fst_iff essential.wpo.simps)  
            qed
          next
            case (Fun f ss) note s = this
            let ?f = "(f,length ss)"
            let ?ss = "set (status \<pi> ?f)"
            show ?thesis
            proof (cases t)
              case (Var y) note t = this
              then show ?thesis unfolding s t using s t st asm co.wpo.simps[of t s] 
                by (smt (verit, del_insts) Pair_inject Term.term.simps(5) Term.term.simps(6) calculation prod.exhaust_sel wpo.wpo_s_imp_ns)
            next
              case (Fun g ts) note t = this
              let ?g = "(g,length ts)"
              let ?ts = "set (status \<pi> ?g)"
              show ?thesis
              proof (cases "\<exists> i \<in> ?ss. (ss ! i) \<succeq> t")
                case True 
                obtain i where ssit:"ss ! i \<succeq> t" and i:"i \<in> ?ss" using True by blast
                let ?s = "Fun f ss"
                from s have s: "s = ?s" by simp
                let ?t = "Fun g ts"
                from t have t: "t = ?t" by simp
                from s have "\<forall> s' \<in> set ss. size s' < size s" by (auto simp: size_simps)
                with \<pi>E[OF i] have "size (ss ! i) <  size s" unfolding s using s by simp
                with ssit have nssit:"\<not> ss ! i \<sqsubset> t" unfolding s t using True IH1[of "ss ! i" t] s t size_simps by simp
                hence ssit:"ss ! i \<sqsubset> t = False" by simp
                have stnltA: "(s, t) \<in> nltA^-1" by fact
                from asm have stnnleA: "(s, t) \<notin> nleA^-1" using stA
                  using neg_nleA by fastforce  
                have "\<exists> j \<in> ?ts. s \<sqsubseteq> (ts ! j)"
                proof(cases "nle_prc ?g ?f")
                  case True
                  from ssit asm stnltA stnnleA True show ?thesis unfolding s t using s t co.wpo.simps[of "Fun g ts" "Fun f ss"] 
                    by (smt (verit) Term.term.simps(6) asm case_prod_conv converseI i nssit snd_conv stnnleA wpo.wpo_s_imp_ns)
                next
                  case False
                  from ssit asm stnltA stnnleA False show ?thesis unfolding s t using s t co.wpo.simps[of "Fun g ts" "Fun f ss"]
                    by (smt (verit) Term.term.simps(6) asm case_prod_beta converseI i nssit snd_conv stnnleA)
                qed 
                then obtain j where j:"j \<in> ?ts" and stsj:"s \<sqsubseteq> (ts ! j)" by blast
                from t have sts:"\<forall> t' \<in> set ts. size t' < size t" by (auto simp: size_simps)
                with \<pi>E[OF j] have "size (ts ! j) <  size t" unfolding t using t by simp
                with stsj have nstsj:"\<not> s \<succ> (ts ! j)" using True IH4[of s "ts ! j"] size_simps by simp
                have 1:"s \<succ> (ss ! i)" unfolding strictly_simple_status_def s ss using 
                    essential.wpo.simps[of s "ss ! i"] i s ss strictly_simple_status_def essential.wpo_ns_refl' by fastforce
                have 2:"ss ! i \<succeq> t" by fact
                have 3:"t \<succ> (ts ! j)" unfolding strictly_simple_status_def s ss using 
                    essential.wpo.simps[of t "ts ! j"] j t ss strictly_simple_status_def essential.wpo_ns_refl' by fastforce
                from 1 2 3 have "s \<succ> ts ! j" using essential.wpo_compat wpo.wpo_s_imp_ns using prc_compat by blast
                with nstsj show ?thesis by simp
              next 
                case False note False1 = this
                let ?s = "Fun f ss"
                from s have s: "s = ?s" by simp
                let ?t = "Fun g ts"
                from t have t: "t = ?t" by simp
                hence ssfalse: "(\<exists> i \<in> ?ss. (ss ! i) \<succeq> (Fun g ts)) = False" unfolding t using False1 t by fastforce
                with not st stA  have stsi: "\<And>i. i \<in> ?ts \<Longrightarrow> (Fun f ss) \<succ> (ts ! i)" using False essential.wpo.simps[of "Fun f ss" "Fun g ts"] 
                  by (smt (verit) Pair_inject Term.term.simps(6) prod.exhaust_sel s split_beta t) 
                from t have sts:"\<forall> t' \<in> set ts. size t' < size t" by (auto simp: size_simps)
                with \<pi>E have "\<forall>i \<in> ?ts. size (ts ! i) <  size t" unfolding t using t by blast
                with stsi have nstsi:"\<forall>i \<in> ?ts. \<not> (Fun f ss) \<sqsubseteq> (ts ! i)" unfolding s t using False size_simps IH2 
                  by (simp add: \<open>\<forall>i\<in>set (status \<pi> (g, length ts)). size (ts ! i) < size t\<close> s)
                from asm have stnltA: "(Fun g ts, Fun f ss) \<in> nltA" using not stA 
                  using neg_nltA co_comp_itself using s t stg by blast
                from asm have stnnleA: "(Fun g ts, Fun f ss) \<notin> nleA" using stA neg_nleA using s t by fastforce  
                hence ssit: "\<And>i. i \<in> ?ss \<Longrightarrow> (ss ! i) \<sqsubset> (Fun g ts)" using asm nstsi stnltA co.wpo.simps[of "Fun g ts" "Fun f ss"] 
                  by (smt (verit) False1 Term.term.simps(6) prod.exhaust_sel s split_beta t essential.wpo_s_imp_ns)
                let ?ss = "map (\<lambda> i. ss ! i) (status \<pi> (f,length ss))"
                let ?ts = "map (\<lambda> i. ts ! i) (status \<pi> (g,length ts))"
                from ssit asm show ?thesis
                proof(cases "ge_prc ?f ?g")
                  case True note True1 = this
                  then show ?thesis
                  proof(cases "gt_prc ?f ?g")
                    case True
                    hence ngtprnc: "\<not> nlt_prc ?g ?f" 
                      by (simp add: gt_prc_comp)
                    from True have "ge_prc ?f ?g" using incl_gt_ge_prc by simp
                    with True have ngeprnc:"\<not> nle_prc ?g ?f" using ge_prc_comp by simp 
                    have "nle_prc ?g ?f" using asm stnltA stnnleA nstsi ssit co.wpo.simps[of "Fun g ts" "Fun f ss"]
                      by (simp add: ngtprnc s t) 
                    then show ?thesis using ngeprnc by blast 
                  next
                    case False
                    from True1 have ngeprnc:"\<not> nle_prc ?g ?f" using False by (simp add: ge_prc_comp)
                    consider (Lex) "c ?f = Lex" "c ?g = Lex" | (Mul) "c ?f = Mul" "c ?g = Mul" | (Diff) "c ?f \<noteq> c ?g" 
                      by (cases "c ?f"; cases "c ?g", auto)
                    thus ?thesis
                    proof cases
                      case Lex 
                      have lexext:"fst(lex_ext essential.wpo n ?ss ?ts)" using assm ssfalse  stsi True1 essential.wpo.simps[of "Fun f ss" "Fun g ts"]
                        using False not s stA t Lex by (simp add: lex_ext_stri_imp_nstri)
                      have colexext:"\<not> snd(lex_ext co.wpo n ?ts ?ss)" 
                      proof  
                        assume asmlex:"snd(lex_ext co.wpo n ?ts ?ss)"
                        show False
                          by (rule lex_ext_co_compat[OF _ _ essential.wpo_s_imp_ns lexext asmlex], insert IH[OF s t], auto)
                      qed
                      have "nle_prc ?g ?f" using st lexext asm stnltA stnnleA nstsi ssit co.wpo.simps[of "Fun g ts" "Fun f ss"] colexext False 
                        Lex s t by (auto split: if_splits)
                      with ngeprnc show ?thesis by simp
                    next
                      case Diff
                      have ts:"?ss \<noteq> [] \<and> ?ts = []" using assm ssfalse stsi True1 essential.wpo.simps[of "Fun f ss" "Fun g ts"]
                        using not s stA t Diff False by (cases "c ?f"; cases "c ?g"; force)
                      have "nle_prc ?g ?f" using ts st asm stnltA stnnleA nstsi ssit co.wpo.simps[of "Fun g ts" "Fun f ss"] False 
                        using Diff s t by (cases "c ?f"; cases "c ?g", auto split: if_splits)
                      with ngeprnc show ?thesis by auto 
                    next
                      case Mul
                      have mulext:"fst(mul_ext essential.wpo ?ss ?ts)" using assm ssfalse stsi True1 essential.wpo.simps[of "Fun f ss" "Fun g ts"]
                        using not s stA t Mul False by force
                      from Mul cLex (* here the real proof is missing to get rid of the cLex assumption *) 
                      have comulext: "\<not> snd(mul_ext co.wpo ?ts ?ss)" by simp
                      have "nle_prc ?g ?f" using st mulext asm stnltA stnnleA nstsi ssit co.wpo.simps[of "Fun g ts" "Fun f ss"] comulext False 
                          Mul s t by (auto split: if_splits)
                      with ngeprnc show ?thesis by auto 
                    qed
                  qed
                next
                  case False
                  with assm False1 stsi False show ?thesis using essential.wpo.simps[of s t] 
                    by (smt (verit) Pair_inject Term.term.simps(6) not prod.exhaust_sel s split_beta t)
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    ultimately show ?thesis 
      using "1.prems" by blast
  qed
qed

theorem co_rewrite_pair_wpo_cowpo:
  assumes ss:"strictly_simple_status \<pi> NS"
    and ctxt_NS: "ctxt.closed NS"
    and prc_compat: "prc_compat' gt_prc ge_prc"
    and cLex: "c = (\<lambda> _. Lex)" 
  shows "co_rewrite_pair COWPO_S WPO_NS"
proof
  show "ctxt.closed WPO_NS" using assms WPO_NS_ctxt[OF ss ctxt_closed_one[OF ctxt_NS]] by (meson one_imp_ctxt_closed)  
  show "subst.closed WPO_NS" using assms essential.wpo_stable' using refl_NS ge_prc_refl by blast
  show "subst.closed COWPO_S" using assms cowpo_stable ssimple_status gt_prc_irrefl by auto
  show "refl WPO_NS" using assms essential.wpo_ns_refl' by (simp add: refl_on_def)
  show "trans WPO_NS" unfolding trans_def using assms essential.wpo_compat by blast 
  show "WPO_NS \<inter> COWPO_S^-1 = {}" using assms co_comp_wpo_cowpo by fastforce
qed 

end


(* we show that the CO-WPO with multiset status is unsound, since in constrast to
  the lexicographic extension, the multiset extension does not preserve co-compatibility. 
  we consider f(a,c) \<rightarrow> f(b,c) with trivial algebra and precedence a > b *)
lemma cowpo_with_multiset_status_is_unsound: 
  (* we only use this assumption to get rid of the assumption in
     Lemma co_comp_wpo_cowpo *)
  assumes [no_atp]: "(\<lambda> (_ :: (string \<times> nat)). Mul) = (\<lambda>_. Lex)" 
  shows False
proof - 
  let ?S = "{} :: (string,string)term rel" 
  let ?NS = "UNIV :: (string,string)term rel" 
  let ?prs = "(\<lambda> f g . f = (''a'',0) \<and> g = (''b'',0)) :: (string \<times> nat) \<Rightarrow> (string \<times> nat) \<Rightarrow> bool" 
  let ?prns = "(\<lambda> f g. ?prs f g \<or> f = g)" 
  let ?nprs = "\<lambda> f g. \<not> ?prs g f" 
  let ?nprns = "\<lambda> f g. \<not> ?prns g f" 
  interpret ex: cowpo_with_assms ?S ?NS 0 full_status "\<lambda> _. Mul" ?S ?NS
    ?nprns ?nprs ?prs ?prns 
    by (unfold_locales, auto simp: refl_on_def irrefl_on_def trans_def)
  define a where "a = (Fun ''a'' [] :: (string,string) term)" 
  define b where "b = (Fun ''b'' [] :: (string,string) term)" 
  define c where "c = (Fun ''c'' [] :: (string,string) term)" 
  define s where "s = Fun ''f'' [a, c]" 
  define t where "t = Fun ''f'' [b, c]" 
  have ctxt: "ctxt.closed ?NS" by auto 
  have stat: "strictly_simple_status full_status ?NS" 
    unfolding strictly_simple_status_def by auto
  have prc: "prc_compat' ?prs ?prns" 
    by (unfold_locales, auto)
  interpret co_rewrite_pair ex.COWPO_S ex.WPO_NS
    by (rule ex.co_rewrite_pair_wpo_cowpo[OF stat ctxt prc assms])
  from disj_NS_S have disj: "ex.WPO_NS \<inter> ex.COWPO_S\<inverse> = {}" by auto
  note defs = a_def b_def c_def s_def t_def
  {
    fix f :: "(string,string)term \<Rightarrow> (string,string)term \<Rightarrow> bool \<times> bool" 
    have a: "mul_ext f [] [] = (False, True)" 
      unfolding mul_ext_def Let_def ns_mul_ext_def s_mul_ext_def
      by (simp add: mult2_alt_def)
    have b: "mul_ext f [] (x # xs) = (False, False)" for x xs 
      unfolding mul_ext_def Let_def ns_mul_ext_def s_mul_ext_def
      by (simp add: mult2_alt_def)
    note a b
  } note [simp] = this
  have [simp]: "(\<forall>j\<in>{0..<Suc (Suc 0)}. P j) = (P 0 \<and> P (Suc 0))" for P 
    apply auto
    subgoal for j by (cases j, cases "j - 1", auto)
    done
  have [simp]: "(\<exists>j\<in>{0..<Suc (Suc 0)}. P j) = (P 0 \<or> P (Suc 0))" for P 
    apply auto
    subgoal for j by (cases j, cases "j - 1", auto)
    done

  
  have st: "(s,t) \<in> ex.WPO_NS" unfolding defs
    apply (simp add: wpo.wpo.simps)
    apply (simp add: a_def[symmetric] b_def[symmetric] c_def[symmetric])
  proof -
    define WPO where "WPO = ex.essential.wpo" 
    have ab: "fst (ex.essential.wpo a b)" unfolding defs by (simp add: wpo.wpo.simps)
    have cc: \<open>snd (ex.essential.wpo c c)\<close> unfolding defs by (simp add: wpo.wpo.simps)
    from ab cc show "snd (mul_ext ex.essential.wpo [a, c] [b, c])" 
      unfolding WPO_def[symmetric] mul_ext_def
      by (simp add: Let_def, intro ns_mul_extI[of _ "{#c#}" "{#a#}" _ "{#c#}" "{#b#}"], 
        auto intro: multpw_listI)
  qed
  with disj_NS_S have ts_not: "(t,s) \<notin> ex.COWPO_S" by auto
  define WPO where "WPO = ex.co.wpo" 
  have bc: "fst (ex.co.wpo b c)" unfolding defs
    by (simp add: wpo.wpo.simps)
  have ca: "fst (ex.co.wpo c a)" unfolding defs
    by (simp add: wpo.wpo.simps)
  from bc ca have "fst (mul_ext ex.co.wpo [b,c] [a,c])" 
    unfolding WPO_def[symmetric]
    unfolding mul_ext_def Let_def apply simp
    by (intro s_mul_extI[of _ "{#}" "{#b,c#}" _ "{#}" "{#a,c#}"], auto)
  hence contra: "(t,s) \<in> ex.COWPO_S" unfolding defs 
    by (simp add: wpo.wpo.simps)
  with ts_not show False ..
qed

end