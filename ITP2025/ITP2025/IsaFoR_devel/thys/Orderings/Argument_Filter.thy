(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Argument_Filter
  imports
    Term_Order_Impl
    First_Order_Rewriting.Trs_Impl
    Auxx.Map_Choice
begin

datatype af_entry = Collapse nat | AFList "nat list"
datatype 'f filtered = FPair (fpair_f: 'f)  nat

(* the main issue to not use pairs is that we can provide an alternative show function *)

derive compare_order filtered

fun filtered_fun :: "'f filtered \<Rightarrow> 'f"
where
  "filtered_fun (FPair f n) = f"

instantiation filtered :: (showl) showl
begin
definition "showsl (f :: 'a filtered) = showsl (filtered_fun f)"
definition "showsl_list (xs :: 'a filtered list) = default_showsl_list showsl xs"
instance ..
end

fun apply_af_entry :: "'f \<Rightarrow> af_entry \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term" where
  "apply_af_entry _ (Collapse i) ts = ts ! i"
| "apply_af_entry f (AFList is) ts = Fun f (map (\<lambda> i. ts ! i) is)" 

fun wf_af_entry :: "nat \<Rightarrow> af_entry \<Rightarrow> bool"
where "wf_af_entry n (Collapse i) = (i < n)"
  |   "wf_af_entry n (AFList is) = Ball (set is) (\<lambda> i. i < n)"

definition default_af_entry :: "nat \<Rightarrow> af_entry"
  where "default_af_entry n \<equiv> AFList [0..<n]"

lemma wf_default_af_entry[simp]: 
  "wf_af_entry n (default_af_entry n)"
  unfolding default_af_entry_def by auto

typedef 'f afs = "{(pi :: 'f \<times> nat \<Rightarrow> af_entry, fs :: ('f \<times> nat) set). 
  (\<forall> f n. wf_af_entry n (pi (f,n)) \<and> ((f,n) \<in> fs \<or> pi (f,n) = default_af_entry n))}"
  by (rule exI[of _ "(\<lambda> (f,n). default_af_entry n, {})"], auto)

setup_lifting type_definition_afs

lift_definition afs :: "'f afs \<Rightarrow> 'f \<times> nat \<Rightarrow> af_entry" is fst .
lift_definition afs_syms :: "'f afs \<Rightarrow> ('f \<times> nat) set" is snd .

lemma afs: "wf_af_entry n (afs pi (f,n))"
  by (transfer, auto)

lemma afs_syms: "(f,n) \<notin> afs_syms pi \<Longrightarrow> afs pi (f,n) = default_af_entry n"
  by (transfer, force)

fun afs_term :: "'f afs \<Rightarrow> ('f,'v)term \<Rightarrow> ('f filtered,'v)term" where 
  "afs_term \<pi> (Fun f ts) = (let l = length ts in apply_af_entry (FPair f l) (afs \<pi> (f,l)) (map (afs_term \<pi>) ts))"
| "afs_term \<pi> (Var x) = Var x"

fun af_term :: "'f afs \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term" where 
  "af_term \<pi> (Fun f ts) = (apply_af_entry f (afs \<pi> (f,length ts)) (map (af_term \<pi>) ts))"
| "af_term \<pi> (Var x) = Var x"

lemma af_term_def: "af_term \<pi> t = map_funs_term filtered_fun (afs_term \<pi> t)"
proof (induct t)
  case (Fun f ts)
  thus ?case using afs[of "length ts" \<pi> f] 
    by (cases "afs \<pi> (f,length ts)", auto simp: Let_def)
qed simp

definition afs_rule :: "'f afs \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f filtered,'v)rule"
where "afs_rule \<pi> lr \<equiv> (afs_term \<pi> (fst lr), afs_term \<pi> (snd lr))"

definition af_rule :: "'f afs \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f,'v)rule" where
  "af_rule \<pi> \<equiv> \<lambda> t. map_funs_rule filtered_fun (afs_rule \<pi> t)"

lemma af_rule_alt_def: "af_rule \<pi> lr = (af_term \<pi> (fst lr), af_term \<pi> (snd lr))" 
  unfolding af_rule_def afs_rule_def af_term_def by auto

definition afs_rules :: "'f afs \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f filtered,'v)rules"
where "afs_rules \<pi> R = map (afs_rule \<pi>) R"

definition af_rules :: "'f afs \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules"
where "af_rules \<pi> R = map (af_rule \<pi>) R"

definition
  afs_check ::
    "showsl \<Rightarrow> 'f::showl afs \<Rightarrow> (('f filtered,'v::showl)rule \<Rightarrow> showsl check) \<Rightarrow> ('f,'v)rule  \<Rightarrow> showsl check"
where
  "afs_check r \<pi> g lr \<equiv> let pl = afs_term \<pi> (fst lr); pr = afs_term \<pi> (snd lr) in g (pl,pr) <+? (\<lambda>s. 
  showsl (STR ''could not orient '') \<circ> showsl (fst lr) \<circ> showsl (STR '' '') \<circ> r \<circ> showsl (STR '' '') \<circ> showsl (snd lr) \<circ>
  showsl (STR ''\<newline>pi( '') \<circ> showsl (fst lr) \<circ> showsl (STR '' ) = '') \<circ> showsl pl \<circ> 
  showsl (STR ''\<newline>pi( '') \<circ> showsl (snd lr) \<circ> showsl (STR '' ) = '') \<circ> showsl pr \<circ> showsl_nl \<circ> s
)"

definition
  af_check ::
    "showsl \<Rightarrow> 'f::showl afs \<Rightarrow> (('f,'v::showl)rule \<Rightarrow> showsl check) \<Rightarrow> ('f,'v)rule  \<Rightarrow> showsl check"
where
  "af_check r \<pi> g lr \<equiv> let pl = af_term \<pi> (fst lr); pr = af_term \<pi> (snd lr) in g (pl,pr) <+? (\<lambda>s. 
  showsl (STR ''could not orient '') \<circ> showsl (fst lr) \<circ> showsl (STR '' '') \<circ> r \<circ> showsl (STR '' '') \<circ> showsl (snd lr) \<circ>
  showsl (STR ''\<newline>pi( '') \<circ> showsl (fst lr) \<circ> showsl (STR '' ) = '') \<circ> showsl pl \<circ> 
  showsl (STR ''\<newline>pi( '') \<circ> showsl (snd lr) \<circ> showsl (STR '' ) = '') \<circ> showsl pr \<circ> showsl_nl \<circ> s
)"

lemma af_rules[simp]: "set (af_rules \<pi> R) = af_rule \<pi> ` (set R)" unfolding af_rules_def by auto
 
context
  fixes \<pi> :: "'f afs"
begin

abbreviation afs_subst :: "('f,'v)subst \<Rightarrow> ('f filtered,'v)subst"
where "afs_subst \<sigma> \<equiv> (\<lambda>x. afs_term \<pi> (\<sigma> x))"

definition afs_rel :: "('f filtered,'v)term rel \<Rightarrow> ('f,'v)term rel"
where "afs_rel R = {lr | lr. afs_rule \<pi> lr \<in> R}"

definition af_rel :: "('f,'v)term rel \<Rightarrow> ('f,'v)term rel"
where "af_rel R = {lr | lr. af_rule \<pi> lr \<in> R}"

abbreviation af_subst :: "('f,'v)subst \<Rightarrow> ('f,'v)subst"
where "af_subst \<sigma> \<equiv> (\<lambda>x. af_term \<pi> (\<sigma> x))"

lemma afs_subst[simp]: "afs_term \<pi> (t \<cdot> \<sigma>) = afs_term \<pi> t \<cdot> afs_subst \<sigma>"
proof -
  have "afs_term \<pi> (t \<cdot> \<sigma>) = afs_term \<pi> t \<cdot> afs_subst (\<sigma>)"
  proof (induct t)
    case (Fun f ss)
    let ?l = "length ss"
    let ?e = "afs \<pi> (f,?l)"
    have wf_e: "wf_af_entry ?l ?e" by (rule afs)
    show ?case
    proof (cases ?e)
      case (Collapse i)
      with wf_e have "i < ?l" by simp
      with Collapse Fun(1)[of "ss ! i"] show ?thesis
        by (auto simp: Let_def)
    next
      case (AFList "is")
      with wf_e have wf: "\<forall> i \<in> set is. i < ?l" by auto
      with AFList Fun(1) show ?thesis 
        by auto
    qed
  qed simp
  then show ?thesis by simp
qed

lemma af_subst: "af_term \<pi> (t \<cdot> \<sigma>) = af_term \<pi> t \<cdot> af_subst \<sigma>"
proof -
  have "af_term \<pi> (t \<cdot> \<sigma>) = af_term \<pi> t \<cdot> af_subst \<sigma>"
  proof (induct t)
    case (Fun f ss)
    let ?l = "length ss"
    let ?e = "afs \<pi> (f,?l)"
    have wf_e: "wf_af_entry ?l ?e" by (rule afs)
    show ?case
    proof (cases ?e)
      case (Collapse i)
      with wf_e have "i < ?l" by simp
      with Collapse Fun(1)[of "ss ! i"] show ?thesis
        by (auto simp: Let_def af_term_def)
    next
      case (AFList "is")
      with wf_e have wf: "\<forall> i \<in> set is. i < ?l" by auto
      with AFList Fun(1) show ?thesis 
        by (auto simp: af_term_def)
    qed
  qed (simp add: af_term_def)
  then show ?thesis by simp
qed


lemma afs_rsteps:
  "(s,t) \<in> (rstep R)^* \<Longrightarrow> (afs_term \<pi> s, afs_term \<pi> t) \<in> (rstep (afs_rule \<pi> ` R))^*"
proof (induct rule: rtrancl_induct)
  case (step t u)
  let ?a = "afs_term \<pi>"
  let ?R = "afs_rule \<pi> ` R"
  let ?RR = "(rstep ?R)^*"
  from step(2) obtain C l r \<sigma>
    where t: "t = C \<langle> l \<cdot> \<sigma> \<rangle>" and u: "u = C \<langle> r \<cdot> \<sigma> \<rangle>" and lr: "(l,r) \<in> R" by blast
  define ll rr where "ll = l \<cdot> \<sigma>" and "rr = r \<cdot> \<sigma>"
  note ctxt = all_ctxt_closedD[OF all_ctxt_closed_rsteps[of _ ?R], of _ _ UNIV]
  have "(?a t, ?a u) \<in> ?RR" unfolding t u ll_def[symmetric] rr_def[symmetric]
  proof (induct C)
    case Hole
    from lr have "(?a l, ?a r) \<in> ?R" by (force simp: afs_rule_def)
    from rstep_subst[OF rstep_rule[OF this], of "afs_subst \<sigma>"]
    show ?case unfolding ll_def rr_def by simp
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"    
    let ?pi = "afs \<pi> (f, ?n)"
    show ?case
    proof (cases ?pi)
      case (Collapse i)
      then show ?thesis 
        by (cases "i = length bef", insert More, auto simp: nth_append)
    next
      case (AFList ls)
      show ?thesis 
        by (simp add: AFList, rule ctxt, auto, case_tac "ls ! i = length bef", insert More, auto simp: nth_append)
    qed
  qed
  with step(3) show ?case by simp
qed simp

lemma af_rsteps: assumes steps: "(s,t) \<in> (rstep R)^*"
  shows "(af_term \<pi> s, af_term \<pi> t) \<in> (rstep (af_rule \<pi> ` R))^*"
proof -
  let ?f = "filtered_fun"
  have id: "map_funs_trs ?f (afs_rule \<pi> ` R) = af_rule \<pi> ` R"
    by (force simp: af_rule_def afs_rule_def af_term_def map_funs_trs.simps)
  from rsteps_imp_map_rsteps[OF afs_rsteps[OF steps], of ?f, folded af_term_def]
  show ?thesis unfolding id .
qed

lemma argument_filter_nj: "\<not> (\<exists> u. (af_term \<pi> s,u) \<in> (rstep (af_rule \<pi> ` Rs))^* \<and> (af_term \<pi> t,u) \<in> (rstep (af_rule \<pi> ` Rt))^*) \<Longrightarrow>
  \<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
  using af_rsteps by auto

lemma afs_subst_closed: 
  assumes "subst.closed R"
  shows "subst.closed (afs_rel R)"
unfolding subst.closed_def
proof (rule subsetI, simp only: split_paired_all)
  fix ss ts
  assume "(ss,ts) \<in> subst.closure (afs_rel R)"
  then show "(ss,ts) \<in> afs_rel R"
  proof (induct)
    case (subst s t \<sigma>)
    from this have "(afs_term \<pi> s, afs_term \<pi> t) \<in> R" unfolding afs_rel_def afs_rule_def by simp
    with assms have "(afs_term \<pi> s \<cdot> afs_subst \<sigma>, afs_term \<pi> t \<cdot> afs_subst \<sigma>) \<in> R" unfolding subst.closed_def 
      using subst by auto    
    then show ?case unfolding afs_rel_def afs_rule_def by auto
  qed
qed

lemma af_subst_closed:
  assumes "subst.closed R"
  shows "subst.closed (af_rel R)"
unfolding subst.closed_def
proof (rule subsetI, simp only: split_paired_all)
  fix ss ts
  assume "(ss,ts) \<in> subst.closure (af_rel R)"
  then show "(ss,ts) \<in> af_rel R"
  proof (induct)
    case (subst s t \<sigma>)
    from this have "(af_term \<pi> s, af_term \<pi> t) \<in> R" unfolding af_rel_def af_term_def
      by (auto simp: af_rule_def afs_rule_def)
    with assms have "(af_term \<pi> s \<cdot> af_subst \<sigma>, af_term \<pi> t \<cdot> af_subst \<sigma>) \<in> R" unfolding subst.closed_def 
      using subst by auto    
    then show ?case unfolding af_rel_def af_rule_def af_subst[symmetric]
      by (auto simp: afs_rule_def af_subst af_term_def)
  qed
qed


lemma afs_SN: 
  assumes "SN R"
  shows "SN (afs_rel R)"
proof -
  have id: "afs_rel R = inv_image R (afs_term \<pi>)" 
    unfolding afs_rel_def afs_rule_def inv_image_def by auto
  show ?thesis unfolding id by (rule SN_inv_image[OF assms])
qed

lemma af_SN: 
  assumes "SN R"
  shows "SN (af_rel R)"
proof -
  have id: "af_rel R = inv_image R (af_term \<pi>)" 
    unfolding af_rel_def afs_rule_def af_rule_def af_term_def inv_image_def by auto
  show ?thesis unfolding id by (rule SN_inv_image[OF assms])
qed

lemma afs_compat: 
  assumes "NS O S \<subseteq> S"
  shows "afs_rel NS O afs_rel S \<subseteq> afs_rel S"
using assms
  by (unfold afs_rel_def afs_rule_def, clarify, auto)

lemma af_compat: 
  assumes "NS O S \<subseteq> S"
  shows "af_rel NS O af_rel S \<subseteq> af_rel S"
using assms
  by (unfold af_rel_def af_rule_alt_def, clarify, auto)

lemma afs_compat2: 
  assumes "S O NS \<subseteq> S"
  shows "afs_rel S O afs_rel NS \<subseteq> afs_rel S"
using assms
  by (unfold afs_rel_def afs_rule_def, clarify, auto)

lemma af_compat2: 
  assumes "S O NS \<subseteq> S"
  shows "af_rel S O af_rel NS \<subseteq> af_rel S"
using assms
  by (unfold af_rel_def af_rule_alt_def, clarify, auto)

lemma afs_refl: 
  assumes "refl NS"
  shows "refl (afs_rel NS)"
using assms unfolding refl_on_def
  by (unfold afs_rel_def afs_rule_def, auto)

lemma af_refl: 
  assumes "refl NS"
  shows "refl (af_rel NS)"
using assms unfolding refl_on_def
  by (unfold af_rel_def af_rule_alt_def, auto)

lemma afs_trans: 
  assumes "trans r"
  shows "trans (afs_rel r)"
unfolding trans_def
proof (unfold afs_rel_def afs_rule_def, clarify, unfold fst_conv snd_conv)
  fix a b c
  assume gt: "(afs_term \<pi> a, afs_term \<pi> b) \<in> r" "(afs_term \<pi> b, afs_term \<pi> c) \<in> r"
  show "\<exists> lr. (a,c) = lr \<and> (afs_term \<pi> (fst lr), afs_term \<pi> (snd lr)) \<in> r"
    by (intro exI conjI, rule refl, insert assms[unfolded trans_def, THEN spec, THEN spec, THEN spec, THEN mp[OF _ gt(1)], THEN mp[OF _ gt(2)]], simp)
qed

lemma af_trans: 
  assumes "trans r"
  shows "trans (af_rel r)"
unfolding trans_def
proof (unfold af_rel_def af_rule_alt_def, clarify, unfold fst_conv snd_conv)
  fix a b c
  assume gt: "(af_term \<pi> a, af_term \<pi> b) \<in> r" "(af_term \<pi> b, af_term \<pi> c) \<in> r"
  show "\<exists> lr. (a,c) = lr \<and> (af_term \<pi> (fst lr), af_term \<pi> (snd lr)) \<in> r"
    by (intro exI conjI, rule refl, insert assms[unfolded trans_def, THEN spec, THEN spec, THEN spec, THEN mp[OF _ gt(1)], THEN mp[OF _ gt(2)]], simp)
qed

lemma afs_NS_mono:
  assumes acc: "all_ctxt_closed UNIV R"
  shows "ctxt.closed (afs_rel R)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume st: "(s,t) \<in> afs_rel R"
  let ?ps = "afs_term \<pi> s"
  let ?pt = "afs_term \<pi> t"
  let ?bsa = "bef @ s # aft"
  let ?bta = "bef @ t # aft"
  from st have pst: "(?ps,?pt) \<in> R" unfolding afs_rel_def afs_rule_def by auto
  let ?l = "Suc (length bef + length aft)"
  let ?ls = "length (bef @ s # aft)"
  let ?lt = "length (bef @ t # aft)"
  let ?af = "afs \<pi> (f,?l)"
  have wf_af: "wf_af_entry ?l ?af" by (rule afs)
  let ?msa = "map (afs_term \<pi>) ?bsa"
  let ?mta = "map (afs_term \<pi>) ?bta"
  let ?pfs = "apply_af_entry (FPair f ?l) ?af ?msa"
  let ?pft = "apply_af_entry (FPair f ?l) ?af ?mta"
  have all2: "\<forall> i < ?l. (?msa ! i, ?mta ! i) \<in> R"
  proof (intro allI impI)
    fix i
    assume "i < ?l"
    then have i_s: "i < ?ls" and i_t: "i < ?lt" by simp_all
    {
      assume bef: "i < length bef"
      with all_ctxt_closed_reflE[OF acc] have "(?msa ! i, ?mta ! i) \<in> R"  
        by (simp only: nth_map[OF i_s], simp add: nth_append)
    }
    moreover
    {
      assume "i = length bef"
      with pst have "(?msa ! i, ?mta ! i) \<in> R" unfolding refl_on_def
       	by (simp only: nth_map[OF i_s], simp add: nth_append)
    }
    moreover
    {
      assume i: "i > length bef"
      from this obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
      with i_s have k2: "k < length aft" by auto
      from i all_ctxt_closed_reflE[OF acc] have "(?msa ! i, ?mta ! i) \<in> R"
        by (simp only: nth_map[OF i_s] nth_map[OF i_t], simp add: nth_append k1)
    }
    moreover
    {
      have "i < length bef \<or> i = length bef \<or> i > length bef" by auto
    }      
    ultimately
    show "(?msa ! i, ?mta ! i) \<in> R" by blast
  qed
  have "(?pfs,?pft) \<in> R"
  proof (cases ?af)
    case (Collapse i)
    with wf_af have "i < ?l"  by simp
    with all2 Collapse show ?thesis by auto
  next
    case (AFList ids)
    with wf_af have ids: "\<forall> i \<in> set ids. i < ?l" by simp
    show ?thesis 
    proof (simp only: AFList apply_af_entry.simps)
      let ?msi = "map ((!) (map (afs_term \<pi>) ?bsa)) ids"
      let ?mti = "map ((!) (map (afs_term \<pi>) ?bta)) ids"
      from ids all2 have args: "\<forall> i < length ids. (?msi ! i, ?mti ! i) \<in> R" by auto
      show "(Fun (FPair f ?l) ?msi, Fun (FPair f ?l) ?mti) \<in> R"
        by (rule all_ctxt_closedD[OF acc], insert args, auto)
    qed
  qed
  then show "(Fun f ?bsa, Fun f ?bta) \<in> afs_rel R" unfolding afs_rel_def afs_rule_def by simp
qed

lemma af_NS_mono:
  assumes acc: "all_ctxt_closed UNIV R"
  shows "ctxt.closed (af_rel R)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume st: "(s,t) \<in> af_rel R"
  let ?ps = "af_term \<pi> s"
  let ?pt = "af_term \<pi> t"
  let ?bsa = "bef @ s # aft"
  let ?bta = "bef @ t # aft"
  from st have pst: "(?ps,?pt) \<in> R" unfolding af_rel_def af_rule_alt_def by auto
  let ?l = "Suc (length bef + length aft)"
  let ?ls = "length (bef @ s # aft)"
  let ?lt = "length (bef @ t # aft)"
  let ?af = "afs \<pi> (f,?l)"
  have wf_af: "wf_af_entry ?l ?af" by (rule afs)
  let ?msa = "map (af_term \<pi>) ?bsa"
  let ?mta = "map (af_term \<pi>) ?bta"
  let ?pfs = "apply_af_entry f ?af ?msa"
  let ?pft = "apply_af_entry f ?af ?mta"
  have all2: "\<forall> i < ?l. (?msa ! i, ?mta ! i) \<in> R"
  proof (intro allI impI)
    fix i
    assume "i < ?l"
    then have i_s: "i < ?ls" and i_t: "i < ?lt" by simp_all
    {
      assume bef: "i < length bef"
      with all_ctxt_closed_reflE[OF acc] have "(?msa ! i, ?mta ! i) \<in> R"  
        by (simp only: nth_map[OF i_s], simp add: nth_append)
    }
    moreover
    {
      assume "i = length bef"
      with pst have "(?msa ! i, ?mta ! i) \<in> R" unfolding refl_on_def
       	by (simp only: nth_map[OF i_s], simp add: nth_append)
    }
    moreover
    {
      assume i: "i > length bef"
      from this obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
      with i_s have k2: "k < length aft" by auto
      from i all_ctxt_closed_reflE[OF acc] have "(?msa ! i, ?mta ! i) \<in> R"
        by (simp only: nth_map[OF i_s] nth_map[OF i_t], simp add: nth_append k1)
    }
    moreover
    {
      have "i < length bef \<or> i = length bef \<or> i > length bef" by auto
    }      
    ultimately
    show "(?msa ! i, ?mta ! i) \<in> R" by blast
  qed
  have "(?pfs,?pft) \<in> R"
  proof (cases ?af)
    case (Collapse i)
    with wf_af have "i < ?l"  by simp
    with all2 Collapse show ?thesis by auto
  next
    case (AFList ids)
    with wf_af have ids: "\<forall> i \<in> set ids. i < ?l" by simp
    show ?thesis 
    proof (simp only: AFList apply_af_entry.simps)
      let ?msi = "map ((!) (map (af_term \<pi>) ?bsa)) ids"
      let ?mti = "map ((!) (map (af_term \<pi>) ?bta)) ids"
      from ids all2 have args: "\<forall> i < length ids. (?msi ! i, ?mti ! i) \<in> R" by auto
      show "(Fun f ?msi, Fun f ?mti) \<in> R"
        by (rule all_ctxt_closedD[OF acc], insert args, auto)
    qed
  qed
  then show "(Fun f ?bsa, Fun f ?bta) \<in> af_rel R" 
    unfolding af_rel_def af_rule_alt_def by auto
qed
end

locale afs_redtriple = redtriple_order S NS NST
  for \<pi> :: "('f)afs" and S NS NST :: "('f filtered,'v)trs" 

locale af_redtriple = redtriple_order S NS NST
  for \<pi> :: "('f)afs" and S NS NST :: "('f,'v)trs" 

sublocale afs_redtriple \<subseteq> redtriple "afs_rel \<pi> S" "afs_rel \<pi> NS" "afs_rel \<pi> NST"
proof -
  let ?S = "afs_rel \<pi> S"
  let ?NS = "afs_rel \<pi> NS"
  let ?NST = "afs_rel \<pi> NST"
  show "redtriple ?S ?NS ?NST"
  proof
    show "SN ?S" by (rule afs_SN, rule SN)
    show "?NS O ?S \<subseteq> ?S" by (rule afs_compat, rule compat_NS_S)
    show "?S O ?NS \<subseteq> ?S" by (rule afs_compat2, rule compat_S_NS)
    show "subst.closed ?S" by (rule afs_subst_closed, rule subst_S)
    show "subst.closed ?NS" by (rule afs_subst_closed, rule subst_NS)
    show "subst.closed ?NST" by (rule afs_subst_closed, rule subst_NST)
    show "ctxt.closed ?NS" by (rule afs_NS_mono, rule all_ctxt_closed)
    show "?NST O ?S \<subseteq> ?S" by (rule afs_compat[OF compat_NST])
    show "?S \<subseteq> ?NS" unfolding afs_rel_def using S_imp_NS by blast
  qed
qed

sublocale af_redtriple \<subseteq> redtriple "af_rel \<pi> S" "af_rel \<pi> NS" "af_rel \<pi> NST"
proof -
  let ?S = "af_rel \<pi> S"
  let ?NS = "af_rel \<pi> NS"
  let ?NST = "af_rel \<pi> NST"
  show "redtriple ?S ?NS ?NST"
  proof
    show "SN ?S" by (rule af_SN, rule SN)
    show "?NS O ?S \<subseteq> ?S" by (rule af_compat, rule compat_NS_S)
    show "?S O ?NS \<subseteq> ?S" by (rule af_compat2, rule compat_S_NS)
    show "subst.closed ?S" by (rule af_subst_closed, rule subst_S)
    show "subst.closed ?NS" by (rule af_subst_closed, rule subst_NS)
    show "subst.closed ?NST" by (rule af_subst_closed, rule subst_NST)
    show "ctxt.closed ?NS" by (rule af_NS_mono, rule all_ctxt_closed)
    show "?NST O ?S \<subseteq> ?S" by (rule af_compat[OF compat_NST])
    show "?S \<subseteq> ?NS" unfolding af_rel_def using S_imp_NS by blast
  qed
qed


fun mono_af_entry :: "nat \<Rightarrow> af_entry \<Rightarrow> bool" where 
  "mono_af_entry n (Collapse i) = (n \<le> 1)"
| "mono_af_entry n (AFList ids) = Ball (set [0 ..< n]) (\<lambda> i. i \<in> set ids)"

definition mono_afs :: "'f afs \<Rightarrow> bool" where
  "mono_afs \<pi> = (\<forall> (f,n) \<in> afs_syms \<pi>. mono_af_entry n (afs \<pi> (f,n)))"

lemma mono_afs: assumes "mono_afs \<pi>"
  shows "mono_af_entry n (afs \<pi> (f,n))"
proof (cases "(f,n) \<in> afs_syms \<pi>")
  case True
  then show ?thesis using assms unfolding mono_afs_def by auto
next
  case False
  from afs_syms[OF this] show ?thesis unfolding default_af_entry_def by simp
qed

lemma mono_afs_ctxt_closed:
  assumes mono_pi: "mono_afs \<pi>"
    and trans_S: "trans S" 
    and monoS: "ctxt.closed (S :: ('f filtered, 'v)trs)"
  shows "ctxt.closed (afs_rel \<pi> S)"
proof -
  let ?S = "afs_rel \<pi> S"
  let ?pi = "afs_term \<pi>"
  {
    fix f bef s t aft
    assume st: "(?pi s, ?pi t) \<in> S"
    let ?bsa = "bef @ s # aft"
    let ?bta = "bef @ t # aft"
    let ?fs = "Fun f ?bsa"
    let ?ft = "Fun f ?bta"
    let ?l = "Suc (length bef + length aft)"
    let ?lba = "length bef + length aft"
    let ?e = "afs \<pi> (f,?l)"
    from mono_afs[OF mono_pi] have mono_e: "mono_af_entry ?l ?e" .
    have wf_e: "wf_af_entry ?l ?e" by (rule afs)
    have "(?pi ?fs, ?pi ?ft) \<in> S"
    proof (cases ?e)
      case (Collapse i)
      with mono_e wf_e show ?thesis using st by auto
    next
      case (AFList ids)
      let ?ids = "{n | n. n < ?l}"
      let ?f = "FPair f ?l"
      obtain l where l: "?l = l" by auto
      from AFList wf_e have ids1: "set ids \<subseteq> ?ids" by auto
      from AFList mono_e have ids2: "?ids \<subseteq> set ids" 	
        by (simp only: l, auto)
      from ids1 ids2 have ids: "set ids = ?ids" by auto
      let ?eq = "\<lambda> i. ?pi (?bsa ! i) = ?pi (?bta ! i)"
      let ?gr = "\<lambda> i. (?pi (?bsa ! i), ?pi (?bta ! i)) \<in> S"
      let ?lb = "length bef"
      have geq: "\<forall> i. ?eq i \<or> ?gr i"
      proof
        fix i
        {
          assume "i < ?lb" then have "?eq i" by (simp add: nth_append)
        }
        moreover
        {
          assume "i = ?lb"
          with st have "?gr i" by (simp add: nth_append)
        }
        moreover 
        {
          assume i2: "i > ?lb"
          then obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
          have "?eq i" unfolding nth_append using i2 k1 by auto
        }
        moreover
        {
          have "i < ?lb \<or> i = ?lb \<or> i > ?lb" by arith
        }
        ultimately show "?eq i \<or> ?gr i" by blast
      qed
      from ids have lb: "?lb \<in> set ids" by auto
      from st have "?gr ?lb" by (simp add: nth_append)
      with lb have gr: "\<exists> i \<in> set ids. ?gr i \<and> i = ?lb" by auto
      obtain ss ts pi g where g: "g = ?f" and ss: "ss = ?bsa" and ts: "ts = ?bta" and pi: "pi = (?pi :: ('f,'v)term \<Rightarrow> ('f filtered,'v)term)" by auto
      let ?eq = "\<lambda> i. pi (ss ! i) = pi (ts ! i)"
      let ?gr = "\<lambda> i. (pi (ss ! i), pi (ts ! i)) \<in> S"
      let ?ss = "map ((!) (map pi ss))"
      let ?ts = "map ((!) (map pi ts))"
      let ?both = "\<lambda> n. ?ts (take n ids) @ ?ss (drop n ids)"
      let ?gss = "Fun g (?ss ids)"
      let ?gboth = "\<lambda> n. Fun g (?both n)"
      from geq ss ts pi have geq: "\<forall> i. ?eq i \<or> ?gr i" by auto
      from gr ss ts pi have "\<exists> i \<in> set ids. ?gr i \<and> i = ?lb" by auto
      from this obtain i where i: "?gr i" and iids: "i \<in> set ids" and idef: "i = ?lb" by auto
      have "\<forall> n. (i \<in> set (take n ids) \<longrightarrow> (?gss, ?gboth n) \<in> S) \<and> (i \<notin> set (take n ids) \<longrightarrow> ?gss = ?gboth n)" (is "\<forall> n. ?p n") 
      proof (intro allI)
        fix n
        show "?p n"
        proof (induct n, simp)
          case (Suc n)
          show ?case
          proof (cases "n \<ge> length ids")
            case True
            with Suc show ?thesis by simp
          next
            case False 
            then have n: "n < length ids" by auto
            let ?bef = "?ts (take n ids)"
            let ?aft = "?ss (drop (Suc n) ids)"
            let ?ssn = "pi (ss ! (ids ! n))"
            let ?tsn = "pi (ts ! (ids ! n))"
            from n ids have ids_n: "ids ! n < ?l" by force
            have gn: "?both n = ?bef @ ?ssn # ?aft"
              by (simp only: Cons_nth_drop_Suc[OF n, symmetric], simp, simp add: nth_map[of "ids ! n" ?bsa pi, simplified, OF ids_n] ss)
            have gsn: "?both (Suc n) = ?bef @ ?tsn # ?aft"
              by (simp only: take_Suc_conv_app_nth[OF n], simp, simp add: nth_map[of "ids ! n" ?bta pi, simplified, OF ids_n] ts)
            {
              assume "?ssn \<noteq> ?tsn \<or> ids ! n = i"
              with geq i have "(?ssn, ?tsn) \<in> S" by blast		
              from ctxt_closed_one[OF monoS this] 
              have gnsn: "(?gboth n, ?gboth (Suc n)) \<in> S"
                by (simp only: gn gsn)
            } note noteq_i = this
            {
              assume "ids ! n \<noteq> i"
              {
                assume "ids ! n < ?lb"
                then have "?gboth (Suc n) = ?gboth n" 
                  by (simp add: gn gsn, simp add: ss ts) 
              }
              moreover
              {
                assume i2: "ids ! n > ?lb"
                have "?gboth (Suc n) = ?gboth n" unfolding term.simps gn gsn 
                  using i2 ss ts by (simp add: nth_append)
              }
              moreover
              {
                from \<open>ids ! n \<noteq> i\<close> have "ids ! n < ?lb \<or> ids ! n > ?lb" by (simp only: idef, arith)
              }
              ultimately have "?gboth (Suc n) = ?gboth n" by blast
            } note eq = this	      
            show ?thesis 
            proof (cases "i \<in> set (take (Suc n) ids)")
              case False 
              then have i_not: "i \<notin> set (take n ids)" and i_not2: "ids ! n \<noteq> i" using take_Suc_conv_app_nth[OF n] by auto
              from i_not Suc have rec: "?gss = ?gboth n" by blast 
              with False eq[OF i_not2] rec show ?thesis by simp 
            next
              case True note oTrue = this
              show ?thesis
              proof (cases "i \<in> set (take n ids)")
                case False
                with True have id: "ids ! n = i" using take_Suc_conv_app_nth[OF n] by auto
                from False Suc have rec: "?gss = ?gboth n" by blast
                from noteq_i id have "(?gboth n, ?gboth (Suc n)) \<in> S" by blast
                with True rec show ?thesis by simp
              next
                case True
                with Suc have rec: "(?gss, ?gboth n) \<in> S" by blast
                show ?thesis
                proof (cases "ids ! n = i")
                  case False
                  from rec eq[OF False] oTrue show ?thesis by simp
                next
                  case True
                  with noteq_i have "(?gboth n, ?gboth (Suc n)) \<in> S" by blast
                  from rec this have "(?gss, ?gboth (Suc n)) \<in> S" using trans_S unfolding trans_def by blast
                  with oTrue show ?thesis by simp
                qed
              qed
            qed
          qed
        qed
      qed
      with spec[OF this, of "length ids"] iids have "(Fun g (?ss ids), Fun g (?ts ids)) \<in> S" by auto
      with g ss ts pi have "(Fun ?f (map ((!) (map ?pi bef @ ?pi s # map ?pi aft)) ids),
          Fun ?f (map ((!) (map ?pi bef @ ?pi t # map ?pi aft)) ids)) \<in> S"
          by auto 
      then show ?thesis using AFList by simp
    qed
  } note main = this
  show "ctxt.closed ?S"
    unfolding afs_rel_def afs_rule_def
    by (rule one_imp_ctxt_closed, insert main, auto)
qed

lemma (in afs_redtriple) ctxt_closed:
  assumes mono_pi: "mono_afs \<pi>"
    and monoS: "ctxt.closed S"
  shows "ctxt.closed (afs_rel \<pi> S)"
  by (rule mono_afs_ctxt_closed[OF mono_pi trans_S monoS])

lemma mono_afs_af_rel_ctxt_closed:
  assumes mono_pi: "mono_afs \<pi>"
    and trans_S: "trans S" 
    and monoS: "ctxt.closed (S :: ('f,'v)trs)"
  shows "ctxt.closed (af_rel \<pi> S)"
proof -
  let ?S = "af_rel \<pi> S"
  let ?pi = "af_term \<pi>"
  {
    fix f bef s t aft
    assume st: "(?pi s, ?pi t) \<in> S"
    let ?bsa = "bef @ s # aft"
    let ?bta = "bef @ t # aft"
    let ?fs = "Fun f ?bsa"
    let ?ft = "Fun f ?bta"
    let ?l = "Suc (length bef + length aft)"
    let ?lba = "length bef + length aft"
    let ?e = "afs \<pi> (f,?l)"
    from mono_afs[OF mono_pi] have mono_e: "mono_af_entry ?l ?e" .
    have wf_e: "wf_af_entry ?l ?e" by (rule afs)
    have "(?pi ?fs, ?pi ?ft) \<in> S"
    proof (cases ?e)
      case (Collapse i)
      with mono_e wf_e show ?thesis using st by auto
    next
      case (AFList ids)
      let ?ids = "{n | n. n < ?l}"
      obtain l where l: "?l = l" by auto
      from AFList wf_e have ids1: "set ids \<subseteq> ?ids" by auto
      from AFList mono_e have ids2: "?ids \<subseteq> set ids" 	
        by (simp only: l, auto)
      from ids1 ids2 have ids: "set ids = ?ids" by auto
      let ?eq = "\<lambda> i. ?pi (?bsa ! i) = ?pi (?bta ! i)"
      let ?gr = "\<lambda> i. (?pi (?bsa ! i), ?pi (?bta ! i)) \<in> S"
      let ?lb = "length bef"
      have geq: "\<forall> i. ?eq i \<or> ?gr i"
      proof
        fix i
        {
          assume "i < ?lb" then have "?eq i" by (simp add: nth_append)
        }
        moreover
        {
          assume "i = ?lb"
          with st have "?gr i" by (simp add: nth_append)
        }
        moreover 
        {
          assume i2: "i > ?lb"
          then obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
          have "?eq i" unfolding nth_append using i2 k1 by auto
        }
        moreover
        {
          have "i < ?lb \<or> i = ?lb \<or> i > ?lb" by arith
        }
        ultimately show "?eq i \<or> ?gr i" by blast
      qed
      from ids have lb: "?lb \<in> set ids" by auto
      from st have "?gr ?lb" by (simp add: nth_append)
      with lb have gr: "\<exists> i \<in> set ids. ?gr i \<and> i = ?lb" by auto
      obtain ss ts pi where ss: "ss = ?bsa" and ts: "ts = ?bta" 
        and pi: "pi = (?pi :: ('f,'v)term \<Rightarrow> ('f,'v)term)" by auto
      let ?eq = "\<lambda> i. pi (ss ! i) = pi (ts ! i)"
      let ?gr = "\<lambda> i. (pi (ss ! i), pi (ts ! i)) \<in> S"
      let ?ss = "map ((!) (map pi ss))"
      let ?ts = "map ((!) (map pi ts))"
      let ?both = "\<lambda> n. ?ts (take n ids) @ ?ss (drop n ids)"
      let ?gss = "Fun f (?ss ids)"
      let ?gboth = "\<lambda> n. Fun f (?both n)"
      from geq ss ts pi have geq: "\<forall> i. ?eq i \<or> ?gr i" by auto
      from gr ss ts pi have "\<exists> i \<in> set ids. ?gr i \<and> i = ?lb" by auto
      from this obtain i where i: "?gr i" and iids: "i \<in> set ids" and idef: "i = ?lb" by auto
      have "\<forall> n. (i \<in> set (take n ids) \<longrightarrow> (?gss, ?gboth n) \<in> S) \<and> (i \<notin> set (take n ids) \<longrightarrow> ?gss = ?gboth n)" (is "\<forall> n. ?p n") 
      proof (intro allI)
        fix n
        show "?p n"
        proof (induct n, simp)
          case (Suc n)
          show ?case
          proof (cases "n \<ge> length ids")
            case True
            with Suc show ?thesis by simp
          next
            case False 
            then have n: "n < length ids" by auto
            let ?bef = "?ts (take n ids)"
            let ?aft = "?ss (drop (Suc n) ids)"
            let ?ssn = "pi (ss ! (ids ! n))"
            let ?tsn = "pi (ts ! (ids ! n))"
            from n ids have ids_n: "ids ! n < ?l" by force
            have gn: "?both n = ?bef @ ?ssn # ?aft"
              by (simp only: Cons_nth_drop_Suc[OF n, symmetric], simp, simp add: nth_map[of "ids ! n" ?bsa pi, simplified, OF ids_n] ss)
            have gsn: "?both (Suc n) = ?bef @ ?tsn # ?aft"
              by (simp only: take_Suc_conv_app_nth[OF n], simp, simp add: nth_map[of "ids ! n" ?bta pi, simplified, OF ids_n] ts)
            {
              assume "?ssn \<noteq> ?tsn \<or> ids ! n = i"
              with geq i have "(?ssn, ?tsn) \<in> S" by blast		
              from ctxt_closed_one[OF monoS this] 
              have gnsn: "(?gboth n, ?gboth (Suc n)) \<in> S"
                by (simp only: gn gsn)
            } note noteq_i = this
            {
              assume "ids ! n \<noteq> i"
              {
                assume "ids ! n < ?lb"
                then have "?gboth (Suc n) = ?gboth n" 
                  by (simp add: gn gsn, simp add: ss ts) 
              }
              moreover
              {
                assume i2: "ids ! n > ?lb"
                have "?gboth (Suc n) = ?gboth n" unfolding term.simps gn gsn 
                  using i2 ss ts by (simp add: nth_append)
              }
              moreover
              {
                from \<open>ids ! n \<noteq> i\<close> have "ids ! n < ?lb \<or> ids ! n > ?lb" by (simp only: idef, arith)
              }
              ultimately have "?gboth (Suc n) = ?gboth n" by blast
            } note eq = this	      
            show ?thesis 
            proof (cases "i \<in> set (take (Suc n) ids)")
              case False 
              then have i_not: "i \<notin> set (take n ids)" and i_not2: "ids ! n \<noteq> i" using take_Suc_conv_app_nth[OF n] by auto
              from i_not Suc have rec: "?gss = ?gboth n" by blast 
              with False eq[OF i_not2] rec show ?thesis by simp 
            next
              case True note oTrue = this
              show ?thesis
              proof (cases "i \<in> set (take n ids)")
                case False
                with True have id: "ids ! n = i" using take_Suc_conv_app_nth[OF n] by auto
                from False Suc have rec: "?gss = ?gboth n" by blast
                from noteq_i id have "(?gboth n, ?gboth (Suc n)) \<in> S" by blast
                with True rec show ?thesis by simp
              next
                case True
                with Suc have rec: "(?gss, ?gboth n) \<in> S" by blast
                show ?thesis
                proof (cases "ids ! n = i")
                  case False
                  from rec eq[OF False] oTrue show ?thesis by simp
                next
                  case True
                  with noteq_i have "(?gboth n, ?gboth (Suc n)) \<in> S" by blast
                  from rec this have "(?gss, ?gboth (Suc n)) \<in> S" using trans_S unfolding trans_def by blast
                  with oTrue show ?thesis by simp
                qed
              qed
            qed
          qed
        qed
      qed
      with spec[OF this, of "length ids"] iids have "(Fun f (?ss ids), Fun f (?ts ids)) \<in> S" by auto
      with ss ts pi have "(Fun f (map ((!) (map ?pi bef @ ?pi s # map ?pi aft)) ids),
          Fun f (map ((!) (map ?pi bef @ ?pi t # map ?pi aft)) ids)) \<in> S"
          by auto 
      then show ?thesis using AFList by simp
    qed
  } note main = this
  show "ctxt.closed ?S"
    unfolding af_rel_def af_rule_alt_def
    by (rule one_imp_ctxt_closed, insert main, auto)
qed

lemma (in af_redtriple) ctxt_closed:
  assumes mono_pi: "mono_afs \<pi>"
    and monoS: "ctxt.closed S"
  shows "ctxt.closed (af_rel \<pi> S)"
  by (rule mono_afs_af_rel_ctxt_closed[OF mono_pi trans_S monoS])

sublocale afs_redtriple \<subseteq> redtriple_order "afs_rel \<pi> S" "afs_rel \<pi> NS" "afs_rel \<pi> NST"
proof -
  let ?S = "afs_rel \<pi> S"
  let ?NS = "afs_rel \<pi> NS"
  let ?NST = "afs_rel \<pi> NST"
  show "redtriple_order ?S ?NS ?NST"
  proof
    show "refl ?NS" by (rule afs_refl[OF refl_NS])
    show "refl ?NST" by (rule afs_refl[OF refl_NST])
    show "trans ?S" by (rule afs_trans[OF trans_S])
    show "trans ?NS" by (rule afs_trans[OF trans_NS])
    show "trans ?NST" by (rule afs_trans[OF trans_NST])
  qed 
qed

sublocale af_redtriple \<subseteq> redtriple_order "af_rel \<pi> S" "af_rel \<pi> NS" "af_rel \<pi> NST"
proof -
  let ?S = "af_rel \<pi> S"
  let ?NS = "af_rel \<pi> NS"
  let ?NST = "af_rel \<pi> NST"
  show "redtriple_order ?S ?NS ?NST"
  proof
    show "refl ?NS" by (rule af_refl[OF refl_NS])
    show "refl ?NST" by (rule af_refl[OF refl_NST])
    show "trans ?S" by (rule af_trans[OF trans_S])
    show "trans ?NS" by (rule af_trans[OF trans_NS])
    show "trans ?NST" by (rule af_trans[OF trans_NST])
  qed 
qed

definition permutation_afs :: "'f afs \<Rightarrow> bool" where
  "permutation_afs \<pi> \<equiv> \<forall> (f,n) \<in> afs_syms \<pi>. 
    case afs \<pi> (f,n) of 
      AFList xs \<Rightarrow> set xs = {0 ..< n} \<and> distinct xs
    | _ \<Rightarrow> False"

context
  fixes \<pi> :: "'f afs"
  assumes perm: "permutation_afs \<pi>"
begin

lemma perm: "\<exists>xs. afs \<pi> (f, n) = AFList xs \<and> set xs = {0..<n} \<and> distinct xs"
proof (cases "(f,n) \<in> afs_syms \<pi>")
  case True
  with perm show ?thesis unfolding permutation_afs_def by (cases "afs \<pi> (f,n)", auto)
next
  case False
  from afs_syms[OF this] show ?thesis unfolding default_af_entry_def by auto
qed

fun af_ctxt :: "('f,'v)ctxt \<Rightarrow> ('f,'v)ctxt" where
  "af_ctxt Hole = Hole"
| "af_ctxt (More f bef C aft) = (let i = length bef;
    n = Suc (i + length aft);
    ts = map (af_term \<pi>) (bef @ C\<langle>undefined\<rangle> # aft) in case afs \<pi> (f,n) of
      AFList xs \<Rightarrow> let i' = SOME i'. i' < n \<and> xs ! i' = i
      in More f (map (\<lambda> j. ts ! (xs ! j)) [0 ..< i']) (af_ctxt C) (map (\<lambda> j. ts ! (xs ! j)) [Suc i' ..< n]))"

lemma af_ctxt[simp]: "af_term \<pi> (C \<langle> t \<rangle>) = (af_ctxt C) \<langle> af_term \<pi> t \<rangle>"
proof (induct C)
  case (More f bef C aft)
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  from perm[of f ?n] obtain xs where pi: "afs \<pi> (f,?n) = AFList xs" and xs: "set xs = {0 ..< ?n}" and d: "distinct xs" by auto
  from distinct_card[OF d] have len: "length xs = ?n" unfolding xs by simp
  let ?p = "\<lambda> i'. i' < ?n \<and> xs ! i' = ?i"
  define i' where "i' = (SOME i'. ?p i')"
  have "?i \<in> set xs" unfolding xs by auto
  with len have "\<exists> i'. ?p i'" unfolding set_conv_nth by auto
  from someI_ex[OF this] have i': "?p i'" unfolding i'_def by simp
  let ?ts = "map (af_term \<pi>) (bef @ C\<langle>undefined\<rangle> # aft)"
  have "(af_ctxt (More f bef C aft)) \<langle> af_term \<pi> t \<rangle> = (More f (map (\<lambda>j. ?ts ! (xs ! j)) [0..<i']) (af_ctxt C)
      (map (\<lambda>j. ?ts ! (xs ! j)) [Suc i'..<?n]))\<langle>af_term \<pi> t\<rangle>" (is "?l = _")
    unfolding af_ctxt.simps Let_def pi af_entry.simps i'_def by simp
  also have "\<dots> = Fun f ((map (\<lambda>j. ?ts ! (xs ! j)) [0..<i']) @ af_term \<pi> (C \<langle> t \<rangle>) # (map (\<lambda>j. ?ts ! (xs ! j)) [Suc i'..<length xs]))"
    (is "_ = Fun f ?r") using More len by simp
  finally have id1: "?l = Fun f ?r" .  
  let ?is = "[0..<i'] @ i' # [Suc i' ..< length xs]" 
  have "xs = map (\<lambda> i. xs ! i) [0..<?n]" unfolding len[symmetric] by (rule nth_equalityI, auto)
  also have "[0..<?n] = ?is" using i' 
    by (metis len upt_append upt_conv_Cons)
  finally have id3: "(map (\<lambda> i. xs ! i) ?is) = xs" by simp
  have "af_term \<pi> (More f bef C aft)\<langle>t\<rangle> = 
    Fun f (map (\<lambda>x. map_funs_term filtered_fun ((map (afs_term \<pi>) bef @ afs_term \<pi> C\<langle>t\<rangle> # map (afs_term \<pi>) aft) ! x)) xs)" 
    (is "?l = _") unfolding af_term_def by (simp add: pi o_def) 
  also have "\<dots> = Fun f (map (\<lambda>x. ((map (af_term \<pi>) bef @ af_term \<pi> C\<langle>t\<rangle> # map (af_term \<pi>) aft) ! x)) xs)"
    by (simp add: xs af_term_def[abs_def], auto simp: nth_append, case_tac "x - length bef", auto)
  also have "\<dots> = Fun f (map (\<lambda>x. ((map (af_term \<pi>) bef @ af_term \<pi> C\<langle>t\<rangle> # map (af_term \<pi>) aft) ! x)) (map (\<lambda> i. xs ! i) ?is))"
    (is "_ = Fun f ?r'") unfolding id3 ..
  finally have id2: "?l = Fun f ?r'" by simp
  have id4: "(Fun f ?r' = Fun f ?r) = (?r' = ?r)" by simp
  show ?case unfolding id1 id2 id4
  proof -
    note i' = i'[folded len]
    have i: "?i < length xs" unfolding len by simp
    show "?r' = ?r" 
    proof (rule nth_equalityI, simp)
      fix j
      assume "j < length ?r'"
      from this[unfolded id3] have j: "j < length xs" by simp
      with xs have xsj: "xs ! j < length xs" unfolding len[symmetric] by auto
      show "?r' ! j = ?r ! j"
      proof (cases "j = i'")
        case True
        show ?thesis using i' unfolding True
          by (simp add: nth_append)
      next
        case False
        let ?ts' = "map (af_term \<pi>) (bef @ C\<langle>undefined\<rangle> # aft)"
        from False d j i' have xsji: "xs ! j \<noteq> ?i" 
          by (metis nth_eq_iff_index_eq)
        have "?r' ! j = ?ts' ! (xs ! j)" unfolding id3 nth_map[OF j]
          using xsji xsj unfolding len by (auto simp: nth_append)
        also have "\<dots> = ?r ! j" using False i' j by (simp add: nth_append)
        finally show ?thesis .
      qed
    qed
  qed
qed simp

lemma step_imp_afs_rstep:
  "(s, t) \<in> rstep R \<Longrightarrow> (af_term \<pi> s, af_term \<pi> t) \<in> rstep (af_rule \<pi> ` R)"
proof (induct rule: rstep_induct_rule)
  case (IH C \<sigma> l r)
  let ?a = "af_term \<pi>"
  let ?R = "af_rule \<pi> ` R"
  define s where "s = ?a (l \<cdot> \<sigma>)"
  define t where "t = ?a (r \<cdot> \<sigma>)"
  from IH have rule: "(?a l, ?a r) \<in> ?R" unfolding af_rule_def af_term_def afs_rule_def by force
  have "(?a (l \<cdot> \<sigma>), ?a (r \<cdot> \<sigma>)) \<in> rstep ?R"
    by (rule rstepI[OF rule, of _ Hole], auto simp: af_term_def)
  from rstep_ctxt[OF this, of "af_ctxt C"] show ?case by simp
qed

lemmas steps_imp_afs_rsteps = af_rsteps

lemma step_imp_afs_rel_rstep: assumes st: "(s,t) \<in> relto (rstep R) (rstep S)"
  shows "(af_term \<pi> s, af_term \<pi> t) \<in> relto (rstep (af_rule \<pi> ` R)) (rstep (af_rule \<pi> ` S))"
proof -
  let ?a = "af_term \<pi>"  
  from st obtain u v where su: "(s,u) \<in> (rstep S)^*" and uv: "(u,v) \<in> (rstep R)" and vt: "(v,t) \<in> (rstep S)^*" by auto
  from steps_imp_afs_rsteps[OF su] step_imp_afs_rstep[OF uv] steps_imp_afs_rsteps[OF vt]
  show ?thesis by blast
qed

lemma af_SN_relto_rstep: assumes SN: "SN (relto (rstep (af_rule \<pi> ` R)) (rstep (af_rule \<pi> ` S)))" (is "SN ?R'")
  shows "SN (relto (rstep R) (rstep S))" (is "SN ?R")
proof
  fix f
  assume steps: "\<forall> i. (f i, f (Suc i)) \<in> ?R"
  define g where "g = (\<lambda> i. (af_term \<pi> (f i)))"
  from step_imp_afs_rel_rstep[OF spec[OF steps]]
  have "\<And> i. (g i, g (Suc i)) \<in> ?R'" unfolding g_def by auto
  with SN show False unfolding SN_defs by auto
qed

lemma af_SN_rstep: assumes SN: "SN (rstep (af_rule \<pi> ` R))"
  shows "SN (rstep R)" using af_SN_relto_rstep[of "{}" R] SN by simp
end
  

type_synonym 'f afs_list = "(('f \<times> nat) \<times> af_entry)list"

abbreviation (input) afs_of' :: "('f :: compare_order) afs_list \<Rightarrow> 'f \<times> nat \<Rightarrow> af_entry" where 
  "afs_of' \<pi> \<equiv> fun_of_map_fun (ceta_map_of \<pi>) (\<lambda> fn. default_af_entry (snd fn))"

lift_definition (code_dt) afs_of :: "('f :: compare_order) afs_list \<Rightarrow> 'f afs option" 
  is "\<lambda> \<pi>. if (\<forall> fn_entry \<in> set \<pi>. case fn_entry of ((f,n),e) \<Rightarrow>
    wf_af_entry n e) then 
    Some (afs_of' \<pi>, set (map fst \<pi>)) else None"
  using map_of_SomeD by (fastforce split: option.splits)

lemma afs_of_Some_afs_syms: "afs_of \<pi> = Some pair
  \<Longrightarrow> afs_syms pair = set (map fst \<pi>)"
  using afs_of.rep_eq[of \<pi>]
  by (transfer, auto split: if_splits)


definition afs_to_unused_arity :: "'f afs \<Rightarrow> nat" where
  "afs_to_unused_arity \<pi> \<equiv> if finite (afs_syms \<pi>) 
    then (SOME x. (\<forall> f n. n \<ge> x \<longrightarrow> afs \<pi> (f,n) = default_af_entry n)) 
    else 0"

lemma afs_to_unused_arity: assumes fin: "finite (afs_syms \<pi>)"
  and n: "n \<ge> afs_to_unused_arity \<pi>"
  shows "afs \<pi> (f,n) = default_af_entry n"
proof -
  from finite_list[OF fin] obtain fs where fs: "afs_syms \<pi> = set fs" by blast
  let ?P = "\<lambda> x. \<forall> f n. n \<ge> x \<longrightarrow> afs \<pi> (f,n) = default_af_entry n"
  let ?m = "(Suc (max_list (map snd fs)))"
  let ?u = "afs_to_unused_arity \<pi>"
  from fin have u: "?u = (SOME x. ?P x)" unfolding afs_to_unused_arity_def by auto
  have "?P ?m"
  proof (intro allI impI)
    fix f n
    assume "?m \<le> n"
    then have "(f,n) \<notin> set fs" using max_list[of n "map snd fs"] by auto
    from afs_syms[OF this[folded fs]] show "afs \<pi> (f,n) = default_af_entry n" .
  qed
  from someI[of ?P, OF this, folded u] n 
  show ?thesis by auto
qed

lemma default_af_entry_id: 
  assumes "afs \<pi> (f,length ts) = default_af_entry (length ts)"
  shows "afs_term \<pi> (Fun f ts) = Fun (FPair f (length ts)) (map (afs_term \<pi>) ts)"
  by (simp add: default_af_entry_def assms Let_def, simp only: list_eq_iff_nth_eq, simp)

lemma default_af_entry_id_af: 
  assumes "afs \<pi> (f,length ts) = default_af_entry (length ts)"
  shows "af_term \<pi> (Fun f ts) = Fun f (map (af_term \<pi>) ts)"
  by (simp add: default_af_entry_def assms Let_def, simp only: list_eq_iff_nth_eq, simp)

definition afs_to_af :: "('f :: compare_order) afs \<Rightarrow> 'f af" where
  "afs_to_af pi fn \<equiv> case afs pi fn of 
        Collapse j \<Rightarrow> {j}
      | AFList ids \<Rightarrow> set ids"

definition afs_with_af :: "('f :: compare_order) afs \<Rightarrow> 'f af \<Rightarrow> 'f af" where
  "afs_with_af pi pi' fn \<equiv> case afs pi fn of 
        Collapse j \<Rightarrow> {j}
      | AFList ids \<Rightarrow> if ids = [0 ..< snd fn] then pi' fn else set ids"
  (* TODO: currently this only takes the second filter, if the first is identity,
      this should be changed later on *)

lemma apply_af_entry_const_is_id: "apply_af_entry (FPair f (0 :: nat)) (afs \<pi> (f, 0)) [] = Fun (FPair f 0) []"
proof -
  let ?e = "afs \<pi> (f, 0)"
  have "wf_af_entry 0 ?e" by (rule afs)
  then show ?thesis by (cases ?e, simp_all)
qed

lemma af_compatible:
  fixes pi :: "('f :: compare_order) afs"
  assumes refl_NS: "refl NS"
  and all_ctxt_closed: "all_ctxt_closed UNIV NS"
  shows "af_compatible (afs_to_af pi) (afs_rel pi (NS :: ('f filtered,'v)term rel))" (is "af_compatible ?af ?NS")
  unfolding af_compatible_def
proof (intro allI)      
  fix f :: 'f and bef :: "('f,'v)term list" and s t :: "('f,'v)term" and  aft
  let ?pi = pi
  let ?bsa = "bef @ s # aft"
  let ?bta = "bef @ t # aft"
  let ?lb = "length bef"
  let ?l = "Suc (?lb + length aft)"    
  let ?s = "Fun f ?bsa"
  let ?t = "Fun f ?bta"
  show "?lb \<in> ?af (f, ?l) \<or> (?s,?t) \<in> ?NS"
  proof (cases "?lb \<in> ?af (f, ?l)")
    case False
    let ?e = "afs ?pi (f, ?l)"
    have wf: "wf_af_entry ?l ?e" by (rule afs)
    let ?ls = "length (bef @ s # aft)"
    let ?lt = "length (bef @ t # aft)"
    let ?msa = "map (afs_term ?pi) ?bsa"
    let ?mta = "map (afs_term ?pi) ?bta"
    let ?pfs = "apply_af_entry (FPair f ?l) ?e ?msa"
    let ?pft = "apply_af_entry (FPair f ?l) ?e ?mta"
    have all2: "\<forall> i < ?l. i \<noteq> ?lb \<longrightarrow> (?msa ! i, ?mta ! i) \<in> NS" 
    proof (intro allI impI)
      fix i
      assume "i < ?l" and ib: "i \<noteq> ?lb"
      then have i_s: "i < ?ls" and i_t: "i < ?lt" by simp_all
      {
        assume bef: "i < length bef"
        with refl_NS have "(?msa ! i, ?mta ! i) \<in> NS" unfolding refl_on_def 
          by (simp only: nth_map[OF i_s], simp add: nth_append)
      }
      moreover
      {
        assume i: "i > length bef"
        from this obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
        with i_s have k2: "k < length aft" by auto
        from i refl_NS have "(?msa ! i, ?mta ! i) \<in> NS" unfolding refl_on_def 
          by (simp only: nth_map[OF i_s] nth_map[OF i_t], simp add: nth_append k1)
      } 
      moreover
      have "i < length bef \<or> i = length bef \<or> i > length bef" by auto
      ultimately
      show "(?msa ! i, ?mta ! i) \<in> NS" using ib by blast
    qed 
    have "(?pfs,?pft) \<in> NS" 
    proof (cases ?e)
      case (Collapse i)
      with wf have len: "i < ?l"  by simp
      from Collapse[simplified] False have "i \<noteq> ?lb" unfolding afs_to_af_def by auto
      with all2 len Collapse show ?thesis by auto
    next
      case (AFList ids)
      with wf have ids: "\<forall> i \<in> set ids. i < ?l" by simp
      show ?thesis 
      proof (unfold AFList apply_af_entry.simps)
        let ?msi = "map ((!) (map (afs_term ?pi) ?bsa)) ids"
        let ?mti = "map ((!) (map (afs_term ?pi) ?bta)) ids"
        from ids False AFList[simplified] have "\<forall> i \<in> set ids. i \<noteq> ?lb" unfolding afs_to_af_def 
          by auto
        with ids all2 have args: "\<forall> i < length ids. (?msi ! i, ?mti ! i) \<in> NS" by auto
        show "(Fun (FPair f ?l) ?msi, Fun (FPair f ?l) ?mti) \<in> NS"
          by (rule all_ctxt_closedD[OF all_ctxt_closed], insert args, auto)
      qed
    qed
    then show "?lb \<in> afs_to_af pi (f, ?l) \<or> (Fun f ?bsa, Fun f ?bta) \<in> afs_rel ?pi NS" unfolding afs_rel_def afs_rule_def by (simp add: afs)
  qed simp
qed

lemma af_compatible_afs_with_af:
  fixes pi :: "('f :: compare_order) afs"
  assumes refl_NS: "refl NS"
    and af_compat: "af_compatible pi' NS" 
    and all_ctxt_closed: "all_ctxt_closed UNIV NS"
  shows "af_compatible (afs_with_af pi pi') (af_rel pi (NS :: ('f,'v)term rel))" 
    (is "af_compatible ?af ?NS")
  unfolding af_compatible_def
proof (intro allI)      
  fix f :: 'f and bef :: "('f,'v)term list" and s t :: "('f,'v)term" and  aft
  let ?pi = pi
  let ?bsa = "bef @ s # aft"
  let ?bta = "bef @ t # aft"
  let ?lb = "length bef"
  let ?l = "Suc (?lb + length aft)"    
  let ?s = "Fun f ?bsa"
  let ?t = "Fun f ?bta"
  show "?lb \<in> ?af (f, ?l) \<or> (?s,?t) \<in> ?NS"
  proof (cases "?lb \<in> ?af (f, ?l)")
    case False
    let ?e = "afs ?pi (f, ?l)"
    have wf: "wf_af_entry ?l ?e" by (rule afs)
    let ?ls = "length (bef @ s # aft)"
    let ?lt = "length (bef @ t # aft)"
    let ?msa = "map (af_term ?pi) ?bsa"
    let ?mta = "map (af_term ?pi) ?bta"
    let ?pfs = "apply_af_entry f ?e ?msa"
    let ?pft = "apply_af_entry f ?e ?mta"
    have all2: "\<forall> i < ?l. i \<noteq> ?lb \<longrightarrow> (?msa ! i, ?mta ! i) \<in> NS" 
    proof (intro allI impI)
      fix i
      assume "i < ?l" and ib: "i \<noteq> ?lb"
      then have i_s: "i < ?ls" and i_t: "i < ?lt" by simp_all
      {
        assume bef: "i < length bef"
        with refl_NS have "(?msa ! i, ?mta ! i) \<in> NS" unfolding refl_on_def 
          by (simp only: nth_map[OF i_s], simp add: nth_append)
      }
      moreover
      {
        assume i: "i > length bef"
        from this obtain k where k1: "i - length bef = Suc k" by (cases "i - length bef", arith+)
        with i_s have k2: "k < length aft" by auto
        from i refl_NS have "(?msa ! i, ?mta ! i) \<in> NS" unfolding refl_on_def 
          by (simp only: nth_map[OF i_s] nth_map[OF i_t], simp add: nth_append k1)
      } 
      moreover
      have "i < length bef \<or> i = length bef \<or> i > length bef" by auto
      ultimately
      show "(?msa ! i, ?mta ! i) \<in> NS" using ib by blast
    qed 
    have "(?pfs,?pft) \<in> NS" 
    proof (cases ?e)
      case (Collapse i)
      with wf have len: "i < ?l"  by simp
      from Collapse[simplified] False have "i \<noteq> ?lb" unfolding afs_with_af_def by auto
      with all2 len Collapse show ?thesis by auto
    next
      case (AFList ids)
      with wf have ids: "\<forall> i \<in> set ids. i < ?l" by simp
      show ?thesis
      proof (cases "ids = [0..<?l]")
        case notId: False
        show ?thesis 
        proof (unfold AFList apply_af_entry.simps)
          let ?msi = "map ((!) (map (af_term ?pi) ?bsa)) ids"
          let ?mti = "map ((!) (map (af_term ?pi) ?bta)) ids"
          from ids notId False AFList[simplified] have "\<forall> i \<in> set ids. i \<noteq> ?lb" unfolding afs_with_af_def 
            by auto
          with ids all2 have args: "\<forall> i < length ids. (?msi ! i, ?mti ! i) \<in> NS" by auto
          show "(Fun f ?msi, Fun f ?mti) \<in> NS"
            by (rule all_ctxt_closedD[OF all_ctxt_closed], insert args, auto)
        qed
      next
        case True
        have list: "[0 ..< ?l] = [0 ..< ?lb] @ ?lb # [Suc ?lb ..< ?l]" 
          by (simp add: upt_eq_lel_conv)
        have cong: "\<And> x1 x2 x3 y1 y2 y3. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 
          \<Longrightarrow> x1 @ x2 # x3 = y1 @ y2 # y3" by auto  
        have [simp]: "i < n \<Longrightarrow> \<not> i < n - Suc 0 \<Longrightarrow> n - Suc 0 = i" for i n by linarith
        have id: "(?pfs,?pft) = (Fun f ?msa, Fun f ?mta)" 
          unfolding AFList True apply_af_entry.simps unfolding list prod.simps term.simps
            map_append prod.inject list.map
          by ((intro conjI refl cong; (intro nth_equalityI)?), auto simp: nth_append)
        from False[unfolded afs_with_af_def AFList af_entry.simps True]
        have "?lb \<notin> pi' (f,?l)" by auto
        thus ?thesis unfolding id unfolding map_append
          using af_compat[unfolded af_compatible_def, rule_format, 
              of "map (af_term ?pi) bef" f "map (af_term ?pi) aft"] by auto
      qed
    qed
    then show "?lb \<in> afs_with_af pi pi' (f, ?l) \<or> (Fun f ?bsa, Fun f ?bta) \<in> af_rel ?pi NS" 
      unfolding af_rel_def af_rule_alt_def by (simp add: afs)
  qed simp
qed

lemma af_ce_compat:
  fixes pi :: "('f :: {showl,compare_order}) afs"
    and NS :: "('f filtered, 'v :: showl) term rel"
  assumes fin: "finite (afs_syms pi)"
    and ce_compat: "ce_compatible NS"
  shows "ce_compatible (afs_rel pi NS)"
proof (unfold ce_compatible_def)
  let ?pi = "afs pi"
  let ?NS = "afs_rel pi NS"
  let ?ar = "afs_to_unused_arity pi"
  let ?sar = "Suc (Suc ?ar)"
  have pi2: "\<And> m c. m \<ge> ?sar \<Longrightarrow> ?pi (c, m) = default_af_entry m"
    by (rule afs_to_unused_arity[OF fin], simp)
  from ce_compatibleE[OF ce_compat] obtain n where ce_NS: "\<And> m c . m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS" by metis
  let ?n = "max n ?sar"
  show "\<exists> n. \<forall> m \<ge> n. \<forall> c. ce_trs (c,m) \<subseteq> ?NS"
  proof (rule exI[of _ ?n], intro allI impI)
    fix m c d
    assume m: "m \<ge> ?n"
    then have mn: "m \<ge> n" by simp
    {
      fix t s :: "('f,'v)term"
      let ?list = "t # s # replicate m (Var undefined)"
      from pi2 m have id: "?pi (c,length ?list) = default_af_entry (length ?list)" by simp
      have "(afs_term pi (Fun c ?list), afs_term pi t) \<in> NS"
      	using ce_NS[OF mn, simplified ce_trs.simps, of "FPair c (Suc (Suc m))"]  
        by (simp only: default_af_entry_id[of pi c ?list, OF id], auto simp: apply_af_entry_const_is_id)
    }
    moreover
    {
      fix t s :: "('f,'v)term"
      let ?list = "t # s # replicate m (Var undefined)"
      from pi2 m have id: "?pi (c,length ?list) = default_af_entry (length ?list)" by simp
      have "(afs_term pi (Fun c ?list), afs_term pi s) \<in> NS"
      using ce_NS[OF mn, simplified ce_trs.simps, of "FPair c (Suc (Suc m))"]  
        by (simp only: default_af_entry_id[of pi c ?list, OF id], auto simp: apply_af_entry_const_is_id)
    }
    ultimately
    show "ce_trs (c,m) \<subseteq> ?NS"
      by (auto simp: ce_trs.simps afs_rel_def afs_rule_def pi2)      
  qed
qed

lemma af_ce_compat_af_rel:
  fixes pi :: "('f :: {showl,compare_order}) afs"
    and NS :: "('f, 'v :: showl) term rel"
  assumes fin: "finite (afs_syms pi)"
    and ce_compat: "ce_compatible NS"
  shows "ce_compatible (af_rel pi NS)"
proof (unfold ce_compatible_def)
  let ?pi = "afs pi"
  let ?NS = "af_rel pi NS"
  let ?ar = "afs_to_unused_arity pi"
  let ?sar = "Suc (Suc ?ar)"
  have pi2: "\<And> m c. m \<ge> ?sar \<Longrightarrow> ?pi (c, m) = default_af_entry m"
    by (rule afs_to_unused_arity[OF fin], simp)
  from ce_compatibleE[OF ce_compat] obtain n where ce_NS: "\<And> m c . m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS" by metis
  let ?n = "max n ?sar"
  show "\<exists> n. \<forall> m \<ge> n. \<forall> c. ce_trs (c,m) \<subseteq> ?NS"
  proof (rule exI[of _ ?n], intro allI impI)
    fix m c d
    assume m: "m \<ge> ?n"
    then have mn: "m \<ge> n" by simp
    {
      fix t s :: "('f,'v)term"
      let ?list = "t # s # replicate m (Var undefined)"
      from pi2 m have id: "?pi (c,length ?list) = default_af_entry (length ?list)" by simp
      have "(af_term pi (Fun c ?list), af_term pi t) \<in> NS"
      	using ce_NS[OF mn, simplified ce_trs.simps, of "c "]  
        by (simp only: default_af_entry_id_af[of pi c ?list, OF id], auto simp: apply_af_entry_const_is_id)
    }
    moreover
    {
      fix t s :: "('f,'v)term"
      let ?list = "t # s # replicate m (Var undefined)"
      from pi2 m have id: "?pi (c,length ?list) = default_af_entry (length ?list)" by simp
      have "(af_term pi (Fun c ?list), af_term pi s) \<in> NS"
      using ce_NS[OF mn, simplified ce_trs.simps, of c]  
        by (simp only: default_af_entry_id_af[of pi c ?list, OF id], auto simp: apply_af_entry_const_is_id)
    }
    ultimately
    show "ce_trs (c,m) \<subseteq> ?NS"
      by (auto simp: ce_trs.simps af_rel_def af_rule_alt_def pi2)      
  qed
qed

definition check_mono_afs where 
  "check_mono_afs \<pi> = check (mono_afs \<pi>) (showsl (STR ''argument filter is not monotone''))"


fun showsl_afs :: "('f :: showl) afs_list \<Rightarrow> showsl"
where
  "showsl_afs af = foldr (\<lambda>((f, n), e).
    showsl (STR ''pi('') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl (STR '') = '') \<circ>
    (case e of
      Collapse i \<Rightarrow> showsl (Suc i)
     | AFList ids \<Rightarrow> showsl_list (map Suc ids)) \<circ> showsl_nl) af"

fun afs_sym :: "'f afs \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f filtered \<times> nat)list" where
  "afs_sym af (f,n) = (case afs af (f,n) of Collapse _ \<Rightarrow> [] | AFList is \<Rightarrow> [(FPair f n, length is)])" 

definition afs_sig :: "'f afs \<Rightarrow> ('f \<times> nat)list \<Rightarrow> ('f filtered \<times> nat)list" where
  "afs_sig af = List.maps (afs_sym af)" 

definition af_sig :: "'f afs \<Rightarrow> ('f \<times> nat)list \<Rightarrow> ('f \<times> nat)list" where
  "af_sig af = map (map_prod filtered_fun id) o afs_sig af" 

lemma afs_sig_funas_term: "funas_term t \<subseteq> set sig \<Longrightarrow> funas_term (afs_term pi t) \<subseteq> set (afs_sig pi sig)" 
proof (induct t)
  case (Fun f ts)
  let ?n = "length ts" 
  let ?f = "(f,?n)" 
  from Fun have f: "?f \<in> set sig" and 
    IH: "t \<in> set ts \<Longrightarrow> funas_term (afs_term pi t) \<subseteq> set (afs_sig pi sig)" for t by auto
  note afs = afs[of ?n pi f]
  show ?case
  proof (cases "afs pi ?f")
    case *: (Collapse i)
    hence "ts ! i \<in> set ts" using afs by auto
    from IH[OF this] show ?thesis using * afs by auto
  next
    case *: (AFList idx)
    from split_list[OF f] * have f: "(FPair f ?n, length idx) \<in> set (afs_sig pi sig)" 
      unfolding afs_sig_def List.maps_def by auto
    have i: "i \<in> set idx \<Longrightarrow> i < ?n" for i using afs * by auto
    have "i \<in> set idx \<Longrightarrow> funas_term (afs_term pi (ts ! i)) \<subseteq> set (afs_sig pi sig)" for i
      using i[of i] IH[of "ts ! i"] by auto
    with i f show ?thesis using * by auto
  qed
qed auto

lemma afs_sig_funas_rule: "set (funas_rule_list lr) \<subseteq> set sig \<Longrightarrow> set (funas_rule_list (afs_rule pi lr)) \<subseteq> set (afs_sig pi sig)" 
  using afs_sig_funas_term[of _ sig pi]
  by (cases lr, auto simp: funas_rule_def afs_rule_def)

lemma funas_term_list_af_term: "funas_term_list (af_term pi t) = map (map_prod filtered_fun id) (funas_term_list (afs_term pi t))" 
proof (induct t)
  case (Fun f ts)
  thus ?case using afs[of "length ts" pi f]
    by (cases "afs pi (f,length ts)", 
        auto simp: funas_term_list.simps Let_def o_def map_concat intro: arg_cong[of _ _ concat])
qed (auto simp: funas_term_list.simps)

lemma af_sig_funas_rule: assumes "set (funas_rule_list lr) \<subseteq> set sig"
  shows "set (funas_rule_list (af_rule pi lr)) \<subseteq> set (af_sig pi sig)" 
  using afs_sig_funas_rule[OF assms, of pi] unfolding af_rule_alt_def af_sig_def o_def
  unfolding funas_rule_list_def fst_conv snd_conv funas_term_list_af_term afs_rule_def by auto
  

lemma afs_sig_funas_trs_list: "funas_trs (set R) \<subseteq> set sig \<Longrightarrow> funas_trs (set (afs_rules pi R)) \<subseteq> set (afs_sig pi sig)" 
  using afs_sig_funas_rule[of _ sig pi]
  unfolding funas_trs_def afs_rules_def by force

lemma af_sig_funas_trs_list: "funas_trs (set R) \<subseteq> set sig \<Longrightarrow> funas_trs (set (af_rules pi R)) \<subseteq> set (af_sig pi sig)" 
  using af_sig_funas_rule[of _ sig pi]
  unfolding funas_trs_def afs_rules_def by force


definition
  filtered_rel_impl :: "'f afs_list \<Rightarrow> ('f filtered, 'v) rel_impl \<Rightarrow> ('f :: {showl, compare_order}, 'v :: showl) rel_impl"
where
  "filtered_rel_impl pi rp = (
    let afso = afs_of pi; afs = the afso; af = afs_to_af afs in \<lparr>
      rel_impl.valid = do {
        check (afso \<noteq> None) (showsl (STR ''invalid positions in argument filter''));  
        rel_impl.valid rp;
        rel_impl.top_refl rp;
        rel_impl.standard rp \<comment> \<open>might be generalized\<close>
      }, 
      standard = succeed,
      desc = showsl (STR ''Argument Filter:\<newline>'') \<circ> showsl_afs pi \<circ> showsl_nl \<circ> rel_impl.desc rp,
      s = afs_check (showsl (STR ''>'')) afs (rel_impl.s rp),
      ns = afs_check (showsl (STR ''>='')) afs (rel_impl.ns rp),
      nst = afs_check (showsl (STR ''>='')) afs (rel_impl.nst rp),
      af = af,
      top_af = full_af, \<comment> \<open>might be generalized\<close>
      SN = rel_impl.SN rp,
      subst_s = rel_impl.subst_s rp,
      ce_compat = rel_impl.ce_compat rp,
      co_rewr = rel_impl.co_rewr rp,
      top_mono = error (showsl_lit (STR ''top-mono with argument filter not yet supported'')),
      top_refl = succeed,
      mono_af = empty_af, \<comment> \<open>TODO: this is a crude underapproximation\<close>
      mono = \<lambda> sig. do {check_mono_afs afs; rel_impl.mono rp (afs_sig afs sig)},
      not_wst = map_option (\<lambda> fs. map fst pi @ map (\<lambda>(f, n). (fpair_f f, n)) fs) (rel_impl.not_wst rp),
      not_sst = None, \<comment> \<open>TODO: strict subterm currently not supported\<close> 
      cpx = no_complexity_check
    \<rparr>)"

lemma filtered_rel_impl: 
  fixes pi :: "('f :: {showl,compare_order}) afs_list" and
        rp :: "('f filtered, 'v :: showl)rel_impl"
  assumes rp: "rel_impl rp" 
  shows "rel_impl (filtered_rel_impl pi rp)"
  unfolding rel_impl_def
proof (intro allI impI, goal_cases)
  case (1 U)
  let ?rp = "filtered_rel_impl pi rp :: ('f, 'v)rel_impl"
  let ?pi = "the (afs_of pi)"
  let ?p = "afs_to_af ?pi"
  let ?pi' = "rel_impl.af rp"
  let ?pi'' = "rel_impl.af ?rp"
  let ?mpi'' = "rel_impl.mono_af ?rp"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
  let ?ws = "rel_impl.not_wst ?rp"
  let ?sst = "rel_impl.not_sst ?rp"
  have cpx: "?cpx = no_complexity_check" unfolding filtered_rel_impl_def Let_def by simp
  have pi'': "?pi'' = ?p" unfolding filtered_rel_impl_def Let_def by simp
  have mpi'': "?mpi'' = empty_af" unfolding filtered_rel_impl_def Let_def by simp
  let ?af_term = "afs_term ?pi"
  let ?af_list = "map (\<lambda> (s,t). (?af_term s, ?af_term t))"
  let ?U = "?af_list U" 
  let ?mono = "\<lambda> sig. funas_trs (set ?U) \<subseteq> set sig \<and> isOK(rel_impl.mono rp sig)" 
  from 1(1) have valid: "isOK(rel_impl.valid rp)" and std: "isOK(rel_impl.standard rp)" 
    and trefl: "isOK(rel_impl.top_refl rp)" and wf_afs: "afs_of pi \<noteq> None" 
    unfolding filtered_rel_impl_def by (auto simp: Let_def)
  then obtain \<pi> where \<pi>: "afs_of pi = Some \<pi>" by (cases, auto)
  from afs_of_Some_afs_syms[OF \<pi>] have fin: "finite (afs_syms ?pi)" unfolding \<pi> by auto
  from rp[unfolded rel_impl_def, rule_format, OF valid, of ?U]
  obtain S NS NST where rel_impl: "rel_impl_prop rp ?U S NS NST" by presburger
  from rel_impl have orient: 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.s rp st) \<Longrightarrow> st \<in> S" 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.ns rp st) \<Longrightarrow> st \<in> NS" 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.nst rp st) \<Longrightarrow> st \<in> NST" 
    by presburger+
  from rel_impl std trefl have *:
    "S \<subseteq> NS" 
    "irrefl S" 
    "ctxt.closed NS"
    "subst.closed NS" "subst.closed NST"
    "S O NS \<subseteq> S"
    "NS O S \<subseteq> S" "NST O S \<subseteq> S" "S O NST \<subseteq> S" 
    "refl NS" "refl NST" 
    "trans S" "trans NS" "trans NST" 
    "af_compatible ?pi' NS" 
    and ws': "not_subterm_rel_info NS (rel_impl.not_wst rp)" 
    and cmono: "\<And> sig. ?mono sig \<Longrightarrow> ctxt.closed S" 
    and subst_s: "isOK (rel_impl.subst_s rp) \<Longrightarrow> subst.closed S" 
    and SN: "isOK(rel_impl.SN rp) \<Longrightarrow> SN S" 
    and ce: "isOK(rel_impl.ce_compat rp) \<Longrightarrow> ce_compatible NS" 
    and ceS: "\<And> sig. ?mono sig \<Longrightarrow> isOK(rel_impl.ce_compat rp) \<Longrightarrow> ce_compatible S"
    and co: "isOK (rel_impl.co_rewr rp) \<Longrightarrow> NS \<inter> S\<inverse> = {}" 
    by (auto simp: rel_impl_def)
  let ?aS = "afs_rel ?pi S"
  let ?aNS = "afs_rel ?pi NS"
  let ?aNST = "afs_rel ?pi NST"
  note defs = filtered_rel_impl_def Let_def rel_impl.simps
  show ?case
  proof (rule exI[of _ ?aS], rule exI[of _ ?aNS], rule exI[of _ ?aNST], intro conjI impI allI)
    from trans_ctxt_imp_all_ctxt_closed[OF \<open>trans NS\<close> \<open>refl NS\<close> *(3)]
    have all: "all_ctxt_closed UNIV NS" .
    {
      fix st
      assume stU: "st \<in> set U" 
      obtain s t where st: "st = (s,t)" by force
      show "isOK(rel_impl.s ?rp st) \<Longrightarrow> st \<in> ?aS" 
        unfolding afs_rel_def afs_rule_def defs using st stU
        by (auto intro!: orient simp: afs_check_def)
      show "isOK(rel_impl.ns ?rp st) \<Longrightarrow> st \<in> ?aNS" 
        unfolding afs_rel_def afs_rule_def defs using st stU
        by (auto intro!: orient simp: afs_check_def)
      show "isOK(rel_impl.nst ?rp st) \<Longrightarrow> st \<in> ?aNST" 
        unfolding afs_rel_def afs_rule_def defs using st stU
        by (auto intro!: orient simp: afs_check_def)
    }
    show "?aS \<subseteq> ?aNS" using \<open>S \<subseteq> NS\<close> unfolding afs_rel_def by auto
    show "subst.closed ?aNS" using \<open>subst.closed NS\<close> by (rule afs_subst_closed)
    show "subst.closed ?aNST" using \<open>subst.closed NST\<close> by (rule afs_subst_closed)
    show "ctxt.closed ?aNS" by (intro afs_NS_mono[OF all])
    show "?aS O ?aNS \<subseteq> ?aS" using afs_compat2[OF \<open>S O NS \<subseteq> S\<close>] .
    show "?aNS O ?aS \<subseteq> ?aS" using afs_compat[OF \<open>NS O S \<subseteq> S\<close>] .
    show "?aNST O ?aS \<subseteq> ?aS" using afs_compat[OF \<open>NST O S \<subseteq> S\<close>] .
    show "?aS O ?aNST \<subseteq> ?aS" using afs_compat2[OF \<open>S O NST \<subseteq> S\<close>] .
    show "trans ?aS" using afs_trans[OF \<open>trans S\<close>] .
    show "trans ?aS" by fact
    show "trans ?aNS" using afs_trans[OF \<open>trans NS\<close>] .
    show "trans ?aNST" using afs_trans[OF \<open>trans NST\<close>] .
    show "irrefl ?aS" using \<open>irrefl S\<close> unfolding afs_rel_def irrefl_on_def afs_rule_def by simp
    show "refl ?aNS" using \<open>refl NS\<close> by (rule afs_refl)
    show "refl ?aNST" using \<open>refl NST\<close> by (rule afs_refl)
    show "af_compatible ?pi'' ?aNS" 
      unfolding defs by (intro af_compatible[OF \<open>refl NS\<close> all])
    {
      assume "isOK (rel_impl.ce_compat ?rp)" 
      hence "isOK (rel_impl.ce_compat rp)" unfolding defs .
      from ce[OF this] have "ce_compatible NS" .
      thus "ce_compatible ?aNS" 
        using af_ce_compat fin by blast
    }
    {
      assume "isOK (rel_impl.co_rewr ?rp)" 
      hence "isOK (rel_impl.co_rewr rp)" unfolding defs .
      from co[OF this] have "NS \<inter> S\<inverse> = {}" .
      thus "?aNS \<inter> ?aS\<inverse> = {}"
        unfolding afs_rel_def afs_rule_def by fastforce
    }
    show "isOK (rel_impl.subst_s ?rp) \<Longrightarrow> subst.closed ?aS" 
      by (intro afs_subst_closed subst_s, unfold defs)
    show "isOK (rel_impl.SN ?rp) \<Longrightarrow> SN ?aS" 
      by (intro afs_SN SN, unfold defs)
    {
      have afs_rule: "afs_rule ?pi = (\<lambda> (s,t). (afs_term ?pi s, afs_term ?pi t))" 
        by (intro ext, auto simp: afs_rule_def)
      fix sig
      assume sub: "funas_trs (set U) \<subseteq> set sig" 
      assume "isOK(rel_impl.mono ?rp sig)" 
      from this[unfolded defs check_mono_afs_def, simplified, unfolded afs_rule]
      have mono1: "mono_afs ?pi" and mono2: "isOK (rel_impl.mono rp (afs_sig ?pi sig))" by auto
      from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans: "trans S" unfolding trans_def by blast
      have afs_rules: "afs_rules ?pi R = map (\<lambda> (l,r). (afs_term ?pi l, afs_term ?pi r)) R" for R :: "('f,'v)rule list"
        by (auto simp: afs_rules_def afs_rule_def)
      have funas: "funas_trs (set ?U) \<subseteq> set (afs_sig ?pi sig)" 
        by (rule subset_trans[OF _ afs_sig_funas_trs_list[OF sub]], simp add: afs_rules)
      show "ctxt.closed ?aS" 
        by (rule mono_afs_ctxt_closed[OF mono1 trans cmono[OF conjI[OF funas mono2]]])
      assume \<open>isOK (rel_impl.ce_compat ?rp)\<close>
      hence "isOK (rel_impl.ce_compat rp)" unfolding defs .
      from ceS[OF conjI[OF funas mono2] this]
      have "ce_compatible S" .
      from af_ce_compat[OF fin this] show "ce_compatible ?aS" .
    }
    let ?ws' = "rel_impl.not_wst rp"
    let ?fs' = "\<lambda>fs. map fst pi @ map (\<lambda>(f, y). (fpair_f f, y)) fs"
    show "not_subterm_rel_info ?aNS ?ws" 
      unfolding filtered_rel_impl_def Let_def rel_impl.simps 
    proof (cases "rel_impl.not_wst rp")
      case (Some fs)
      show "not_subterm_rel_info ?aNS (map_option ?fs' ?ws')" unfolding Some option.simps not_subterm_rel_info.simps
      proof (intro allI impI)
        fix fn i
        assume nmem1: "fn \<notin> set (?fs' fs)"
        then have "fn \<notin> fst ` set pi" by auto
        then have nmem: "fn \<notin> afs_syms ?pi" using afs_of_Some_afs_syms[OF \<pi>] unfolding \<pi> by auto
        obtain f n where f: "fn = (f,n)" by force
        from afs_syms[OF nmem[unfolded f]]
        have pi: "afs ?pi (f,n) = default_af_entry n" .
        show "simple_arg_pos ?aNS fn i" unfolding f
        proof (rule simple_arg_posI)
          fix ts :: "('f,'v)term list"
          assume n: "length ts = n" and i: "i < n"
          then show "(Fun f ts, ts ! i) \<in> ?aNS" unfolding afs_rel_def afs_rule_def
          proof (simp del: afs_term.simps add: default_af_entry_id[of ?pi, OF pi[folded n]])
            from nmem1 have "(FPair f n, length ts) \<notin> set fs" unfolding f n
              by force
            from ws'[unfolded Some, simplified, rule_format, OF this]
            have "simple_arg_pos NS (FPair f n, length ts) i" .
            from this[unfolded simple_arg_pos_def, rule_format, of "map (afs_term ?pi) ts"]
            show "(Fun (FPair f n) (map (afs_term ?pi) ts), afs_term ?pi (ts ! i)) \<in> NS"
              using n[symmetric] i by auto
          qed
        qed
      qed
    qed simp    
  qed (auto simp: filtered_rel_impl_def Let_def empty_af no_complexity_check_def full_af)
qed


definition
  filtered_rel_impl_af :: "'f afs_list \<Rightarrow> ('f, 'v) rel_impl \<Rightarrow> ('f :: {showl, compare_order}, 'v :: showl) rel_impl"
where
  "filtered_rel_impl_af pi rp = (
    let afso = afs_of pi; afs = the afso; af = afs_with_af afs (rel_impl.af rp) in \<lparr>
      rel_impl.valid = do {
        check (afso \<noteq> None) (showsl (STR ''invalid positions in argument filter''));
        rel_impl.valid rp;
        rel_impl.top_refl rp;
        rel_impl.standard rp \<comment> \<open>might be generalized\<close>
      }, 
      standard = succeed,
      desc = showsl (STR ''Argument Filter:\<newline>'') \<circ> showsl_afs pi \<circ> showsl_nl \<circ> rel_impl.desc rp,
      s = af_check (showsl (STR ''>'')) afs (rel_impl.s rp),
      ns = af_check (showsl (STR ''>='')) afs (rel_impl.ns rp),
      nst = af_check (showsl (STR ''>='')) afs (rel_impl.nst rp),
      af = af,
      top_af = full_af, \<comment> \<open>might be generalized\<close>
      SN = rel_impl.SN rp,
      subst_s = rel_impl.subst_s rp,
      ce_compat = rel_impl.ce_compat rp,
      co_rewr = rel_impl.co_rewr rp,
      top_mono = error (showsl_lit (STR ''top-mono with argument filter not yet supported'')),
      top_refl = succeed,
      mono_af = empty_af, \<comment> \<open>TODO: this is a crude underapproximation\<close>
      mono = \<lambda> sig. do {check_mono_afs afs; rel_impl.mono rp (af_sig afs sig)},
      not_wst = map_option (\<lambda> fs. map fst pi @ fs) (rel_impl.not_wst rp),
      not_sst = None, \<comment> \<open>TODO: strict subterm currently not supported\<close>
      cpx = no_complexity_check
    \<rparr>)"

lemma filtered_rel_impl_af: 
  fixes pi :: "('f :: {showl,compare_order}) afs_list" and
        rp :: "('f, 'v :: showl)rel_impl"
  assumes rp: "rel_impl rp" 
  shows "rel_impl (filtered_rel_impl_af pi rp)"
  unfolding rel_impl_def
proof (intro allI impI, goal_cases)
  case (1 U)
  let ?rp = "filtered_rel_impl_af pi rp :: ('f, 'v)rel_impl"
  let ?pi = "the (afs_of pi)"
  let ?pi' = "rel_impl.af rp" 
  let ?p = "afs_with_af ?pi ?pi'"
  let ?pi'' = "rel_impl.af ?rp"
  let ?mpi'' = "rel_impl.mono_af ?rp"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
  let ?ws = "rel_impl.not_wst ?rp"
  let ?sst = "rel_impl.not_sst ?rp"
  have cpx: "?cpx = no_complexity_check" unfolding filtered_rel_impl_af_def Let_def by simp
  have pi'': "?pi'' = ?p" unfolding filtered_rel_impl_af_def Let_def by simp
  have mpi'': "?mpi'' = empty_af" unfolding filtered_rel_impl_af_def Let_def by simp
  let ?af_term = "af_term ?pi"
  let ?af_list = "map (\<lambda> (s,t). (?af_term s, ?af_term t))"
  let ?U = "?af_list U" 
  let ?mono = "\<lambda> sig. funas_trs (set ?U) \<subseteq> set sig \<and> isOK(rel_impl.mono rp sig)" 
  from 1(1) have valid: "isOK(rel_impl.valid rp)" 
    and std: "isOK(rel_impl.standard rp)" and wf_afs: "afs_of pi \<noteq> None" 
    and trefl: "isOK(rel_impl.top_refl rp)"
    unfolding filtered_rel_impl_af_def by (auto simp: Let_def)
  then obtain \<pi> where \<pi>: "afs_of pi = Some \<pi>" by (cases, auto)
  from afs_of_Some_afs_syms[OF \<pi>] have fin: "finite (afs_syms ?pi)" unfolding \<pi> by auto
  from rp[unfolded rel_impl_def, rule_format, OF valid, of ?U]
  obtain S NS NST where rel_impl: "rel_impl_prop rp ?U S NS NST" by presburger
  from rel_impl have orient: 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.s rp st) \<Longrightarrow> st \<in> S" 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.ns rp st) \<Longrightarrow> st \<in> NS" 
    "\<And> st. st \<in> set ?U \<Longrightarrow> isOK(rel_impl.nst rp st) \<Longrightarrow> st \<in> NST" 
    by presburger+
  from rel_impl std trefl have *:
    "S \<subseteq> NS" 
    "irrefl S" 
    "ctxt.closed NS"
    "subst.closed NS" "subst.closed NST"
    "S O NS \<subseteq> S"
    "NS O S \<subseteq> S" "NST O S \<subseteq> S"  "S O NST \<subseteq> S"
    "refl NS" "refl NST" 
    "trans S" "trans NS" "trans NST" 
    and af: "af_compatible ?pi' NS" 
    and ws': "not_subterm_rel_info NS (rel_impl.not_wst rp)" 
    and cmono: "\<And> sig. ?mono sig \<Longrightarrow> ctxt.closed S" 
    and subst_s: "isOK (rel_impl.subst_s rp) \<Longrightarrow> subst.closed S" 
    and SN: "isOK(rel_impl.SN rp) \<Longrightarrow> SN S" 
    and ce: "isOK(rel_impl.ce_compat rp) \<Longrightarrow> ce_compatible NS" 
    and ceS: "\<And> sig. ?mono sig \<Longrightarrow> isOK(rel_impl.ce_compat rp) \<Longrightarrow> ce_compatible S"
    and co: "isOK (rel_impl.co_rewr rp) \<Longrightarrow> NS \<inter> S\<inverse> = {}" 
    by (auto simp: rel_impl_def)
  let ?aS = "af_rel ?pi S"
  let ?aNS = "af_rel ?pi NS"
  let ?aNST = "af_rel ?pi NST"
  note defs = filtered_rel_impl_af_def Let_def rel_impl.simps
  show ?case
  proof (rule exI[of _ ?aS], rule exI[of _ ?aNS], rule exI[of _ ?aNST], intro conjI orient impI allI)
    from trans_ctxt_imp_all_ctxt_closed[OF \<open>trans NS\<close> \<open>refl NS\<close> *(3)]
    have all: "all_ctxt_closed UNIV NS" .
    {
      fix st
      assume stU: "st \<in> set U" 
      obtain s t where st: "st = (s,t)" by force
      show "isOK(rel_impl.s ?rp st) \<Longrightarrow> st \<in> ?aS" 
        unfolding af_rel_def af_rule_alt_def defs using st stU
        by (auto intro!: orient simp: af_check_def)
      show "isOK(rel_impl.ns ?rp st) \<Longrightarrow> st \<in> ?aNS" 
        unfolding af_rel_def af_rule_alt_def defs using st stU
        by (auto intro!: orient simp: af_check_def)
      show "isOK(rel_impl.nst ?rp st) \<Longrightarrow> st \<in> ?aNST" 
        unfolding af_rel_def af_rule_alt_def defs using st stU
        by (auto intro!: orient simp: af_check_def)
    }
    show "?aS \<subseteq> ?aNS" using \<open>S \<subseteq> NS\<close> unfolding af_rel_def by auto
    show "subst.closed ?aNS" using \<open>subst.closed NS\<close> by (rule af_subst_closed)
    show "subst.closed ?aNST" using \<open>subst.closed NST\<close> by (rule af_subst_closed)
    show "ctxt.closed ?aNS" by (intro af_NS_mono[OF all])
    show "?aS O ?aNS \<subseteq> ?aS" using af_compat2[OF \<open>S O NS \<subseteq> S\<close>] .
    show "?aNS O ?aS \<subseteq> ?aS" using af_compat[OF \<open>NS O S \<subseteq> S\<close>] .
    show "?aNST O ?aS \<subseteq> ?aS" using af_compat[OF \<open>NST O S \<subseteq> S\<close>] .
    show "?aS O ?aNST \<subseteq> ?aS" using af_compat2[OF \<open>S O NST \<subseteq> S\<close>] .
    show "trans ?aS" using af_trans[OF \<open>trans S\<close>] .
    show "trans ?aS" by fact
    show "trans ?aNS" using af_trans[OF \<open>trans NS\<close>] .
    show "trans ?aNST" using af_trans[OF \<open>trans NST\<close>] .
    show "irrefl ?aS" using \<open>irrefl S\<close> unfolding af_rel_def irrefl_on_def af_rule_alt_def by simp
    show "refl ?aNS" using \<open>refl NS\<close> by (rule af_refl)
    show "refl ?aNST" using \<open>refl NST\<close> by (rule af_refl)
    show "af_compatible ?pi'' ?aNS" 
      unfolding defs
      by (intro af_compatible_afs_with_af[OF \<open>refl NS\<close> af all])
    {
      assume "isOK (rel_impl.ce_compat ?rp)" 
      hence "isOK (rel_impl.ce_compat rp)" unfolding defs .
      from ce[OF this] have "ce_compatible NS" .
      thus "ce_compatible ?aNS" 
        using af_ce_compat_af_rel fin by blast
    }
    {
      assume "isOK (rel_impl.co_rewr ?rp)" 
      hence "isOK (rel_impl.co_rewr rp)" unfolding defs .
      from co[OF this] have "NS \<inter> S\<inverse> = {}" .
      thus "?aNS \<inter> ?aS\<inverse> = {}"
        unfolding af_rel_def af_rule_alt_def by fastforce
    }
    show "isOK (rel_impl.subst_s ?rp) \<Longrightarrow> subst.closed ?aS" 
      by (intro af_subst_closed subst_s, unfold defs)
    show "isOK (rel_impl.SN ?rp) \<Longrightarrow> SN ?aS" 
      by (intro af_SN SN, unfold defs)
    have afs: "af_rule ?pi = (\<lambda> (l,r). (af_term ?pi l, af_term ?pi r))"
      by (rule ext, unfold af_rule_alt_def, force)
    {
      have af_rule: "af_rule ?pi = (\<lambda> (s,t). (af_term ?pi s, af_term ?pi t))" 
        by (intro ext, auto simp: af_rule_alt_def)
      fix sig
      assume sub: "funas_trs (set U) \<subseteq> set sig" 
      assume "isOK(rel_impl.mono ?rp sig)" 
      from this[unfolded defs check_mono_afs_def, simplified, unfolded af_rule]
      have mono1: "mono_afs ?pi" and mono2: "isOK (rel_impl.mono rp (af_sig ?pi sig))" by auto
      from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans: "trans S" unfolding trans_def by blast
      have af_rules: "af_rules ?pi R = map (\<lambda> (l,r). (af_term ?pi l, af_term ?pi r)) R" for R :: "('f,'v)rule list"
        by (auto simp: af_rules_def af_rule_alt_def)
      have funas: "funas_trs (set ?U) \<subseteq> set (af_sig ?pi sig)" 
        by (rule subset_trans[OF _ af_sig_funas_trs_list[OF sub]], simp add: af_rules)
      show "ctxt.closed ?aS" 
        by (rule mono_afs_af_rel_ctxt_closed[OF mono1 trans cmono[OF conjI[OF funas mono2]]])
      assume \<open>isOK (rel_impl.ce_compat ?rp)\<close>
      hence "isOK (rel_impl.ce_compat rp)" unfolding defs .
      from ceS[OF conjI[OF funas mono2] this]
      have "ce_compatible S" .
      from af_ce_compat_af_rel[OF fin this] show "ce_compatible ?aS" .
    }
    let ?ws' = "rel_impl.not_wst rp"
    let ?fs' = "\<lambda>fs. map fst pi @ fs"
    show "not_subterm_rel_info ?aNS ?ws" 
      unfolding defs 
    proof (cases "rel_impl.not_wst rp")
      case (Some fs)
      show "not_subterm_rel_info ?aNS (map_option ?fs' ?ws')" unfolding Some option.simps not_subterm_rel_info.simps
      proof (intro allI impI)
        fix fn i
        assume nmem1: "fn \<notin> set (?fs' fs)"
        then have "fn \<notin> fst ` set pi" by auto
        then have nmem: "fn \<notin> afs_syms ?pi" using afs_of_Some_afs_syms[OF \<pi>] unfolding \<pi> by auto
        obtain f n where f: "fn = (f,n)" by force
        from afs_syms[OF nmem[unfolded f]]
        have pi: "afs ?pi (f,n) = default_af_entry n" .
        show "simple_arg_pos ?aNS fn i" unfolding f
        proof (rule simple_arg_posI)
          fix ts :: "('f,'v)term list"
          assume n: "length ts = n" and i: "i < n"
          then show "(Fun f ts, ts ! i) \<in> ?aNS" unfolding af_rel_def af_rule_alt_def
          proof (simp del: af_term.simps add: default_af_entry_id_af[of ?pi, OF pi[folded n]])
            from nmem1 have "(f, length ts) \<notin> set fs" unfolding f n
              by force
            from ws'[unfolded Some, simplified, rule_format, OF this]
            have "simple_arg_pos NS (f, length ts) i" .
            from this[unfolded simple_arg_pos_def, rule_format, of "map (af_term ?pi) ts"]
            show "(Fun f (map (af_term ?pi) ts), af_term ?pi (ts ! i)) \<in> NS"
              using n[symmetric] i by auto
          qed
        qed
      qed
    qed simp
  qed (auto simp: filtered_rel_impl_af_def Let_def empty_af no_complexity_check_def full_af)
qed

end
