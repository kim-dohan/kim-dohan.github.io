(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Matchbounds
imports
  First_Order_Rewriting.Multihole_Context
  First_Order_Rewriting.Trs_Impl
  Ord.RPO_More
  Auxx.Multiset2
begin

hide_const Error_Monad.mapM

fun base :: "'f \<times> nat \<Rightarrow> 'f" where "base (f,h) = f"
fun height :: "'f \<times> nat \<Rightarrow> nat" where "height (f,h) = h"
fun lift :: "nat \<Rightarrow> 'f \<Rightarrow> 'f \<times> nat" where "lift h f = (f,h)"
abbreviation "base_term \<equiv> map_funs_term base"
abbreviation "lift_term h \<equiv> map_funs_term (lift h)"

lemma base_lift: "base_term (lift_term h s) = s"
  by (simp only: map_funs_term_comp o_def, simp add: map_funs_term_ident[unfolded id_def])

fun sym_collect :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term \<Rightarrow> 'f list"
where "sym_collect p (Var x) = []"
  |   "sym_collect p (Fun f ts) = (if p (Fun f ts) then [f] else []) @ 
  concat (map (sym_collect p) ts)"

(* distinguish between different kinds of match-relations *)
datatype relation_kind = 
  Strict_TRS (* match *)
| Weak_TRS "nat option" (* match-RT as in Korp Zankl RTA 2010 paper or match-RT_c as in their LMsubst_closure 2014 paper *) 

fun
  compute_height ::
    "relation_kind \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f \<times> nat, 'v) term \<Rightarrow> nat \<Rightarrow> nat"
where
  "\<And>br. compute_height Strict_TRS bl br l x = Suc x"
| "\<And>br. compute_height (Weak_TRS (Some c)) bl br l x =
    (if lift_term x bl = l \<and> size (funs_term_ms bl) \<ge> size (funs_term_ms br)
    then min c x else min c (Suc x))"
| "\<And>br. compute_height (Weak_TRS None) bl br l x =
    (if lift_term x bl = l \<and> size (funs_term_ms bl) \<ge> size (funs_term_ms br)
    then x else Suc x)"

definition cover :: "(('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> relation_kind \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f \<times> nat,'v)trs"
  where "cover ff rel R \<equiv> { (l', lift_term h r) | l r l' h. 
       (l,r) \<in> R 
     \<and> base_term l' = l 
     \<and> h = compute_height rel l r l' (min_list (map height (sym_collect (\<lambda> t'. ff (l,r) (base_term t')) l')))}"

lemma cover_empty[simp]: "cover x y {} = {}" unfolding cover_def by auto

lemma cover_left_linear: assumes "left_linear_trs R"
  shows "left_linear_trs (cover ff rel R)"
  using assms
  unfolding left_linear_trs_def cover_def
  by (clarify, insert linear_map_funs_term[of base], auto)

lemma cover_var_condition: assumes "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and "(l,r) \<in> cover ff rel R"
  shows "vars_term r \<subseteq> vars_term l"
  using assms vars_term_map_funs_term2[of base]
  unfolding cover_def
  by force

fun roof :: "('f,'v)rule \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
  where [code del]: "roof (l,r) = (\<lambda> t. vars_term r \<subseteq> vars_term t)"


lemma height_lift: assumes "(f,n) \<in> funas_term (lift_term h t)"
  shows "height f = h"
using assms
by (induct t, auto)

definition raise :: "('f \<times> nat,'v) trs" where
  "raise \<equiv> {(Fun (f,n) ts, Fun (f, Suc n) ts) | f n ts. True}"

lemma roof_raise_locally_SN: assumes wf_trs: "wf_trs R" shows "locally_terminating (cover roof Strict_TRS (R :: ('f,'v)trs) \<union> raise)"
  unfolding locally_terminating_def
proof (intro allI impI)
  fix F :: "('f \<times> nat)sig"
  assume "finite F"
  from finite_list[OF this] obtain Fs where F: "F = set Fs" by auto
  let ?hs = "map (\<lambda>(f,n). height f) Fs"
  obtain m where m: "m = Suc (max_list ?hs)" by auto
  have small: "\<And> f n. (f,n) \<in> F \<Longrightarrow> height f < m" unfolding F m using max_list[of _ ?hs] by force
  let ?S = "sig_step F (rstep (cover roof Strict_TRS R \<union> raise))"
  let ?R = "sig_step F (cover roof Strict_TRS R \<union> raise)"
  have subset: "?S \<subseteq> rstep ?R" 
  proof 
    fix s t
    assume "(s,t) \<in> ?S"
    from sig_stepE[OF this] have sF: "funas_term s \<subseteq> F" and tF: "funas_term t \<subseteq> F" and step: "(s,t) \<in> rstep (cover roof Strict_TRS R \<union> raise)" by auto
    from step obtain C l r \<sigma> where lr: "(l,r) \<in> cover roof Strict_TRS R \<union> raise" 
      and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
    from sF tF have F: "funas_term l \<subseteq> F" "funas_term r \<subseteq> F" unfolding s t 
      by (auto simp: funas_term_subst)
    from sig_stepI[OF lr this]
    show "(s,t) \<in> rstep ?R" unfolding s t by auto
  qed
  let ?prc = "\<lambda> (f :: 'f \<times> nat,n) (g,k). (height f < height g \<and> height g \<le> m, height f < height g \<and> height g \<le> m \<or> f = g \<and> n = k)"
  let ?prl = "\<lambda> _. False"
  interpret rpo_with_assms ?prc ?prl _ 0
  proof(unfold_locales, force)
    have id: " {(f, g). fst (?prc f g)} = {((f,n), (g,k)) | f n g k. height f < height g \<and> height g \<le> m}"  by auto
    show "SN {(f, g). fst (?prc f g)}" unfolding id
      by (rule SN_subset[OF SN_inv_image[of _ "\<lambda>(f,n). height f", unfolded inv_image_def, OF SN_nat_bounded[of m]]], auto)
  qed auto
  show "SN ?S"
  proof (rule SN_subset[OF _ subset], rule rpo_manna_ness, unfold sig_step_def, clarify)
    fix l r
    assume lr: "(l,r) \<in> cover roof Strict_TRS R \<union> raise"
    and wfl: "funas_term l \<subseteq> F" and wfr: "funas_term r \<subseteq> F"
    {
      assume lr: "(l,r) \<in> cover roof Strict_TRS R"
      from lr[unfolded cover_def]
      obtain ll rr h where base: "base_term l = ll" and llrr: "(ll,rr) \<in> R" and
        r: "r = lift_term h rr" and
        h: "h = Suc (min_list (map height (sym_collect (\<lambda> t'. roof (ll,rr) (base_term t')) l)))" by auto
      from wf_trs[unfolded wf_trs_def] llrr obtain ff lls where ll: "ll = Fun ff lls" and vars: "vars_term rr \<subseteq> vars_term ll" 
        by (cases ll, force+)
      from vars r base vars_term_map_funs_term2[of "lift h" rr] vars_term_map_funs_term2[of base l] 
      have vars: "vars_term r \<subseteq> vars_term l" and vars2: "vars_term rr = vars_term r" by auto
      obtain vr where vr: "vars_term r = vr" by auto
      from base ll have "is_Fun l" by (cases l, auto)
      with vars have "\<exists> f' ls'. l \<unrhd> Fun f' ls' \<and> Suc (height f') = h \<and> vars_term r \<subseteq> vars_term (Fun f' ls')" unfolding h roof.simps vars2[symmetric] vars_term_map_funs_term2 unfolding vars2 vr nat.inject
      proof (induct l)
        case (Var x) then show ?case by simp
      next
        case (Fun f ls) 
        let ?fs = "\<lambda> s. sym_collect (\<lambda> t'. vr \<subseteq> vars_term t') s"
        let ?hs = "\<lambda> s. map height (?fs s)"
        let ?h = "\<lambda> s. min_list (?hs s)"
        show ?case 
        proof (cases "height f = ?h (Fun f ls)")
          case True
          show ?thesis unfolding True[symmetric]
            by (intro exI conjI, rule supteq.refl, rule, rule Fun(2))
        next
          case False        
          let ?fls = "concat (map ?fs ls)"
          from Fun(2) have id: "?fs (Fun f ls) = f # ?fls" by auto
          then have id: "?hs (Fun f ls) = height f # map height ?fls" by auto
          then have hsnNil: "?hs (Fun f ls) \<noteq> []" by simp
          from min_list_ex[OF hsnNil] obtain h where mem: "h \<in> set (?hs (Fun f ls))"
            and min: "h = min_list (?hs (Fun f ls))" by auto
          from False mem min have "h \<in> set (map height ?fls)" unfolding id by auto
          then obtain l where l: "l \<in> set ls" and h: "h \<in> set (map height (?fs l))"
            by auto
          have subset: "set (map height (?fs l)) \<subseteq> set (?hs (Fun f ls))" using l by auto
          from h have vr: "vr \<subseteq> vars_term l" by (induct l, auto)
          from h have var: "is_Fun l" by (cases l, auto)
          from Fun(1)[OF l vr var] obtain f' ls' where supteq: "l \<unrhd> Fun f' ls'"
            and hf': "height f' = min_list (?hs l)" and vr: "vr \<subseteq> vars_term (Fun f' ls')"
            by auto
          from l supteq have supteq: "Fun f ls \<unrhd> Fun f' ls'" by auto
          show ?thesis 
            by (intro exI conjI, rule supteq, unfold hf' min_list_subset[OF subset h[unfolded min]], insert vr, auto)
        qed        
      qed      
      then obtain f' ls' where sub: "l \<unrhd> Fun f' ls'" and h: "h = Suc (height f')" and vars: "vars_term r \<subseteq> vars_term (Fun f' ls')" by auto
      from wfl sub have "(f',length ls') \<in> F" by auto
      from small[OF this] have f'm: "height f' < m" .
      {
        fix g k
        assume "(g,k) \<in> funas_term r"
        from height_lift[OF this[unfolded r]]
        have "height g = h" by simp        
        with h f'm have "height f' < height g \<and> height g \<le> m" by simp
      } note main = this
      have "rpo_pr (Fun f' ls') r = (True,True)" 
        by (rule rpo_large_sym[OF _ vars], insert main, auto)    
      from supteq_imp_rpo_nstri[OF sub] this
      have "fst (rpo_pr l r)" using rpo_compat by force
    }
    moreover
    {
      assume "(l,r) \<in> raise"
      then obtain f n ts where l: "l = Fun (f,n) ts" and r: "r = Fun (f,Suc n) ts" unfolding raise_def by auto
      {
        fix t
        assume t: "t \<in> set ts"
        then have "Fun (f,n) ts \<rhd> t" by auto
        from supt_imp_rpo_stri[OF this] have "rpo_s (Fun (f,n) ts) t" .
      } note arg = this
      from wfr[unfolded r] have "((f, Suc n),length ts) \<in> F" by auto
      from small[OF this] have "Suc n < m" by auto
      then have "rpo_s l r" unfolding l r rpo.simps Let_def using arg by auto
    }
    ultimately show "rpo_s l r" using lr by blast
  qed  
qed

definition match :: "('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "match \<equiv> \<lambda> _ _. True"


lemma sym_collect_match: "sym_collect (\<lambda> t'. match lr (f t')) t = funs_term_list t" unfolding match_def
proof (induct t)
  case (Var x) show ?case by (simp add: funs_term_list.simps)
next
  case (Fun f ts)
  show ?case 
    by (simp add: funs_term_list.simps, insert Fun, induct ts, auto simp: funs_term_list.simps)
qed
    

context
  fixes R :: "('f,'v)trs"
  assumes wf: "wf_trs R"
  and non_duplicating: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
begin

context
  fixes F :: "('f \<times> nat)sig"
  and m :: nat
  and k :: nat
  assumes small: "\<And> f n. (f,n) \<in> F \<Longrightarrow> height f \<le> m"
  and small2: "\<And> l r. (l,r) \<in> R \<Longrightarrow> length (funas_term_list r) \<le> k"
  and k1: "1 \<le> k"
begin
private abbreviation mm where "mm \<equiv> \<lambda> s. funs_term_ms (map_funs_term (\<lambda> f. m - height f) s)"

lemma mm_lift_term_conv: "mm (lift_term h (s :: ('f,'v)term)) = mset (replicate (size (funs_term_ms s)) (m - h))"
proof (induct s)
  case (Fun f ss)
  have lift: "lift h = (\<lambda>a :: 'f. (a, h))" by (rule ext, simp)
  have "?case \<longleftrightarrow> \<Sum>\<^sub>#
     ((funs_term_ms \<circ>\<circ>\<circ> (\<circ>)) (map_funs_term (\<lambda>f. m - height f)) (map_funs_term (\<lambda>a. (a, h))) `#
      mset ss) =
    replicate_mset (size (\<Sum>\<^sub># (funs_term_ms `# mset ss))) (m - h)" 
    by simp
  also have "\<dots>" using Fun
    by (induct ss, auto simp: lift replicate_add) 
      (metis mset_append mset_replicate replicate_add)
  finally show ?case by simp
qed simp

lemma bound_mset_mm_size: "bound_mset k (mm t) \<le> term_size t * Suc k^m"
proof -
  {
    fix j
    assume "j \<in> set_mset (mm t)"
    then have "j < Suc m"
      by (induct t, auto)
  }
  from bound_mset_linear_in_size[of "mm t" "Suc m" k, OF this] 
  obtain x where "bound_mset k (mm t) = 0 \<or> x < Suc m \<and> bound_mset k (mm t) \<le> size (mm t) * Suc k ^ x" (is "?A \<or> ?B") by auto
  then show ?thesis
  proof
    assume ?A then show ?thesis by simp
  next
    assume ?B
    then have "bound_mset k (mm t) \<le> size (mm t) * Suc k ^ x" by simp
    also have "size (mm t) \<le> term_size t"
    proof (induct t)
      case (Fun f ts)
      then show ?case by (induct ts, force+)
    qed simp
    also have "Suc k ^ x \<le> Suc k ^ m"
      by (rule power_increasing, insert \<open>?B\<close>, auto)
    finally show ?thesis by auto
  qed
qed

definition drop_c where
  "drop_c = filter_mset (\<lambda> x. x \<noteq> (0 :: nat))"

abbreviation mmd where "mmd \<equiv> \<lambda> s. drop_c (funs_term_ms (map_funs_term (\<lambda> f. m - height f) s))"

lemma bound_mset_mmd_size: "bound_mset k (mmd t) \<le> term_size t * Suc k^m"
proof -
  have "bound_mset k (mmd t) \<le> bound_mset k (mm t)"
    by (rule bound_mset_mono, auto simp: drop_c_def)
  also have "\<dots> \<le> term_size t * Suc k^m"
    by (rule bound_mset_mm_size)
  finally show ?thesis .
qed

private fun aux_rel where 
  "aux_rel Strict_TRS RR = {(s,t) . (mm s, mm t) \<in> bmult_less k \<and> (non_collapsing RR \<longrightarrow> (mmd s, mmd t) \<in> bmult_less k)}"
| "aux_rel (Weak_TRS (Some c)) RR = (if c = m then {(s,t) . (mmd s, mmd t) \<in> (bmult_less k)^=} else UNIV)"
| "aux_rel (Weak_TRS None) RR = {(s,t) . (mm s, mm t) \<in> (bmult_less k)^=}"

lemma sig_match_raise_step_imp_aux_rel: assumes "(t,s) \<in> sig_step F (rstep (cover match rel RR \<union> raise))"
  and RR: "RR \<subseteq> R"
  shows "(s,t) \<in> aux_rel rel RR"
proof -
  note bmult_less_def[simp]
  let ?lt = "{(x,y :: nat). x < y}"
  let ?le = "\<lambda> s t. (mm s, mm t) \<in> bounded_mult k ?lt"
  let ?ler = "\<lambda> s t. (mm s, mm t) \<in> (bounded_mult k ?lt)^="
  let ?led = "\<lambda> s t. (mmd s, mmd t) \<in> bounded_mult k ?lt"
  let ?ledr = "\<lambda> s t. (mmd s, mmd t) \<in> (bounded_mult k ?lt)^="
  let ?rel = "\<lambda> s t. (s,t) \<in> aux_rel rel RR"
  from assms
  have ts: "(t,s) \<in> rstep (cover match rel RR \<union> raise)"
    and t: "funas_term t \<subseteq> F"
    and s: "funas_term s \<subseteq> F" by auto      
  then show ?thesis 
  proof (induct)
    case (IH C \<sigma> l r)        
    let ?C = "funs_ctxt_ms (map_funs_ctxt (\<lambda> f. m - height f) C)"
    let ?Cd = "drop_c ?C"
    let ?\<sigma> = "\<lambda> t. \<Sum>\<^sub># (image_mset (\<lambda> x. funs_term_ms ((map_funs_subst (\<lambda>f. m - height f) \<sigma>) x)) (vars_term_ms t))"
    let ?\<sigma>d = "\<lambda> t. drop_c (?\<sigma> t)"
    have id: "\<And> t. mm (C\<langle>t \<cdot> \<sigma>\<rangle>) = ?C + mm t + ?\<sigma> t"
      by (simp  add: funs_term_ms_ctxt_apply funs_term_ms_subst_apply multiset_eq_iff)
    have idd: "\<And> t. mmd (C\<langle>t \<cdot> \<sigma>\<rangle>) = ?Cd + mmd t + ?\<sigma>d t" unfolding id drop_c_def by simp
    from IH(1) show "?rel (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)"        
    proof
      assume lr: "(l,r) \<in> cover match rel RR"
      from lr[unfolded cover_def] RR obtain ll rr h where base: "base_term l = ll" and llrr: "(ll,rr) \<in> R" and
        llrrRR: "(ll,rr) \<in> RR" and
        r: "r = lift_term h rr" and
        h: "h = compute_height rel ll rr l (min_list (map height (sym_collect (\<lambda> t'. match (ll,rr) (base_term t')) l)))" by auto
      have "size (mm r) = length (funas_term_list rr)" unfolding r
      proof (induct rr)
        case (Fun f ss)
        then show ?case by (induct ss, auto simp: funas_term_list.simps)
      qed (simp add: funas_term_list.simps)
      also have "\<dots> \<le> k" by (rule small2[OF llrr])
      finally have k: "size (mm r) \<le> k" .
      let ?h = "min_list (map height (funs_term_list l))"
      from wf[unfolded wf_trs_def] llrr obtain ff lls where ll: "ll = Fun ff lls" by (cases ll, force+)
      define hh where "hh = m - ?h"
      {
        let ?mmm = "\<lambda>ls. mset (map (\<lambda>f. m - height f) ls)"
        let ?fl = "funs_term_list l"
        let ?mm = "min_list (map height ?fl)"
        from base ll have ne: "map height ?fl \<noteq> []" by (cases l, auto simp: funs_term_list.simps)
        from min_list_ex[OF this] obtain f where
          f: "f \<in> set ?fl" and hf: "?mm = height f" by auto
        from f[unfolded set_funs_term_list funs_term_funas_term] 
        obtain n where fn: "(f,n) \<in> funas_term l" by auto
        from IH(2) have l: "funas_term l \<subseteq> F" by (auto simp: funas_term_subst)
        from fn l have "(f,n) \<in> F" by auto
        from small[OF this] have "height f \<le> m" .
        then have m: "?h \<le> m" unfolding hf by auto
        from f[unfolded set_conv_nth] obtain i where i: "i < length ?fl" 
          and f: "?fl ! i = f" by auto
        from id_take_nth_drop[OF i, unfolded f] obtain bef aft 
          where fl: "?fl = bef @ f # aft" by auto        
        have "\<exists> L. mm l = L + {# m - ?h #}" unfolding mset_funs_term_list[symmetric] 
          unfolding hf funs_term_list_map_funs_term
          unfolding fl
          by (rule exI[of _ "?mmm bef + ?mmm aft"], simp add: multiset_eq_iff)
        note this and m
      } note Lm = this
      then obtain L where L: "mm l = L + {# hh #}" unfolding hh_def by auto
      from non_duplicating[OF llrr] have "vars_term_ms (base_term r) \<subseteq># vars_term_ms (base_term l)" unfolding base r by auto 
      then have "vars_term_ms r \<subseteq># vars_term_ms l" by simp
      then obtain M where Mid: "vars_term_ms l = vars_term_ms r + M" 
        by (rule mset_le_addE)
      obtain \<sigma>diff where \<sigma>l: "?\<sigma> l = ?\<sigma> r + \<sigma>diff" unfolding Mid
        by auto
      have \<sigma>dl: "?\<sigma>d l = ?\<sigma>d r + drop_c \<sigma>diff" unfolding \<sigma>l by (simp add: drop_c_def)
      from h[unfolded sym_collect_match]
      have hS: "h = compute_height rel ll rr l ?h" by simp
      have mml: "mm (C\<langle>l \<cdot> \<sigma>\<rangle>) = (?C + ?\<sigma> r) + (L + {#hh#} + \<sigma>diff)"
        unfolding id L \<sigma>l multiset_eq_iff by auto
      have mmr: "mm (C\<langle>r \<cdot> \<sigma>\<rangle>) = (?C + ?\<sigma> r) + mm r"
        unfolding id multiset_eq_iff by auto
      have mmdl': "mmd (C\<langle>l \<cdot> \<sigma>\<rangle>) = (?Cd + ?\<sigma>d r) + (mmd l + drop_c \<sigma>diff)"
        unfolding idd \<sigma>l multiset_eq_iff by (auto simp: drop_c_def)
      have mmdl: "mmd (C\<langle>l \<cdot> \<sigma>\<rangle>) = (?Cd + ?\<sigma>d r) + (drop_c L + drop_c {#hh#} + drop_c \<sigma>diff)"
        unfolding idd L \<sigma>l multiset_eq_iff by (auto simp: drop_c_def)
      have mmdr: "mmd (C\<langle>r \<cdot> \<sigma>\<rangle>) = (?Cd + ?\<sigma>d r) + mmd r"
        unfolding idd multiset_eq_iff by auto
      have "size (mmd r) \<le> size (mm r)" unfolding drop_c_def by (rule size_filter_mset_lesseq)
      with k have kd: "size (mmd r) \<le> k" by simp
      {
        assume hS: "h = Suc ?h"
        {
          fix h'
          assume h': "h' \<in># mm r" 
          from this[unfolded mset_funs_term_list[symmetric]]
          have "h' \<in> (\<lambda>f. m - height f) ` (funs_term r)" 
            unfolding funs_term_list_map_funs_term in_multiset_in_set using set_funs_term_list by auto
          from this[unfolded funs_term_funas_term]  
          obtain f n where f: "(f,n) \<in> funas_term r" and h': "h' = m - height f"
            by auto
          from IH(3) f have "(f,n) \<in> F" by (auto simp: funas_term_subst)
          from small[OF this] height_lift[OF f[unfolded r]] h' hS have "h' < hh" unfolding hh_def by auto
        }
        then have h: "\<forall>h'. h' \<in># mm r \<longrightarrow> h' < hh" by auto
        {
          assume "non_collapsing RR"
          with llrrRR have "is_Fun rr" unfolding non_collapsing_def by auto
        } note nc = this
        {
          assume "is_Fun rr"
          then have "\<exists> h'. h' \<in># mm r" unfolding r by (cases rr, auto)
          with h have "hh \<noteq> 0" by (cases hh, auto)
        } note r_Fun = this
        {
          assume "hh \<noteq> 0"
          with mmdl have mmdl: "mmd (C\<langle>l \<cdot> \<sigma>\<rangle>) = (?Cd + ?\<sigma>d r) + (drop_c L + {#hh#} + drop_c \<sigma>diff)"
            unfolding mmdl by (simp add: drop_c_def)
          from h have h: "\<forall>h'. h' \<in># mmd r \<longrightarrow> h' < hh" by (auto simp: drop_c_def)
          have "?led (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)"
            unfolding mmdl mmdr
            by (rule bounded_mult, insert kd h, auto)
        } note led = this
        {
          assume "hh = 0"
          with mmdl have mmdl: "mmd (C\<langle>l \<cdot> \<sigma>\<rangle>) = (?Cd + ?\<sigma>d r) + (drop_c L + drop_c \<sigma>diff)"
            unfolding mmdl by (simp add: drop_c_def)
          from \<open>hh = 0\<close> r_Fun obtain x where rr: "rr = Var x" by (cases rr, auto)
          with r have r: "r = Var x" by simp
          have "mmd (C\<langle>r \<cdot> \<sigma>\<rangle>) = ?Cd + ?\<sigma>d r" unfolding mmdr unfolding r by (simp add: drop_c_def)
          with mmdl have "mmd (C\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq># mmd (C\<langle>l \<cdot> \<sigma>\<rangle>)" by simp
        } note subset = this
        from subset_imp_bounded_mult_refl[OF subset, of k ?lt] led
        have ledr: "?ledr (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)" by auto
        have le: "?le (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)"        
          unfolding mml mmr
          by (rule bounded_mult, insert k h, auto)
        then have ler: "?ler (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)" by auto
        note le led[OF r_Fun[OF nc]] ledr ler
      } note Suc = this
      {
        assume "h = Suc ?h"
        note solved = Suc[OF this] 
        then have ?case 
        proof (cases rel)
          case (Weak_TRS c_opt)
          with solved show ?thesis by (cases c_opt, auto)
        qed auto
      } note Suc_case = this
      show ?case
      proof (cases "h = Suc ?h")
        case False note oFalse = this
        with hS obtain c_opt where rel: "rel = Weak_TRS c_opt" by (cases rel, auto)
        show ?thesis
        proof (cases c_opt)
          case (Some c)
          note rel = rel[unfolded Some]
          show ?thesis
          proof (cases "c = m")
            case True
            note rel = rel[unfolded True]
            note hS = hS[unfolded rel]
            have "?ledr (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)"
            proof (rule subset_imp_bounded_mult_refl, cases "h = m")
              case True
              {
                fix h'
                assume "h' \<in># mm r"
                from this[unfolded mset_funs_term_list[symmetric]]
                have "h' \<in> (\<lambda>f. m - height f) ` (funs_term r)" 
                  unfolding funs_term_list_map_funs_term in_multiset_in_set using set_funs_term_list by auto
                from this[unfolded funs_term_funas_term]  
                obtain f n where f: "(f,n) \<in> funas_term r" and h': "h' = m - height f"
                  by auto
                from height_lift[OF f[unfolded r]] h' True have "h' = 0" by simp
              }
              then have r: "mmd r = {#}" unfolding drop_c_def 
                by (intro multiset_eqI, auto, insert neq0_conv, fastforce)
              show "mmd C\<langle>r \<cdot> \<sigma>\<rangle> \<subseteq># mmd C\<langle>l \<cdot> \<sigma>\<rangle>" unfolding mmdl mmdr 
                unfolding r by auto
            next
              case False
              from hS[simplified] False oFalse have lh: "lift_term ?h ll = l" and subset: "size (funs_term_ms rr) \<le> size (funs_term_ms ll)" and h: "h = ?h" 
                by (auto split: if_splits)
              from lh h have lh: "l = lift_term h ll" by simp
              define cr where "cr = size (funs_term_ms rr)"
              define cl where "cl = size (funs_term_ms ll)"
              define cd where "cd = cl - cr"
              from subset have id: "size (funs_term_ms ll) = cr + cd" unfolding cr_def cl_def cd_def by simp
              have "mmd r \<subseteq># mmd l" unfolding drop_c_def
              proof (rule multiset_filter_mono)
                show "mm r \<subseteq># mm l" 
                  unfolding lh r 
                  unfolding mm_lift_term_conv 
                  unfolding id cr_def[symmetric]
                  by (induct cd, auto) (metis add_mset_add_single mset_le_incr_right1)
              qed
              also have "mmd l \<subseteq># mmd l + drop_c \<sigma>diff" by simp
              finally
              show "mmd C\<langle>r \<cdot> \<sigma>\<rangle> \<subseteq># mmd C\<langle>l \<cdot> \<sigma>\<rangle>"
                unfolding mmdl' mmdr by simp
            qed
            then show ?thesis unfolding rel by simp
          qed (insert rel, simp)
        next
          case None
          note rel = rel[unfolded this]
          note hS = hS[unfolded rel]
          from hS[simplified] oFalse have lh: "lift_term ?h ll = l" and subset: "size (funs_term_ms rr) \<le> size (funs_term_ms ll)" and h: "h = ?h" 
            by (auto split: if_splits)
          from lh h have lh: "l = lift_term h ll" by simp
          define cr where "cr = size (funs_term_ms rr)"
          define cl where "cl = size (funs_term_ms ll)"
          define cd where "cd = cl - cr"
          from subset have id: "size (funs_term_ms ll) = cr + cd" unfolding cr_def cl_def cd_def by simp
          have "mm r \<subseteq># mm l"  
            unfolding lh r 
            unfolding mm_lift_term_conv 
            unfolding id cr_def[symmetric]
            by (induct cd, auto) (metis add_mset_add_single mset_le_incr_right1)
          also have "mm l \<subseteq># mm l + \<sigma>diff" by simp
          finally
          have "mm C\<langle>r \<cdot> \<sigma>\<rangle> \<subseteq># mm C\<langle>l \<cdot> \<sigma>\<rangle>"
            unfolding mml mmr L by simp
          then have "?ler (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)"
            by (rule subset_imp_bounded_mult_refl)
          then show ?thesis unfolding rel by simp
        qed
      qed (insert Suc_case, simp)
    next
      assume lr: "(l,r) \<in> raise"
      then obtain f n ts where l: "l = Fun (f,n) ts" and r: "r = Fun (f,Suc n) ts" unfolding raise_def by auto
      from IH(3)[unfolded r] have "((f, Suc n), length ts) \<in> F" by auto
      from small[OF this] have "Suc n \<le> m" by auto
      then have small: "m - Suc n < m - n" by auto
      have "\<exists> L. mm (l \<cdot> \<sigma>) = L + {# m - n #} \<and> mm (r \<cdot> \<sigma>) = L + {# m - Suc n #}"
        unfolding l r eval_term.simps
        unfolding funs_term_ms_map_funs_term by auto
      then obtain L where id: "mm (l \<cdot> \<sigma>) = L + {# m - n #}" "mm (r \<cdot> \<sigma>) = L + {# m - Suc n #}" by auto
      have id: "mm (C \<langle>l \<cdot> \<sigma> \<rangle>) = (?C + L) + {# m - n #}" "mm (C \<langle>r \<cdot> \<sigma> \<rangle>) = (?C + L) + {# m - Suc n #}" 
        unfolding funs_term_ms_ctxt_apply map_funs_term_ctxt_distrib id multiset_eq_iff by auto
      have le: "?le (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)" unfolding id
        by (rule bounded_mult, insert small k1, auto)
      have id: "mmd (C \<langle>l \<cdot> \<sigma> \<rangle>) = drop_c (?C + L) + {# m - n #}" "mmd (C \<langle>r \<cdot> \<sigma> \<rangle>) = drop_c (?C + L) + drop_c {# m - Suc n #}" 
        unfolding id using small by (auto simp: drop_c_def)
      have led: "?led (C\<langle>r \<cdot> \<sigma>\<rangle>) (C\<langle>l \<cdot> \<sigma>\<rangle>)" unfolding id
        by (rule bounded_mult, insert small k1, auto simp: drop_c_def split: if_splits)
      show ?case
      proof (cases rel)
        case (Weak_TRS c_opt)
        with le led show ?thesis by (cases c_opt, auto)
      qed (insert le led, auto)
    qed
  qed
qed

lemma sig_match_raise_step_imp_bmult_less: assumes "(t,s) \<in> sig_step F (rstep (cover match Strict_TRS R \<union> raise))"
  shows "(mm s, mm t) \<in> bmult_less k"
  using sig_match_raise_step_imp_aux_rel[OF assms] by simp

lemma sig_match_raise_step_imp_mult_step: assumes "(t,s) \<in> sig_step F (rstep (cover match Strict_TRS R \<union> raise))"
  shows "(mm s, mm t) \<in> mult {(x, y). x < y}"
  by (rule bounded_mult_into_mult[OF sig_match_raise_step_imp_bmult_less[OF assms, unfolded bmult_less_def]])

lemma RTA_encoding: 
  assumes R': "R' \<subseteq> R"
  and S: "S \<subseteq> R"
  shows "relative_simulation_image 
  (sig_step F (rstep (cover match Strict_TRS R')))
  (sig_step F (rstep (raise \<union> cover match (Weak_TRS None) S))) ((bmult_less k)^-1) mm"
  (is "relative_simulation_image ?R ?S ?L _")
proof
  fix s t 
  assume "(s,t) \<in> ?R"
  then have "(mm s, mm t) \<in> ?L" 
  using sig_match_raise_step_imp_aux_rel[of s t Strict_TRS, OF _ R'] 
    by (auto simp: sig_step_def)
  then show "(mm s, mm t) \<in> ?L^+" by auto
next
  fix s t
  assume "(s,t) \<in> ?S"
  then have "(mm s, mm t) \<in> ?L^="
  using sig_match_raise_step_imp_aux_rel[of s t "Weak_TRS None", OF _ S] 
    by (force simp: sig_step_def)
  then show "(mm s, mm t) \<in> ?L^*" by auto
qed

lemma LMCS_encoding: 
  assumes R': "R' \<subseteq> R"
  and nc: "non_collapsing R'"
  and S: "S \<subseteq> R"
  shows "relative_simulation_image 
  (sig_step F (rstep (cover match Strict_TRS R')))
  (sig_step F (rstep (raise \<union> cover match (Weak_TRS (Some m)) S))) ((bmult_less k)^-1) mmd"
  (is "relative_simulation_image ?R ?S ?L _")
proof
  fix s t 
  assume "(s,t) \<in> ?R"
  then have "(mmd s, mmd t) \<in> ?L" 
  using sig_match_raise_step_imp_aux_rel[of s t Strict_TRS, OF _ R'] nc
    by (auto simp: sig_step_def)
  then show "(mmd s, mmd t) \<in> ?L^+" by auto
next
  fix s t
  assume "(s,t) \<in> ?S"
  then have "(mmd s, mmd t) \<in> ?L^="
  using sig_match_raise_step_imp_aux_rel[of s t "Weak_TRS (Some m)", OF _ S] 
    by (force simp: sig_step_def)
  then show "(mmd s, mmd t) \<in> ?L^*" by auto
qed  

lemma sig_match_raise_rel_linear_bound_LMsubst_closure: assumes 
  steps: "(s,t) \<in> (relto (sig_step F (rstep (cover match Strict_TRS Rs))) (sig_step F (rstep (raise \<union> cover match (Weak_TRS (Some m)) S))))^^n" (is "_ \<in> ?R ^^ n")  
  and Rs: "Rs \<subseteq> R"
  and S: "S \<subseteq> R"
  and nc: "non_collapsing Rs"
  shows "n \<le> term_size s * Suc k ^ m"
proof -
  let ?L = "bmult_less k"
  from relative_simulation_image.count_relative[OF LMCS_encoding[OF Rs nc S] steps, unfolded converse_power]
    obtain n' where n': "n' \<ge> n" and less: "(mmd t, mmd s) \<in> ?L^^n'" by auto
  from n' bound_mset_bmult_less[OF less]
  have "n \<le> bound_mset k (mmd s)" by simp
  also have "\<dots> \<le> term_size s * Suc k ^ m"
    by (rule bound_mset_mmd_size)
  finally show ?thesis .
qed  

lemma sig_match_raise_rel_linear_bound_RTA: assumes 
  steps: "(s,t) \<in> (relto (sig_step F (rstep (cover match Strict_TRS Rs))) (sig_step F (rstep (raise \<union> cover match (Weak_TRS None) S))))^^n" (is "_ \<in> ?R ^^ n")  
  and Rs: "Rs \<subseteq> R"
  and S: "S \<subseteq> R"
  shows "n \<le> term_size s * Suc k ^ m"
proof -
  let ?L = "bmult_less k"
  from relative_simulation_image.count_relative[OF RTA_encoding[OF Rs S] steps, unfolded converse_power]
    obtain n' where n': "n' \<ge> n" and less: "(mm t, mm s) \<in> ?L^^n'" by auto
  from n' bound_mset_bmult_less[OF less]
  have "n \<le> bound_mset k (mm s)" by simp
  also have "\<dots> \<le> term_size s * Suc k ^ m"
    by (rule bound_mset_mm_size)
  finally show ?thesis .
qed  

lemma sig_match_union_raise_linear_bound: assumes steps: "(s,t) \<in> (sig_step F (rstep (cover match Strict_TRS R \<union> raise)))^^n" (is "_ \<in> ?R ^^ n")
  shows "n \<le> term_size s * Suc k ^ m"
proof -
  from steps have "(mm t, mm s) \<in> (bmult_less k)^^n"
  proof (induct n arbitrary: t)
    case (Suc n)
    from Suc(2) obtain u where su: "(s,u) \<in> ?R ^^ n" and ut: "(u,t) \<in> ?R" by auto
    from sig_match_raise_step_imp_bmult_less[OF ut] Suc(1)[OF su] show ?case by (rule relpow_Suc_I2)
  qed simp
  from bound_mset_bmult_less[OF this] 
  have "n \<le> bound_mset k (mm s)" .
  also have "\<dots> \<le> term_size s * Suc k ^ m"
    by (rule bound_mset_mm_size)
  finally show ?thesis .
qed  

lemma sig_match_raise_rel_linear_bound: assumes 
  steps: "(s,t) \<in> (relto (sig_step F (rstep (cover match Strict_TRS Rs))) (sig_step F (rstep (raise \<union> cover match (Weak_TRS c_opt) S))))^^n" (is "_ \<in> ?R ^^ n")  
  and Rs: "Rs \<subseteq> R"
  and S: "S \<subseteq> R"
  and c_opt: "non_collapsing Rs \<and> c_opt = Some m \<or> c_opt = None"
  shows "n \<le> term_size s * Suc k ^ m"
proof (cases c_opt)
  case None
  from sig_match_raise_rel_linear_bound_RTA[OF steps[unfolded None] Rs S]
  show ?thesis .
next
  case (Some c)
  with c_opt have nc: "non_collapsing Rs" and c_opt: "c_opt = Some m" by auto
  from sig_match_raise_rel_linear_bound_LMsubst_closure[OF steps[unfolded c_opt] Rs S nc]
  show ?thesis .
qed


lemma SN_sig_step_match_raise: "SN (sig_step F (rstep (cover Matchbounds.match Strict_TRS R \<union> raise)))"
proof -
  let ?gt = "\<lambda> s t. (s,t) \<in> rstep (cover match Strict_TRS R \<union> raise) \<and> funas_term s \<subseteq> F \<and> funas_term t \<subseteq> F"  
  let ?lt = "{(x,y :: nat). x < y}"
  let ?le = "\<lambda> s t. (mm s, mm t) \<in> mult ?lt"
  let ?R = "{(s,t). ?le s t}"
  have id: "{(s,t). ?gt t s} = (sig_step F (rstep (cover match Strict_TRS R \<union> raise)))^-1" 
    unfolding sig_step_def by auto
  have trans: "trans ?lt" unfolding trans_def by auto
  have main: "wf {(s,t). ?gt t s}" 
  proof (rule wf_subset)
    show "wf ?R"
      using wf_inv_image[OF wf_mult[OF wf_less], of mm]
      unfolding inv_image_def .
  next    
    show "{(s,t). ?gt t s} \<subseteq> ?R" using sig_match_raise_step_imp_mult_step
      unfolding id by auto
  qed
  show "SN (sig_step F (rstep (cover match Strict_TRS R \<union> raise)))"
    by (rule wf_imp_SN[OF main[unfolded id]])
qed
end

lemma match_raise_locally_SN: assumes finR: "finite R" 
  shows "locally_terminating (cover match Strict_TRS R \<union> raise)"
  unfolding locally_terminating_def
proof (intro allI impI)
  fix F :: "('f \<times> nat) sig" 
  assume fin: "finite F" 
  from finite_list[OF fin] obtain Fs where F: "F = set Fs" by auto
  let ?hs = "map (\<lambda>(f,n). height f) Fs"
  define m where "m = max_list ?hs"
  have small: "\<And> f n. (f,n) \<in> F \<Longrightarrow> height f \<le> m" unfolding F m_def using max_list[of _ ?hs] by force
  from finite_list[OF finR] obtain Rs where R: "R = set Rs" by auto
  let ?fs = "map (\<lambda> (l,r). length (funas_term_list r)) Rs"
  define k where "k = Suc (max_list ?fs)"
  have small2: "\<And> l r. (l,r) \<in> R \<Longrightarrow> length (funas_term_list r) \<le> k" unfolding R k_def using max_list[of _ ?fs] by force
  have k1: "1 \<le> k" unfolding k_def by simp
  show "SN (sig_step F (rstep (cover Matchbounds.match Strict_TRS R \<union> raise)))"
    by (rule SN_sig_step_match_raise[OF small small2 k1])
qed 
end

definition ge_raise :: "('f \<times> nat) sig \<Rightarrow> (('f \<times> nat),'v)term \<Rightarrow> (('f \<times> nat),'v)term \<Rightarrow> bool" where
  "ge_raise F s t \<equiv> (t,s) \<in> (sig_step F (rstep raise))^*"

lemma ge_raise_trans: "ge_raise F s t \<Longrightarrow> ge_raise F t u \<Longrightarrow> ge_raise F s u" unfolding ge_raise_def by auto

fun max_raise :: "(('f \<times> nat),'v)rule \<Rightarrow> (('f \<times> nat),'v)term option" where
  "max_raise (Var x,Var y) = (do {
     guard (x = y);
     Some (Var y)
   })"
| "max_raise (Fun (f1,h1) ts1, Fun (f2,h2) ts2) = (do {
    guard ((f1,length ts1) = (f2,length ts2));
    ts \<leftarrow> mapM max_raise (zip ts1 ts2);
    Some (Fun (f2,max h1 h2) ts)
  })"
| "max_raise _ = None"

lemma max_raise_Fun: assumes len: "length ts1 = n" "length ts2 = n" "length ts = n"
  and some: "\<And> j. j < n \<Longrightarrow> max_raise (ts1 ! j, ts2 ! j) = Some (ts ! j)"
  shows "max_raise (Fun (f, a1) ts1, Fun (f, a2) ts2) = Some (Fun (f, max a1 a2) ts)"
proof -
  let ?z = "zip ts1 ts2"
  from mapM_None[of max_raise ?z]
  obtain ts' where Some: "mapM max_raise ?z = Some ts'" using len some 
    by (cases "mapM max_raise ?z", auto simp: set_zip)
  from mapM_Some[OF Some] len some have "ts' = ts" 
    by (intro nth_equalityI, auto)
  with Some have "mapM max_raise (zip ts1 ts2) = Some ts" by simp
  then show ?thesis by (simp add: len)
qed

lemma max_raise_refl: "max_raise (s,s) = Some s"
proof (induct s)
  case (Fun f ss)
  obtain g a where f: "f = (g,a)" by force
  have "max_raise (Fun (g,a) ss, Fun (g,a) ss) = Some (Fun (g,max a a) ss)"
    by (rule max_raise_Fun[OF refl], insert Fun, auto)
  then show ?case by (simp add: f)
qed auto

lemma max_raise_sym: "max_raise (s,t) = max_raise (t,s)"
proof (induct s arbitrary: t)
  case (Var x t)
  show ?case by (cases t, auto simp: guard_def)
next
  case (Fun f ss t) note IH = this
  obtain fn fh where f: "f = (fn, fh)" by force
  show ?case 
  proof (cases t)
    case (Fun g ts)
    obtain gn gh where g: "g = (gn, gh)" by force
    let ?f = "(fn,length ss)"
    let ?g = "(gn,length ts)"
    have "(?f = ?g) = (?g = ?f)" "max fh gh = max gh fh" by auto
    note id = Fun f g this
    show ?thesis 
    proof (cases "?g = ?f")
      case False
      then show ?thesis unfolding max_raise.simps guard_def id by auto
    next
      case True
      then have len: "length ss = length ts" by auto
      let ?ssts = "mapM max_raise (zip ss ts)"
      let ?tsss = "mapM max_raise (zip ts ss)"
      from True have "?thesis = (?ssts = ?tsss)"
        unfolding max_raise.simps id guard_def 
        by (simp, cases ?ssts, (cases ?tsss, (auto)[2])+)
      also have "..." using len IH
        by (induct ss ts rule: list_induct2, force+)
      finally show ?thesis by simp
    qed
  qed auto
qed


lemma max_raise_base_Some: "base_term s = base_term t \<Longrightarrow> (\<exists> u. max_raise (s,t) = Some u \<and> base_term u = base_term t)"
proof (induct s arbitrary: t)
  case (Var x t)
  then show ?case by (cases t, auto)
next
  case (Fun fp ss)
  then obtain gp ts where t: "t = Fun gp ts" by (cases t, auto)
  obtain f fh where fp: "fp = (f,fh)" by force
  note cond = Fun(2)[unfolded t fp]
  from cond obtain gh where gp: "gp = (f,gh)" by (cases gp, auto)
  from cond have id: "map base_term ss = map base_term ts" by auto
  from arg_cong[OF this, of length] have len: "length ss = length ts" by auto
  let ?p = "\<lambda> i u. max_raise (ss ! i, ts ! i) = Some u \<and> base_term u = base_term (ts ! i)"
  {
    fix i
    assume i: "i < length ts"
    then have "ss ! i \<in> set ss" using len by auto
    from Fun(1)[OF this map_nth_conv[OF id, rule_format]] i len
    have "\<exists> u. ?p i u" by auto
  }
  then have "\<forall> i. \<exists> u. i < length ts \<longrightarrow> ?p i u" by blast
  from choice[OF this] obtain u where IH: "\<And> i. i < length ts \<Longrightarrow> ?p i (u i)" by blast
  let ?u = "Fun (f,max fh gh) (map u [0 ..< length ts])"
  have id1: "map (base_term \<circ> u) [0..<length ts] = map base_term ts"
    by  (rule nth_map_conv, insert IH, auto)
  have id2: "mapM max_raise (zip ss ts) = Some (map u [0..<length ts])"
    unfolding mapM_map set_zip using IH by (auto intro!: nth_map_conv simp: len)
  show ?case unfolding t fp gp
    by (rule exI[of _ ?u], auto simp: len id1 id2)
qed

lemma max_raise_Some_imp_eq_base: "max_raise (s,t) = Some u \<Longrightarrow> base_term s = base_term u \<and> base_term t = base_term u"
proof (induct s arbitrary: t u)
  case (Var x t u)
  then show ?case by (cases t, auto split: bind_splits)
next
  case (Fun f ss t u)
  then obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  obtain h a where f: "f = (h,a)" by force
  from Fun(2) t f obtain b where g: "g = (h,b)" by (cases g, auto split: bind_splits)
  note rec = Fun(2)[unfolded t f g, simplified]
  from rec have len: "length ss = length ts" by (simp add: guard_def split: if_splits)
  from rec obtain us where u: "u = Fun (h,max a b) us" by (cases u, auto split: bind_splits)
  from rec u have rec: "mapM max_raise (zip ss ts) = Some us" by (auto simp: bind_eq_Some_conv)
  from mapM_Some[OF rec] len have len: "length ss = length us" "length ts = length us" by auto
  {
    fix i
    assume i: "i < length us"
    have "base_term (ss ! i) = base_term (us ! i) \<and> base_term (ts ! i) = base_term (us ! i)"
      by (rule Fun(1), insert i len mapM_Some_idx[OF rec], auto)
  }
  then have id: "map base_term ss = map base_term us \<and> map base_term ts = map base_term us"
    by (intro conjI nth_equalityI, auto simp: len)
  show ?case unfolding t u f g using id by auto
qed  
  
lemma max_raise_ge_raise: assumes F: "\<And> f h h' n. ((f,h),n) \<in> F \<Longrightarrow> h' \<le> h \<Longrightarrow> ((f,h'),n) \<in> F"
  shows "max_raise (s,t) = Some u \<Longrightarrow> funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow> ge_raise F u s \<and> funas_term u \<subseteq> F" unfolding ge_raise_def
proof (induct s arbitrary: t u)
  case (Var x t u)
  then show ?case by (cases t, auto simp: guard_def split: if_splits)
next
  case (Fun f ss t u) 
  note IH = Fun(1)
  note some = Fun(2)
  obtain fn fh where f: "f = (fn, fh)" by force
  from some obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  obtain gn gh where g: "g = (gn, gh)" by force
  note some = some[unfolded t f g, simplified]
  from some have fn: "gn = fn" and len: "length ts = length ss" by (auto split: bind_splits)
  from some obtain us where map: "mapM max_raise (zip ss ts) = Some us"
    and u: "u = Fun ((fn,max fh gh)) us" by (auto split: bind_splits)
  note map = map[unfolded mapM_map]
  from map have us: "us = map (\<lambda>x. the (max_raise x)) (zip ss ts)" by (auto split: if_splits)
  from us len have len2: "length ss = length us" by auto
  have "\<exists> k. max fh gh = fh + k" by presburger
  then obtain k where max: "max fh gh = fh + k" by auto
  from Fun(3)[unfolded f g] len2 have F1: "((fn,fh),length us) \<in> F" "\<Union> (funas_term ` set ss) \<subseteq> F" by auto
  from Fun(4)[unfolded t f g fn] len len2 have F2: "((fn,gh),length us) \<in> F" "\<Union> (funas_term ` set ts) \<subseteq> F" by auto
  let ?R = "sig_step F (rstep raise)"  
  let ?u = "\<lambda> h. Fun (fn,fh + h) us"
  {
    fix i
    assume i: "i < length ss"
    then have mem: "ss ! i \<in> set ss" by auto
    from i have "(ss ! i, ts ! i) \<in> set (zip ss ts)" using len 
      unfolding set_zip by auto
    with map have max: "max_raise (ss ! i, ts ! i) \<noteq> None" by (auto split: if_splits)
    have "(ss ! i, us ! i) \<in> ?R^* \<and> funas_term (us ! i) \<subseteq> F"
    proof (rule IH[OF mem])
      show "max_raise (ss ! i, ts ! i) = Some (us ! i)"
        unfolding us using max i len len2 by auto
    qed (insert F1(2) F2(2) i len len2, unfold set_conv_nth, auto, blast)
  } note IH = this
  have F3: "\<Union> (funas_term ` set us) \<subseteq> F" unfolding set_conv_nth using IH[unfolded len2] by auto
  from F1(1) F2(1) have "((fn, max fh gh), length us) \<in> F" unfolding max_def by (auto split: if_splits)
  then have Fk: "((fn,fh + k),length us) \<in> F" unfolding max by auto
  have "(Fun f ss, Fun f us) \<in> ?R^*"
  proof (rule all_ctxt_closedD[OF all_ctxt_closed_sig_rsteps _ len2], unfold f len)
    show "((fn, fh), length us) \<in> F" by fact
    fix i
    assume i: "i < length ss"
    from IH[OF this] have "(ss ! i, us ! i) \<in> ?R^*" "funas_term (us ! i) \<subseteq> F" by auto
    show "(ss ! i, us ! i) \<in> ?R^*" by fact
    show "funas_term (us ! i) \<subseteq> F" by fact
    show "funas_term (ss ! i) \<subseteq> F" using F1(2) i unfolding set_conv_nth by auto
  qed
  also have "(Fun f us, u) \<in> ?R^*"
    unfolding u f fn max using Fk
  proof (induct k)
    case (Suc k)
    note k = Suc(2)
    have sk: "((fn,fh + k),length us) \<in> F" by (rule F[OF k], simp)
    have "(Fun (fn,fh) us, ?u k) \<in> ?R^*" by (rule Suc(1)[OF sk])
    also have "(?u k, ?u (Suc k)) \<in> ?R"
      by (rule sig_stepI[OF rstepI[of "?u k" "?u (Suc k)" _ _ Hole Var]], unfold raise_def, insert F3 k sk, auto)
    finally show ?case .
  qed auto
  finally show ?case unfolding u max using Fk F3 by auto
qed

fun max_raise_list :: "('f \<times> nat,'v)term list \<Rightarrow> ('f \<times> nat,'v) term option" where
  "max_raise_list [] = None"
| "max_raise_list [t] = Some t"
| "max_raise_list (t # s # ts) = do {
     h \<leftarrow> max_raise (t,s);
     max_raise_list (h # ts)
  }"

lemma max_raise_list_ge_raise: assumes F: "\<And> f h h' n. ((f,h),n) \<in> F \<Longrightarrow> h' \<le> h \<Longrightarrow> ((f,h'),n) \<in> F"
  shows "t \<in> set ts \<Longrightarrow> max_raise_list ts = Some s \<Longrightarrow> \<Union> (funas_term ` set ts) \<subseteq> F \<Longrightarrow> ge_raise F s t \<and> funas_term s \<subseteq> F"
proof (induct ts arbitrary: t rule: max_raise_list.induct)
  case (3 u v ts t)
  from 3(3) obtain w where w: "max_raise (u,v) = Some w" by (auto split: bind_splits)
  from 3(4) have Fu: "funas_term u \<subseteq> F" and Fv: "funas_term v \<subseteq> F" and Fts: "\<Union> (funas_term ` set ts) \<subseteq> F" by auto
  from 3(3) w have "max_raise_list (w # ts) = Some s" by auto
  note IH = 3(1)[OF w _ this]
  from max_raise_ge_raise[OF F w Fu Fv] have Fw: "funas_term w \<subseteq> F" by auto
  with Fts have "\<Union> (funas_term ` set (w # ts)) \<subseteq> F" by auto
  note IH = IH[OF _ this]
  from 3(2) have "t \<in> {u,v} \<or> t \<in> set ts" by auto
  then show ?case
  proof
    assume "t \<in> {u,v}"
    with max_raise_ge_raise[OF F w Fu Fv] max_raise_ge_raise[OF F w[unfolded max_raise_sym[of u]] Fv Fu] 
    have ge: "ge_raise F w t" by auto
    from ge_raise_trans[OF IH[THEN conjunct1] ge] IH show ?thesis by auto
  qed (insert IH, auto)
next
  case (2 t u)
  then have u: "u = s" and F: "funas_term s \<subseteq> F" by auto
  show ?case unfolding u ge_raise_def using F by auto
qed auto
  
lemma max_raise_list_base_Some: "base_term ` set ts = {b} \<Longrightarrow> \<exists> u. max_raise_list ts = Some u \<and> base_term u = b"
proof (induct ts rule: max_raise_list.induct)
  case (3 t v vs)
  from 3(2) have "base_term t = base_term v" "base_term v = b" by auto
  from max_raise_base_Some[OF this(1)] this(2) obtain u 
    where u: "max_raise (t,v) = Some u" and bu: "base_term u = b"
    by auto
  from 3(1)[OF u] bu 3(2) obtain v where "max_raise_list (u # vs) = Some v" and "base_term v = b" by auto
  with u show ?case by auto
qed auto

lemma max_raise_list_Some_imp_eq_base: "max_raise_list ss = Some t \<Longrightarrow> base_term ` set ss = {base_term t}"
proof (induct ss rule: max_raise_list.induct)
  case (3 s1 s2 ss)
  from 3(2) obtain t1 where mr: "max_raise (s1,s2) = Some t1" by (cases "max_raise (s1,s2)", auto)
  from 3(2) mr have "max_raise_list (t1 # ss) = Some t" by auto
  from 3(1)[OF mr this] have IH: "base_term ` set (t1 # ss) = {base_term t}" by auto
  from max_raise_Some_imp_eq_base[OF mr] IH
  show ?case by auto
qed auto

lemma max_raise_list_Fun: assumes "\<And> j. j < n \<Longrightarrow> length (tss j) = k"
    and "\<And> j. j < n \<Longrightarrow> max_raise_list (tss j) = Some (ts ! j)"
    and "length as = k"
    and "length ts = n"
    and "0 < k"
  shows "max_raise_list (map (\<lambda>i. Fun (f, as ! i) (map (\<lambda>j. tss j ! i) [0..<n])) [0..<k]) = Some (Fun (f, max_list as) ts)"
  using assms
proof (induct k arbitrary: as ts tss)
  case (Suc k as ts tss)
  note IH = Suc(1)
  note prems = Suc(2-)
  show ?case
  proof (cases k)
    case 0
    from 0 prems obtain a where as: "as = [a]" by (cases as, auto)
    {
      fix i
      assume "i < n"
      from prems(1-2)[OF this, unfolded 0]
      have "tss i ! 0 = ts ! i" by (cases "tss i", auto)
    }
    with as Suc(2-) show ?thesis unfolding 0
      by (simp, intro nth_equalityI, auto)
  next
    case (Suc k')
    let ?n = "[0 ..< n]"
    define ts1 where "ts1 = map (\<lambda> j. hd (tss j)) ?n"
    define ts2 where "ts2 = map (\<lambda> j. hd (tl (tss j))) ?n"
    define tss' where "tss' = (\<lambda> j. tl (tl (tss j)))"
    {
      fix j
      assume j: "j < n"
      from prems(1)[OF j, unfolded Suc] j have "tss j = ts1 ! j # ts2 ! j # tss' j" unfolding ts1_def ts2_def tss'_def
        by (cases "tss j", auto, cases "tl (tss j)", auto)
    } note tss = this
    from prems(1) tss Suc have len_tss': "\<And> j. j < n \<Longrightarrow> length (tss' j) = k'" by auto
    {
      fix j
      assume j: "j < n"
      note prems(2)[OF j, unfolded tss[OF j], simplified]
    }
    then have "\<forall> j. \<exists> t. j < n \<longrightarrow> max_raise (ts1 ! j, ts2 ! j) = Some t \<and> max_raise_list (t # tss' j) = Some (ts ! j)"
      by (auto simp: bind_eq_Some_conv)
    from choice[OF this] obtain t 
      where max_raise: "\<And> j. j < n \<Longrightarrow> max_raise (ts1 ! j, ts2 ! j) = Some (t j)" 
      and rec: "\<And> j. j < n \<Longrightarrow> max_raise_list (t j # tss' j) = Some (ts ! j)" by auto
    let ?t = "map t ?n"
    define tss'' where "tss'' = (\<lambda> j. t j # tss' j)"
    have mr: "max_raise (Fun (f, as ! 0) (map (\<lambda>j. tss j ! 0) [0..<n]), Fun (f, as ! Suc 0) (map (\<lambda>j. tss j ! Suc 0) [0..<n]))
      = Some (Fun (f, max (as ! 0) (as ! Suc 0)) ?t)"
      by (rule max_raise_Fun[of _ n], insert max_raise tss, auto)
    from prems(3)[unfolded Suc] obtain a1 a2 as' where as: "as = a1 # a2 # as'"
      by (cases as, auto, cases "tl as", auto)
    let ?as = "max (as ! 0) (as ! Suc 0) # as'"
    from as prems Suc have max_as: "max_list as = max_list ?as" 
      and len_as': "length as' = k'" by auto
    show ?thesis 
      unfolding Suc map_upt_Suc
      unfolding max_raise_list.simps mr bind.simps max_as
      by (rule HOL.trans[OF arg_cong[of _ _ max_raise_list] IH[of tss'' _ ?as]],
        unfold Suc map_upt_Suc, auto simp: tss''_def as tss prems rec len_as' len_tss')
  qed
qed simp

inductive_set raise_step :: "('f \<times> nat,'v)trs \<Rightarrow> ('f \<times> nat,'v)trs" for R :: "('f \<times> nat, 'v)trs" where
  raise_step: "(l,r) \<in> R 
  \<Longrightarrow> split_vars l = (C,xs) 
  \<Longrightarrow> length ss = length xs 
  \<Longrightarrow> (\<And> i j. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i = xs ! j \<Longrightarrow> base_term (ss ! i) = base_term (ss ! j))
  \<Longrightarrow> (\<And> x. \<Theta> x = (if x \<in> vars_term l then the (max_raise_list (map fst (filter (\<lambda> (si,xi). xi = x) (zip ss xs)))) else Var x))
  \<Longrightarrow> (D \<langle> fill_holes C ss \<rangle>, D \<langle> r \<cdot> \<Theta> \<rangle>) \<in> raise_step R"

lemma raise_step_set: "raise_step R = {(D \<langle> fill_holes C ss \<rangle>, D \<langle> r \<cdot> \<Theta> \<rangle>) | l D C ss r \<Theta> xs. 
  (l,r) \<in> R \<and>
  split_vars l = (C,xs) \<and> 
  length ss = length xs \<and>
  (\<forall> i j. i < length xs \<longrightarrow> j < length xs \<longrightarrow> xs ! i = xs ! j \<longrightarrow> base_term (ss ! i) = base_term (ss ! j)) \<and>
  (\<forall> x. \<Theta> x = (if x \<in> vars_term l then the (max_raise_list (map fst (filter (\<lambda> (si,xi). xi = x) (zip ss xs)))) else Var x))}"
  (is "?l = ?r")
proof -
  define rr where "rr = ?r" 
  have "(s,t) \<in> ?r" if "(s,t) \<in> ?l" for s t using that by (cases, blast)
  moreover
  {
    fix s t
    assume "(s,t) \<in> ?r"
    then obtain  l D C ss r \<Theta> xs 
    where prem: "(s,t) = (D \<langle> fill_holes C ss \<rangle>, D \<langle> r \<cdot> \<Theta> \<rangle>) \<and> (l,r) \<in> R \<and>
      split_vars l = (C,xs) \<and> 
      length ss = length xs \<and>
      (\<forall> i j. i < length xs \<longrightarrow> j < length xs \<longrightarrow> xs ! i = xs ! j \<longrightarrow> base_term (ss ! i) = base_term (ss ! j)) \<and>
      (\<forall> x. \<Theta> x = (if x \<in> vars_term l then the (max_raise_list (map fst (filter (\<lambda> (si,xi). xi = x) (zip ss xs)))) else Var x))"
      by blast
    from prem have id: "s = D \<langle> fill_holes C ss \<rangle>" "t = D \<langle> r \<cdot> \<Theta> \<rangle>" by auto
    have "(s,t) \<in> ?l" unfolding id
      by (intro raise_step[of l r _ C], insert prem, blast+)
  }
  ultimately show ?thesis unfolding rr_def[symmetric] by force
qed

context 
  fixes F :: "('f \<times> nat)sig"
  assumes F_cond: "\<And> f h h' n. ((f,h),n) \<in> F \<Longrightarrow> h' \<le> h \<Longrightarrow> ((f,h'),n) \<in> F"
begin
lemma sig_raise_step_imp_sig_steps:  assumes step: "(s,t) \<in> sig_step F (raise_step R)"
  shows "(s,t) \<in> (sig_step F (rstep raise))^* O (sig_step F (rstep R))"
proof -
  let ?R = "sig_step F (rstep R)"
  let ?Rai = "sig_step F (rstep raise)"
  from step have "(s,t) \<in> raise_step R" "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" by auto
  then show ?thesis
  proof (induct rule: raise_step.induct)
    case (raise_step l r C xs ss \<Theta> D)
    note Theta = raise_step(5)
    note split = raise_step(2)
    note len_ss = raise_step(3)
    note F = raise_step(6,7)  
    from F(1) have FCss: "funas_term (fill_holes C ss) \<subseteq> F" by auto    
    from split_vars_eqf_subst[of l \<Theta>, unfolded split]
    have eqf: "l \<cdot> \<Theta> =\<^sub>f (C, map \<Theta> xs)" by auto
    from eqfE[OF eqf] have ltheta: "l \<cdot> \<Theta> = fill_holes C (map \<Theta> xs)" and nh: "num_holes C = length xs" by auto
    from nh len_ss have "num_holes C = length ss" by simp
    then have Css: "fill_holes C ss =\<^sub>f (C,ss)" by auto
    from FCss[unfolded eqf_funas_term[OF this]] have FC: "funas_mctxt C \<subseteq> F" and Fss: "\<Union> (funas_term ` set ss) \<subseteq> F" by auto
    {
      fix i
      assume i: "i < length xs"
      then have id: "map \<Theta> xs ! i = \<Theta> (xs ! i)" by auto
      let ?ts = "map fst [(si, xi)\<leftarrow>zip ss xs . xi = xs ! i]"
      have "(ss ! i, map \<Theta> xs ! i) \<in> (sig_step F (rstep raise))^* \<and> funas_term (map \<Theta> xs ! i) \<subseteq> F" unfolding id 
      proof (rule max_raise_list_ge_raise[unfolded ge_raise_def raise_step, OF F_cond])
        show ss: "ss ! i \<in> set ?ts" using i unfolding set_map set_filter set_zip len_ss by force
        have "base_term ` set ?ts = {base_term (ss ! i)}" (is "?l = ?r")
        proof
          show "?r \<subseteq> ?l" using ss by auto
          show "?l \<subseteq> ?r"
          proof
            fix b
            assume "b \<in> ?l"
            then obtain j where j: "j < length xs" and id: "xs ! j = xs ! i" and b: "b = base_term (ss ! j)"
              unfolding set_map set_filter set_zip len_ss by auto
            from raise_step(4)[OF j i id] show "b \<in> ?r" unfolding b by auto
          qed
        qed                
        from max_raise_list_base_Some[OF this]
        show "max_raise_list ?ts = Some (\<Theta> (xs ! i))" unfolding Theta
          using split_vars_vars_term[of l, symmetric] i unfolding split by auto
      next
        have "set ?ts \<subseteq> set ss" unfolding set_map set_filter set_zip by force
        with Fss         
        show "\<Union> (funas_term ` set ?ts) \<subseteq> F" by auto
      qed 
    }
    note main = this
    have FTheta: "\<Union> (funas_term ` set (map \<Theta> xs)) \<subseteq> F" unfolding set_map set_conv_nth length_map using main[THEN conjunct2] by force
    have raise: "(fill_holes C ss, fill_holes C (map \<Theta> xs)) \<in> ?Rai^* \<and> fill_holes C (map \<Theta> xs) =\<^sub>f (C, map \<Theta> xs)"
      by (rule eqf_all_ctxt_closed_step[OF all_ctxt_closed_sig_rsteps Css _ _ FCss], unfold length_map, insert main FTheta len_ss, auto)
    from raise ltheta have steps: "(fill_holes C ss, l \<cdot> \<Theta>) \<in> ?Rai^*" by auto
    from eqf_funas_term[OF eqf] FC FTheta have Flt: "funas_term (l \<cdot> \<Theta>) \<subseteq> F" by auto
    from F have FD: "funas_ctxt D \<subseteq> F" by auto
    have steps: "(D\<langle>fill_holes C ss\<rangle>, D\<langle>l \<cdot> \<Theta>\<rangle>) \<in> ?Rai^*" 
      by (rule all_ctxt_closed_ctxtE[OF _ FCss Flt steps FD], auto)
    moreover
    {
      from raise_step(1) have step: "(D\<langle>l \<cdot> \<Theta>\<rangle>, D\<langle>r \<cdot> \<Theta>\<rangle>) \<in> rstep R" by auto
      have "(D\<langle>l \<cdot> \<Theta>\<rangle>, D\<langle>r \<cdot> \<Theta>\<rangle>) \<in> ?R"
        by (rule sig_stepI[OF step _ F(2)], insert Flt FD, auto)
    }
    ultimately show ?case by blast
  qed
qed

lemma sig_raise_steps_imp_sig_steps:  assumes step: "(s,t) \<in> (sig_step F (raise_step R))^*"
  shows "(s,t) \<in> (sig_step F (rstep (raise \<union> R)))^*"
  using assms
proof (induct)
  case (step t u)
  from step(3) sig_raise_step_imp_sig_steps[OF step(2)]
  have "(s,u) \<in> (sig_step F (rstep (raise \<union> R)))\<^sup>* O
    (sig_step F (rstep raise))\<^sup>* O sig_step F (rstep R)" by auto
  then show ?case unfolding sig_step_union rstep_union by regexp
qed simp

lemma sig_rel_raise_step_imp_sig_steps:  assumes step: "(s,t) \<in> relto (sig_step F (raise_step R)) (sig_step F (raise_step S))" (is "_ \<in> relto ?RR ?RS")
  shows "(s,t) \<in> relto (sig_step F (rstep R)) (sig_step F (rstep (raise \<union> S)))" (is "_ \<in> relto ?R ?S")
proof -
  from step obtain u v where su: "(s,u) \<in> ?RS^*" and uv: "(u,v) \<in> ?RR" and vt: "(v,t) \<in> ?RS^*" by blast
  from sig_raise_step_imp_sig_steps[OF uv] have uv: "(u,v) \<in> ?S^* O ?R" unfolding sig_step_union rstep_union by regexp
  from sig_raise_steps_imp_sig_steps[OF su] have su: "(s,u) \<in> ?S^*" .
  from sig_raise_steps_imp_sig_steps[OF vt] have vt: "(v,t) \<in> ?S^*" .
  from su uv vt have st: "(s,t) \<in> ?S^* O ?S^* O ?R O ?S^*" by blast
  then show ?thesis by regexp
qed
end

lemma raise_step_union: "raise_step (R \<union> S) = raise_step R \<union> raise_step S" 
  unfolding raise_step_set by blast


lemma rstep_raise_imp_base_eq: "(s,t) \<in> rstep raise \<Longrightarrow> base_term s = base_term t"
  by (induct, auto simp: raise_def)

lemma rstep_cover_imp_base_step: "(s,t) \<in> rstep (cover ff rel R) \<Longrightarrow> (base_term s, base_term t) \<in> rstep R"
proof (induct rule: rstep_induct_rule)
  case (IH C \<sigma> ll lr)
  from this[unfolded cover_def] obtain  l h r where lr: "(l,r) \<in> R" and l: "base_term ll = l" 
    and r: "lr = lift_term h r" by blast
  from base_lift[of h r] r have r: "base_term lr = r" by simp
  from lr l r have "(base_term ll, base_term lr) \<in> R" by simp
  then show ?case by auto
qed

lemma raise_step_cover_imp_rstep: assumes "(s,t) \<in> raise_step (cover ff rel R)"
  shows "(base_term s, base_term t) \<in> rstep R"
proof -
  from assms have "(s,t) \<in> sig_step UNIV (raise_step (cover ff rel R))" by (simp add: sig_step_UNIV)
  from sig_raise_step_imp_sig_steps[OF _ this]
  have "(s,t) \<in> (rstep raise)\<^sup>* O rstep (cover ff rel R)" by (simp add: sig_step_UNIV)
  then obtain u where su: "(s,u) \<in> (rstep raise)^*" and ut: "(u,t) \<in> rstep (cover ff rel R)" by auto
  from su have "base_term s = base_term u"
  proof (induct)
    case (step v u)
    from rstep_raise_imp_base_eq[OF step(2)] step(3) show ?case by simp
  qed simp
  with rstep_cover_imp_base_step[OF ut] show ?thesis by simp
qed

lemma raise_steps_covers_imp_rsteps: assumes "(s,t) \<in> (raise_step (cover ff rel R \<union> cover ff' rel' R') )^*"
  shows "(base_term s, base_term t) \<in> (rstep (R \<union> R'))^*"
  using assms
proof (induct)
  case (step u t)
  from step(2)[unfolded raise_step_union]
  have "(base_term u, base_term t) \<in> (rstep (R \<union> R'))"
  proof 
    assume "(u,t) \<in> raise_step (cover ff rel R)"
    from raise_step_cover_imp_rstep[OF this] show ?thesis by auto
  next
    assume "(u,t) \<in> raise_step (cover ff' rel' R')"
    from raise_step_cover_imp_rstep[OF this] show ?thesis by auto
  qed
  with step(3) show ?case by auto
qed simp

lemma raise_steps_cover_imp_rsteps: assumes steps: "(s,t) \<in> (raise_step (cover ff rel R))^*"
  shows "(base_term s, base_term t) \<in> (rstep R)^*"
  using raise_steps_covers_imp_rsteps[of s t ff rel R ff rel R] steps by auto

(* lemma 12 in IC 09 *)
context
  fixes R :: "('f,'v)trs"
  assumes var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin
lemma rstep_imp_raise_step[rule_format]: assumes "(s,t) \<in> rstep R"
  and "base_term s' = s"
  shows "(\<exists> t'. base_term t' = t \<and> (s',t') \<in> raise_step (cover ff rel R))"
proof -
  have "(s,t) \<in> rstep R \<Longrightarrow> base_term s' = s \<longrightarrow> (\<exists> t'. (s',t') \<in> raise_step (cover ff rel R) \<and> base_term t' = t)"
  proof (induct arbitrary: s' rule: rstep_induct_rule)
    case (IH D \<sigma> l r)
    show ?case
    proof 
      fix s'
      let ?R = "cover ff rel R"
      assume "base_term s' = D \<langle> l \<cdot> \<sigma> \<rangle>"
      from map_funs_term_ctxt_decomp[OF this] 
      obtain E u where D: "D = map_funs_ctxt base E" and u: "l \<cdot> \<sigma> = base_term u" and s': "s' = E \<langle> u \<rangle>" by blast
      from subst_eq_map_decomp[OF u]
      obtain C xs \<delta>s where u: "u =\<^sub>f (C, \<delta>s)" 
        and split: "split_vars l = (map_mctxt base C, xs)" 
        and \<sigma>: "\<And> i. i < length xs \<Longrightarrow> \<sigma> (xs ! i) = base_term (\<delta>s ! i)" by auto
      from split_vars_map_mctxt[OF split] have splitv: "split_vars (fill_holes C (map Var xs)) = (C,xs)" by auto
      from split_vars_num_holes[of "fill_holes C (map Var xs)", unfolded splitv] have nh: "num_holes C = length (map Var xs)" by simp
      from eqfE[OF u] have u: "u = fill_holes C \<delta>s" and \<delta>s: "num_holes C = length \<delta>s" by auto
      from split_vars_eqf_subst[of l Var, unfolded split] have l: "l =\<^sub>f (map_mctxt base C, map Var xs)" by simp
      have "\<exists> y. (fill_holes C (map Var xs),lift_term y r) \<in> ?R" unfolding cover_def
      proof (rule exI, rule, intro exI, rule conjI[OF refl conjI[OF IH conjI[OF _ refl]]]) 
        show "base_term (fill_holes C (map Var xs)) = l" 
        unfolding eqfE(1)[OF map_funs_term_fill_holes[OF nh]]
        unfolding eqfE[OF l] map_map o_def by auto
      qed
      then obtain n where rule: "(fill_holes C (map Var xs), lift_term n r) \<in> ?R" ..
      from \<delta>s nh have len: "length \<delta>s = length xs" by auto
      define \<Theta> where "\<Theta> = (\<lambda> x. (if x \<in> vars_term (fill_holes C (map Var xs))
           then the (max_raise_list (map fst [(si, xi)\<leftarrow>zip \<delta>s xs . xi = x])) else Var x))"
      show "\<exists>t'. (s', t') \<in> raise_step ?R \<and> base_term t' = D\<langle>r \<cdot> \<sigma>\<rangle>"
      proof (intro exI conjI, unfold s' D u, rule raise_step[OF rule splitv])
        fix i j
        assume i: "i < length xs" and j: "j < length xs" and id: "xs ! i = xs ! j"
        show "base_term (\<delta>s ! i) = base_term (\<delta>s ! j)" 
          using \<sigma>[OF i, symmetric, unfolded id, unfolded \<sigma>[OF j]] i j by auto
      next
        have "(base_term E\<langle>lift_term n r \<cdot> \<Theta>\<rangle> = (map_funs_ctxt base E)\<langle>r \<cdot> \<sigma>\<rangle>) = (r \<cdot> (\<lambda>x. base_term (\<Theta> x)) = r \<cdot> \<sigma>)" (is "?goal = _") 
          by (simp add: base_lift)
        also have "\<dots>"
        proof (rule term_subst_eq)
          fix x
          assume "x \<in> vars_term r"
          with var_cond[OF IH] have x: "x \<in> vars_term l" by auto
          then have xs: "x \<in> set xs" using split_vars_vars_term[of l, unfolded split] by auto
          also have "set xs = vars_term (fill_holes C (map Var xs))" using split_vars_vars_term[of "fill_holes C (map Var xs)", unfolded splitv] by auto
          finally have x: "(x \<in> vars_term (fill_holes C (map Var xs))) = True" by simp
          let ?ts = "map fst [(si, xi)\<leftarrow>zip \<delta>s xs . xi = x]"
          {
            from xs obtain i where i: "i < length xs" and x: "x = xs ! i" unfolding set_conv_nth by auto
            then have "\<delta>s ! i \<in> set ?ts" unfolding set_zip set_map set_filter len by force
            with \<sigma>[OF i] have "\<sigma> x \<in> base_term ` set ?ts" unfolding x by auto
          }
          moreover
          {
            fix t
            assume "t \<in> base_term ` set ?ts"
            then obtain i where t: "t = base_term (\<delta>s ! i)" and i: "i < length xs" and x: "xs ! i = x"
              unfolding set_map set_filter set_zip by force
            from \<sigma>[OF i] t x have "t = \<sigma> x" by auto
          }
          ultimately have "base_term ` set ?ts = {\<sigma> x}" by blast        
          from max_raise_list_base_Some[OF this] obtain u where res: "max_raise_list ?ts = Some u" and u: "base_term u = \<sigma> x" by auto
          have "base_term (\<Theta> x) = base_term (the (max_raise_list ?ts))"
            unfolding \<Theta>_def x by auto
          also have "\<dots> = \<sigma> x" unfolding res using u by auto
          finally show "base_term (\<Theta> x) = \<sigma> x" .
        qed
        finally show ?goal by blast
      qed (auto simp: \<Theta>_def len)
    qed
  qed
  then show ?thesis using assms by blast
qed
end

lemma rel_rsteps_imp_rel_raise_steps: 
  assumes  var_cond:  "\<And> l r. (l,r) \<in> R \<union> S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and steps: "(s,t) \<in> (relto (rstep R) (rstep S))^^n"
  and base: "base_term s' = s"
  shows "(\<exists> t'. base_term t' = t \<and> (s',t') \<in> (relto (raise_step (cover ffR relR R)) (raise_step (cover ffS relS S)))^^n)"
  by (rule simulate_conditional_relative_steps_count[of "\<lambda> s t. base_term t = s", 
    OF rstep_imp_raise_step[OF var_cond] rstep_imp_raise_step[OF var_cond] steps base], blast+)

lemma max_raise_map_vars: fixes vw defines "av \<equiv> map_vars_term vw"
  assumes g: "ground s" "ground t"
  and r: "max_raise (av s, av t) = Some u"
  shows "\<exists> v. max_raise (s,t) = Some v \<and> ground v \<and> u = av v" 
  using g r
proof (induct s arbitrary: t u)
  case (Fun fl ss ftt u)
  obtain f l where fl: "fl = (f,l)" by force
  from Fun(3) obtain fl' ts where ftt: "ftt = Fun fl' ts" by (cases ftt, auto)
  obtain g l' where fl': "fl' = (g,l')" by force
  note res = Fun(4)[unfolded fl ftt fl' av_def, simplified, folded av_def]
  from res have gf: "g = f" and len: "length ss = length ts" by (auto split: bind_splits)
  define z where "z = zip (map av ss) (map av ts)"
  from len have lenz: "length z = length ts" unfolding z_def by simp
  from res obtain us where Some: "mapM max_raise z = Some us"
    and u: "u = Fun (g, max l l') us" unfolding z_def by (auto split: bind_splits)
  from mapM_Some[OF Some] have lenus: "length us = length ts" using lenz by simp
  let ?p = "\<lambda> i v. max_raise (ss ! i, ts ! i) = Some v \<and> us ! i = av v \<and> ground v \<and> max_raise (z ! i) = Some (av v)"
  {
    fix i
    assume i: "i < length ts"
    with lenz have "i < length z" by simp
    from mapM_Some_idx[OF Some this] obtain y where res: "max_raise (z ! i) = Some y" and us: "us ! i = y"
      by auto
    from i len have mem: "ss ! i \<in> set ss" and "ts ! i \<in> set ts" by auto
    with Fun(2-3)[unfolded ftt] have g: "ground (ss ! i)" "ground (ts ! i)" by auto
    from i len have "z ! i = (av (ss ! i), av (ts ! i))" unfolding z_def by auto
    from Fun(1)[OF mem g res[unfolded this]] res us have 
      "\<exists> v. ?p i v" by auto
  }
  then have "\<forall> i. \<exists> v. i < length ts \<longrightarrow> ?p i v" by blast
  from choice[OF this] obtain vs where IH: "\<And> i. i < length ts \<Longrightarrow> ?p i (vs i)" by blast
  let ?vs = "map vs [0 ..< length ts]"
  have us: "us = map (av \<circ> vs) [0..<length ts]"
    by (rule nth_equalityI, insert len lenus IH, auto)
  have "mapM max_raise (zip ss ts) = Some (map (\<lambda>x. the (max_raise x)) (zip ss ts))" 
    unfolding mapM_map set_zip len using IH by auto
  also have "map (\<lambda>x. the (max_raise x)) (zip ss ts) = ?vs"
    by (rule nth_equalityI, insert IH, auto simp: len)
  finally show ?case unfolding fl ftt fl' gf u
    by (intro exI[of _ "Fun (f, max l l') ?vs"], insert IH, simp add: len av_def us)
qed simp

lemma max_raise_list_map_vars:
  fixes vw
  defines "av \<equiv> map_vars_term vw"
  assumes g: "Ball (set sss) ground"
  and r: "max_raise_list (map av sss) = Some u"
  and s: "set sss \<noteq> {}"
  shows "\<exists> v. max_raise_list sss = Some v \<and> u = av v"
  using g r s
proof (induct sss rule: max_raise_list.induct)
  case (3 s t ss)
  from 3(2) have gs: "ground s" and gt: "ground t" by auto
  note r = 3(3)
  from r obtain u1 where mra: "max_raise (av s, av t) = Some u1" by (auto split: bind_splits)
  from max_raise_map_vars[OF gs gt mra[unfolded av_def]] obtain v1 where mr: "max_raise (s,t) = Some v1" and gv1: "ground v1" 
    and u1: "u1 = av v1" unfolding av_def by blast
  from r mra u1 have res: "max_raise_list (map av (v1 # ss)) = Some u" by simp
  from gv1 3(2) have "Ball (set (v1 # ss)) ground" by auto
  from 3(1)[OF mr this res] show ?case using mr by auto
qed auto
  
(* important direction of remark after Def. 11 in IC 09 *)
lemma left_bounded_raise_step_imp_rstep: assumes ll: "left_linear_trs R"
  shows "(s,t) \<in> raise_step R \<Longrightarrow> (s,t) \<in> rstep R"
proof (induct rule: raise_step.induct)
  case (raise_step l r C xs ss \<Theta> D)
  from raise_step(1) have lr: "(l,r) \<in> R" .
  from ll lr have l: "linear_term l" unfolding left_linear_trs_def by auto
  from split_vars_eqf_subst[of l \<Theta>, unfolded raise_step(2)] 
  have eqf: "l \<cdot> \<Theta> =\<^sub>f (C, map \<Theta> xs)" by auto
  from split_vars_vars_term_list[of l, unfolded raise_step(2)] have xs: "xs = vars_term_list l" by auto
  from raise_step(3) have len: "length ss = length xs" by auto
  from rstepI[OF lr refl refl] have "(D \<langle> l \<cdot> \<Theta> \<rangle>, D \<langle>r \<cdot> \<Theta> \<rangle>) \<in> rstep R" by auto
  also have "l \<cdot> \<Theta> = fill_holes C (map \<Theta> xs)" using eqfE[OF eqf] by auto
  also have "map \<Theta> xs = ss" 
  proof (rule nth_equalityI, unfold length_map, simp add: len)
    fix i
    assume i: "i < length xs"    
    then have mem: "xs ! i \<in> set xs" by auto
    with xs have cond: "xs ! i \<in> vars_term l" by auto
    let ?fxs = "filter ((=) (xs ! i)) xs"
    from linear_vars_term_list[OF l, folded xs, of "xs ! i"]
    have "length ?fxs \<le> 1" .
    moreover from mem have "xs ! i \<in> set ?fxs" by auto
    ultimately have fxs: "?fxs = [xs ! i]" by (cases ?fxs, auto)
    let ?zip = "[(si, xi)\<leftarrow>zip ss xs . xi = xs ! i]"
    from i len have mem: "(ss ! i, xs ! i) \<in> set ?zip" unfolding set_filter set_zip by auto
    from i have "map \<Theta> xs ! i = \<Theta> (xs ! i)" by simp
    also have "\<dots> = the (max_raise_list (map fst ?zip))" unfolding raise_step(5) using cond by auto
    also have "?zip = [(ss ! i, xs ! i)]" 
    proof (cases ?zip)
      case Nil
      with mem show ?thesis by auto
    next
      case (Cons sx1 zs) note oCons = this
      show ?thesis
      proof (cases zs)
        case Nil
        with Cons mem show ?thesis by auto
      next
        case (Cons xs2 zs')
        define x where "x = xs ! i"
        from arg_cong[OF oCons[unfolded Cons], of "\<lambda> l. length (map snd l)"] 
        have "2 \<le> length (map snd ?zip)" by auto
        also have "map snd ?zip = ?fxs" using len unfolding x_def[symmetric]
        proof (induct xs arbitrary: ss)
          case (Cons y ys sss)
          from Cons(2) obtain a ss where sss: "sss = a # ss" and len: "length ss = length ys" by (cases sss, auto)
          from Cons(1)[OF len] show ?case unfolding sss by auto
        qed auto
        finally show ?thesis unfolding fxs by simp
      qed
    qed 
    finally show "map \<Theta> xs ! i = ss ! i" by simp
  qed  
  finally show ?case .
qed

definition rstep_bounded :: "nat \<Rightarrow> ('f \<times> nat,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "rstep_bounded c R L \<equiv> \<forall> s t f n. s \<in> lift_term 0 ` L \<longrightarrow> (s,t) \<in> (rstep R)^* \<longrightarrow> (f,n) \<in> funas_term t \<longrightarrow> height f \<le> c"

definition raise_step_bounded :: "nat \<Rightarrow> ('f \<times> nat,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "raise_step_bounded c R L \<equiv> \<forall> s t f n. s \<in> lift_term 0 ` L \<longrightarrow> (s,t) \<in> (raise_step R)^* \<longrightarrow> (f,n) \<in> funas_term t \<longrightarrow> height f \<le> c"

definition e_bounded :: "(('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "e_bounded e c R \<equiv> rstep_bounded c (cover e Strict_TRS R)"

definition e_raise_bounded :: "(('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "e_raise_bounded e c R \<equiv> raise_step_bounded c (cover e Strict_TRS R)"

fun weak_kind_condition :: "nat \<Rightarrow> nat option \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "weak_kind_condition c None R = True"
| "weak_kind_condition c (Some c') R = (c = c' \<and> non_collapsing R)"
 
definition match_rel_bounded :: "nat \<Rightarrow> nat option \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "match_rel_bounded c c_opt R S \<equiv> rstep_bounded c (cover match Strict_TRS R \<union> cover match (Weak_TRS c_opt) S)"

definition match_raise_rel_bounded :: "nat \<Rightarrow> nat option \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "match_raise_rel_bounded c c_opt R S \<equiv> raise_step_bounded c (cover match Strict_TRS R \<union> cover match (Weak_TRS c_opt) S)"

lemmas bounded_defs = 
  rstep_bounded_def 
  raise_step_bounded_def
  e_bounded_def
  e_raise_bounded_def
  match_rel_bounded_def
  match_raise_rel_bounded_def

lemma rstep_bounded_left_linear_imp_raise_bounded: assumes bounded: "rstep_bounded c R L" and ll: "left_linear_trs R"
  shows "raise_step_bounded c R L" unfolding bounded_defs
proof (intro allI impI)
  fix s t f n
  assume L: "s \<in> lift_term 0 ` L"
  and steps: "(s,t) \<in> (raise_step R)^*"
  and fn: "(f,n) \<in> funas_term t"
  from left_bounded_raise_step_imp_rstep[OF ll]
  have subset: "raise_step R \<subseteq> rstep R" by auto
  show "height f \<le> c" 
    by (rule bounded[unfolded bounded_defs, rule_format, OF L _ fn], insert steps rtrancl_mono[OF subset], auto)
qed

lemma e_bounded_left_linear_imp_e_raise_bounded: assumes bounded: "e_bounded e c R L" and 
  ll: "left_linear_trs R" 
  shows "e_raise_bounded e c R L" 
  using bounded unfolding e_raise_bounded_def e_bounded_def
  by (rule rstep_bounded_left_linear_imp_raise_bounded[OF _ cover_left_linear[OF ll]]) 

lemma match_rel_bounded_left_linear_imp_raise_bounded: assumes bounded: "match_rel_bounded c c_opt R S L" and 
  ll: "left_linear_trs R" "left_linear_trs S"
  shows "match_raise_rel_bounded c c_opt R S L" 
  using bounded unfolding match_raise_rel_bounded_def match_rel_bounded_def
  by (rule rstep_bounded_left_linear_imp_raise_bounded,
  insert cover_left_linear[OF ll(1), of match Strict_TRS] 
  cover_left_linear[OF ll(2), of match "Weak_TRS c_opt"], 
  auto simp: left_linear_trs_def)

context
begin
private fun seq_gen :: "(('g,'v)term \<Rightarrow> ('f,'v)term) \<Rightarrow> ('f,'v)trs \<Rightarrow> (('f,'v)term \<Rightarrow> ('g,'v)term) \<Rightarrow> (nat \<Rightarrow> ('g,'v)term) \<Rightarrow> nat \<Rightarrow> ('f,'v)term" where 
  "seq_gen l R b ts 0 = l (ts 0)"
| "seq_gen l R b ts (Suc i) = (SOME t. (seq_gen l R b ts i, t) \<in> R \<and> b t = ts (Suc i))"

(* Thm 13. in IC 09, not instantiated to specific enrichments e *)
lemma e_raise_bounded: assumes var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and lSN: "locally_terminating (cover e Strict_TRS R \<union> raise)"
  and R: "finite R"
  and F: "finite F"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and bounded: "e_raise_bounded e c R L"
  shows "SN_on (rstep R) L"
proof 
  fix ts
  assume start: "ts 0 \<in> L" and ssteps: "\<forall> i. (ts i, ts (Suc i)) \<in> rstep R"
  then have steps: "\<And> i. (ts i, ts (Suc i)) \<in> rstep R" by auto
  let ?rel = "raise_step (cover e Strict_TRS R)"
  let ?seq = "seq_gen (lift_term 0) ?rel base_term ts"
  define ss where "ss = ?seq" 
  {
    fix i
    have "base_term (?seq i) = ts i \<and> (i > 0 \<longrightarrow> (?seq (i - 1), ?seq i) \<in> ?rel)"
    proof (induct i)
      case 0
      show ?case unfolding seq_gen.simps base_lift by auto
    next
      case (Suc i)
      define s where "s = ?seq i"
      from Suc have base: "base_term s = ts i" unfolding s_def by blast
      have id: "\<And> x. (0 < Suc i \<longrightarrow> x) = x" "Suc i - 1 = i" by auto
      let ?p = "\<lambda> t'. (s, t') \<in> ?rel \<and> base_term t' = ts (Suc i)"
      from rstep_imp_raise_step[OF var_cond steps base, of e]
        obtain t' where *: "?p t'" by auto
      from someI[of ?p t', OF this] have "?p (SOME t'. ?p t')" .
      then show ?case unfolding seq_gen.simps id s_def[symmetric] by auto
    qed    
  } note steps = this[folded ss_def]  
  {
    fix i
    have "(ss i, ss (Suc i)) \<in> ?rel" "base_term (ss i) = ts i" using steps[of "Suc i"] steps[of i] by auto
  } note steps = this
  let ?G = "funas_trs R \<union> F"
  define GG where "GG = ?G"
  define G where "G ={((f,l),n) | f l n. (f,n) \<in> ?G \<and> l \<le> c}"
  let ?rell = "(sig_step G (rstep raise))^* O sig_step G (rstep (cover e Strict_TRS R))"
  let ?relll = "sig_step G (rstep (cover e Strict_TRS R \<union> raise))"
  from R have "finite (funas_trs R)" by (rule finite_funas_trs)
  then have "finite (GG \<times> {l. l \<le> c})" using F unfolding GG_def by auto
  note fin = finite_imageI[OF this, of "\<lambda> ((f,n),l). ((f,l),n)"]
  have G: "finite G" unfolding G_def GG_def[symmetric] 
    by (rule HOL.subst[of _ _ finite, OF _ fin], force)
  {
    fix i 
    have steps': "(ss 0, ss i) \<in> ?rel^*"
    proof (induct i)
      case (Suc i)
      then show ?case using steps[of i] by auto
    qed auto
    have "ss 0 = lift_term 0 (ts 0)" unfolding ss_def by simp 
    with start have ss0: "ss 0 \<in> lift_term 0 ` L" by auto
    from bounded[unfolded bounded_defs, rule_format, OF ss0 steps']
    have limit: "\<And> f n. (f,n) \<in> funas_term (ss i) \<Longrightarrow> height f \<le> c" by auto
    {
      fix fhn
      assume mem: "fhn \<in> funas_term (ss i)"
      obtain f h n where f: "fhn = ((f,h),n)" by (cases fhn, auto)
      note mem = mem[unfolded f]
      have "fhn \<in> G" unfolding G_def
      proof(rule, intro exI conjI, rule f)
        from limit[OF mem] show "h \<le> c" by simp
      next
        from mem have "(f,n) \<in> funas_term (ts i)" 
          unfolding steps(2)[symmetric]
          unfolding funas_term_map_funs_term by force
        also have "funas_term (ts i) \<subseteq> ?G"
        proof (induct i)
          case 0
          with start L show ?case by auto
        next
          case (Suc i)
          show ?case 
            by (rule rstep_preserves_funas_terms_var_cond[OF _ Suc \<open>(ts i, ts (Suc i)) \<in> rstep R\<close> var_cond], auto)
        qed
        finally show "(f,n) \<in> ?G" .
      qed
    }
    then have "funas_term (ss i) \<subseteq> G" by auto    
  } note limit = this 
  {
    fix i
    from steps(1)[of i] limit[of i] limit[of "Suc i"]
    have "(ss i, ss (Suc i)) \<in> sig_step G (raise_step (cover e Strict_TRS R))" by auto
  } note steps = this
  {
    fix i
    have "(ss i, ss (Suc i)) \<in> ?rell"
      by (rule sig_raise_step_imp_sig_steps[OF _ steps], unfold G_def, auto)
    also have "?rell \<subseteq> (sig_step G (rstep (cover e Strict_TRS R)) \<union> sig_step G (rstep raise))^+" by regexp
    also have "sig_step G (rstep (cover e Strict_TRS R)) \<union> sig_step G (rstep raise) = ?relll"
    unfolding sig_step_def rstep_union by auto
    finally have "(ss i, ss (Suc i)) \<in> ?relll^+" .
  } note steps = this
  from lSN[unfolded locally_terminating_def, rule_format, OF G] 
  have SN: "SN ?relll" .
  then have "SN (?relll^+)" by (rule SN_imp_SN_trancl)
  with steps
  show False by auto
qed
end

lemma match_raise_bounded_linear_complexity_rel_main: assumes wf: "wf_trs (R \<union> S)" 
  and R: "finite (R \<union> S)"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and non_duplicating: "\<And> l r. (l,r) \<in> R \<union> S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and c_opt: "weak_kind_condition c c_opt R"
  and bounded: "match_raise_rel_bounded c c_opt R S L"
  shows "\<exists> c. \<forall> n s t. s \<in> L \<longrightarrow> (s, t) \<in> (relto (rstep R) (rstep S)) ^^ n \<longrightarrow> n \<le> term_size s * c"
proof -
  from wf have var_cond: "\<And> l r. (l,r) \<in> R \<union> S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  let ?G = "funas_trs (R \<union> S) \<union> F"
  define GG where "GG = ?G"
  define G where "G ={((f,l),n) | f l n. (f,n) \<in> ?G \<and> l \<le> c}"
  let ?RS = "relto (rstep R) (rstep S)"
  let ?CRS = "cover match Strict_TRS R \<union> cover match (Weak_TRS c_opt) S"
  let ?rel = "relto (raise_step (cover match Strict_TRS R)) (raise_step (cover match (Weak_TRS c_opt) S))"
  let ?rell = "relto (sig_step G (raise_step (cover match Strict_TRS R))) (sig_step G (raise_step (cover match (Weak_TRS c_opt) S)))"
  let ?rel3 = "relto (sig_step G (rstep (cover match Strict_TRS R))) (sig_step G (rstep (raise \<union> cover match (Weak_TRS c_opt) S)))"
  {
    fix s t
    assume "(s,t) \<in> ?rell"
    from sig_rel_raise_step_imp_sig_steps[of G _ _ "cover match (Weak_TRS c_opt) S" "cover match Strict_TRS R", OF _ this]
    have "(s,t) \<in> ?rel3" unfolding G_def by auto
  }
  then have rel3: "?rell \<subseteq> ?rel3" by blast
  from R have "finite (funas_trs (R \<union> S))" by (rule finite_funas_trs)
  from finite_list[OF R] obtain RS where RS: "R \<union> S = set RS" by auto
  let ?fs = "map (\<lambda> (l,r). length (funas_term_list r)) RS"
  define k where "k = Suc (max_list ?fs)"
  have k2: "\<And> l r. (l,r) \<in> R \<union> S \<Longrightarrow> length (funas_term_list r) \<le> k" unfolding RS k_def using max_list[of _ ?fs] by force
  have k1: "1 \<le> k" unfolding k_def by simp
  have cc: "\<And> f n. (f,n) \<in> G \<Longrightarrow> height f \<le> c" unfolding G_def by force
  show ?thesis
  proof (rule exI[of _ "Suc k ^ c"], intro allI impI)
    fix n s t 
    assume start: "s \<in> L" and st: "(s,t) \<in> ?RS^^n"
    let ?s = "lift_term 0 s"
    have base: "base_term ?s = s" by (simp add: base_lift)
    from rel_rsteps_imp_rel_raise_steps[OF var_cond st base] obtain lt where steps: "(?s,lt) \<in> ?rel^^n" by blast
    have start: "?s \<in> lift_term 0 ` L" using start by auto
    have "(?s,lt) \<in> ?rell^^n" 
    proof (rule abstract_closure_twice.AA_steps_imp_BB_steps[OF _ start steps, of _ "raise_step ?CRS" "\<lambda> t. funas_term t \<subseteq> G"],
      unfold_locales) 
      fix ls lt
      assume ls: "ls \<in> lift_term 0 ` L" and steps: "(ls,lt) \<in> (raise_step ?CRS)^*" 
      from bounded[unfolded bounded_defs, rule_format, OF this]
      have height: "\<And> f n. (f,n) \<in> funas_term lt \<Longrightarrow> height f \<le> c" .
      from raise_steps_covers_imp_rsteps[OF steps] have steps: "(base_term ls, base_term lt) \<in> (rstep (R \<union> S))^*" .
      from ls L have "funas_term (base_term ls) \<subseteq> ?G" by (force simp: base_lift)
      from rsteps_preserve_funas_terms[OF _ this steps wf] have G: "funas_term (base_term lt) \<subseteq> ?G" by auto
      from height G[unfolded funas_term_map_funs_term]
      show "funas_term lt \<subseteq> G" unfolding G_def by force
    qed (auto simp: raise_step_union)
    with relpow_mono[OF rel3] have steps: "(lift_term 0 s, lt) \<in> ?rel3^^n" by blast
    from c_opt have "non_collapsing R \<and> c_opt = Some c \<or> c_opt = None" by (cases c_opt, auto)
    from sig_match_raise_rel_linear_bound[OF wf non_duplicating cc k2 k1 steps _ _ this]
    show "n \<le> term_size s * Suc k ^ c" by simp
  qed
qed

fun stackable_of_cm where
  "stackable_of_cm (Derivational_Complexity F) = F"
| "stackable_of_cm (Runtime_Complexity C D) = C"

fun roots_of_cm where
  "roots_of_cm (Derivational_Complexity F) = F"
| "roots_of_cm (Runtime_Complexity C D) = D"

definition ground_terms_of :: "'f sig \<Rightarrow> 'f sig \<Rightarrow> ('f,'v)term set" where
  "ground_terms_of H R = {s . \<Union> (funas_term ` set (args s)) \<subseteq> H \<and> the (root s) \<in> R \<and> ground s}"

lemma ground_terms_ofI: assumes stackH: "set (stackable_of_cm cm) \<subseteq> H"
  and conH: "(con,0) \<in> H"
  and ft: "is_Fun t"
  and tcm: "t \<in> terms_of cm"
  and R: "set (roots_of_cm cm) \<subseteq> R"
  shows "t \<cdot> (\<lambda> _. Fun con []) \<in> ground_terms_of H R" (is "t \<cdot> ?\<sigma> \<in> ?L")
proof -
  from ft obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from t tcm R have root: "the (root (t \<cdot> ?\<sigma>)) \<in> R" by (cases cm, auto)
  from tcm stackH have "\<Union> (funas_term ` set (args t)) \<subseteq> H" unfolding t
    by (cases cm) (auto simp: funas_args_term_def)
  with conH have "\<Union> (funas_term ` set (args (t \<cdot> ?\<sigma>))) \<subseteq> H" unfolding t
    by (auto simp: funas_term_subst split: if_splits)
  moreover have "ground (t \<cdot> ?\<sigma>)" by simp
  ultimately show "t \<cdot> ?\<sigma> \<in> ?L" using root unfolding ground_terms_of_def by auto
qed

lemma match_raise_bounded_linear_complexity_rel: 
  fixes R S :: "('f,'v)trs"
  assumes wf: "wf_trs (R \<union> S)" 
  and R: "finite (R \<union> S)"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and HL: "ground_terms_of H H' \<subseteq> L"
  and stackH: "set (stackable_of_cm cm) \<subseteq> H"
  and rootsH': "set (roots_of_cm cm) \<subseteq> H'"
  and conH: "(con,0) \<in> H"
  and c_opt: "weak_kind_condition c c_opt R"
  and non_duplicating: "\<And> l r. (l,r) \<in> R \<union> S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and bounded: "match_raise_rel_bounded c c_opt R S L"
  shows "deriv_bound_measure_class (relto (rstep R) (rstep S)) cm (Comp_Poly 1)"
proof -
  let ?RS = "relto (rstep R) (rstep S)"
  from match_raise_bounded_linear_complexity_rel_main[OF wf R L non_duplicating c_opt bounded] obtain c 
  where lin: "\<And> n s t.  s \<in> L \<Longrightarrow> (s, t) \<in> ?RS^^ n \<Longrightarrow> n \<le> term_size s * c" by blast
  show ?thesis unfolding deriv_bound_measure_class_def
  proof (rule)
    fix n and t :: "('f,'v)term"
    assume tcm: "t \<in> terms_of_nat cm n"
    then have tn: "term_size t \<le> n" by (cases cm, auto)
    have "deriv_bound ?RS t (n * c)" unfolding deriv_bound_def
    proof (rule, elim exE)
      fix s
      let ?\<sigma> = "(\<lambda> _. Fun con []) :: ('f,'v)subst"
      assume *: "(t, s) \<in> ?RS ^^ Suc (n * c)"
      have seq: "(t \<cdot> ?\<sigma>, s \<cdot> ?\<sigma>) \<in> ?RS ^^ Suc (n * c)"
        by (rule relpow_image[OF _ *], insert subst.closedD[OF subst_closed_rel_rstep[of "(R,S)"], of _ _ ?\<sigma>], simp)
      from relpow_Suc_E2[OF *] obtain u where "(t,u) \<in> ?RS" by metis
      then have "(t,u) \<in> (rstep (R \<union> S))^+" unfolding rstep_union by regexp
      then obtain u where "(t,u) \<in> rstep (R \<union> S)" by (rule converse_tranclE)
      with NF_Var[OF wf, of _ u] have tf: "is_Fun t" by (cases t, auto)
      from tcm have "t \<in> terms_of cm" unfolding terms_of by auto
      from ground_terms_ofI[OF stackH conH tf this rootsH'] HL
      have "t \<cdot> ?\<sigma> \<in> L" by auto
      from lin[OF this seq] have "Suc (n * c) \<le> term_size t * c" by simp
      also have "\<dots> \<le> n * c" using tn by auto
      finally show False by simp
    qed
    then show "deriv_bound ?RS t (c * n ^ 1 + 0)" by (simp add: ac_simps)
  qed
qed

lemma match_raise_bounded_linear_complexity: 
  fixes R :: "('f,'v)trs"
  assumes wf: "wf_trs R" 
  and R: "finite R"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and HL: "ground_terms_of H H' \<subseteq> L"
  and stackH: "set (stackable_of_cm cm) \<subseteq> H"
  and rootsH': "set (roots_of_cm cm) \<subseteq> H'"
  and conH: "(con,0) \<in> H"
  and non_duplicating: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and bounded: "e_raise_bounded match c R L"
  shows "deriv_bound_measure_class (rstep R) cm (Comp_Poly 1)"
proof -
  have Rempty: "R \<union> {} = R" "relto (rstep R) (rstep {}) = rstep R" by auto
  show ?thesis
  proof (rule match_raise_bounded_linear_complexity_rel[of R "{}", unfolded Rempty, OF wf R L HL stackH rootsH' conH _ non_duplicating])
    show "match_raise_rel_bounded c None R {} L" using bounded 
      unfolding match_raise_rel_bounded_def e_raise_bounded_def by simp
  qed auto
qed

(* 
   getting e_bounded_ness criterion of Geser et. al via left-linearity 
   (adding raise to local termination does not harm, since known enrichments can cope with raise rules)
 *)
lemma e_bounded:
  assumes var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and SN: "locally_terminating (cover e Strict_TRS R \<union> raise)"
  and R: "finite R"
  and F: "finite F"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and ll: "left_linear_trs R"
  and bounded: "e_bounded e c R L"
  shows "SN_on (rstep R) L"
proof -
  from e_raise_bounded[OF var_cond SN R F L e_bounded_left_linear_imp_e_raise_bounded[OF bounded ll]]
  show ?thesis .
qed

lemma match_raise_bounded_SN_on: 
  assumes wf: "wf_trs R" 
  and R: "finite R"
  and F: "finite F"
  and L: "\<Union>(funas_term ` L) \<subseteq> F"
  and non_duplicating: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and bounded: "e_raise_bounded match c R L"
  shows "SN_on (rstep R) L"
  by (rule e_raise_bounded[OF _ match_raise_locally_SN[OF wf non_duplicating R] R F L bounded],
  insert wf, auto simp: wf_trs_def)

hide_const (open) match
hide_const (open) roof
hide_const (open) raise

end
