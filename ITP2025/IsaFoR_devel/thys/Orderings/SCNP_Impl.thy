(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory SCNP_Impl
imports
  SCNP
  Term_Order_Impl
  Weighted_Path_Order.List_Order
  Auxx.Map_Choice
  First_Order_Rewriting.Trs_Impl
begin

type_synonym 'f scnp_af = "(('f \<times> nat) \<times> (nat \<times> nat) list) list"

lemma check_scnp_af:
  assumes rt: "compat_redpair_order S NS"
    and af: "af_compatible \<pi> NS" 
    and ext: "list_order_extension s_ext ns_ext"
  shows "af_scnp S NS s_ext ns_ext \<pi>"
proof -
  from rt interpret compat_redpair_order S NS .
  from ext interpret list_order_extension s_ext ns_ext .
  show ?thesis by (unfold_locales, rule af)
qed

definition scnp_desc :: "('f :: showl) scnp_af \<Rightarrow> showsl \<Rightarrow> showsl"
where
  "scnp_desc af mu =
    showsl_lit (STR ''SCNP-version with mu = '') \<circ> mu \<circ> showsl_lit (STR '' and the level mapping defined by\<newline>'') \<circ>
    showsl_sep (\<lambda>((f, n), as). showsl_lit (STR ''pi('') \<circ> showsl f \<circ> showsl_lit (STR '') = '') \<circ> 
      default_showsl_list (\<lambda> (p, l).
        showsl_lit (STR ''('') \<circ> (if p < n then showsl (Suc p) else showsl_lit (STR ''epsilon'')) \<circ>
        showsl_lit (STR '','') \<circ> showsl l \<circ> showsl_lit (STR '')'')) as)
      showsl_nl af \<circ> showsl_nl"

definition scnp_arity :: "'f scnp_af \<Rightarrow> nat" 
where
  "scnp_arity af = max_list (map (\<lambda> (fi,ijs). length ijs) af)"

definition label_s_ns_impl :: "(('f :: showl, 'v :: showl)rule \<Rightarrow> showsl check)
  \<Rightarrow> (('f, 'v)rule \<Rightarrow> showsl check) \<Rightarrow> ('f,'v)term \<times> nat
  \<Rightarrow> ('f,'v)term \<times> nat \<Rightarrow> bool \<times> bool"
  where "label_s_ns_impl cS cNS s t \<equiv> case s of (s',i) \<Rightarrow> case t of (t',j) \<Rightarrow> 
            if isOK(cS (s',t')) then (True,True) else 
            if isOK(cNS (s',t')) then (i > j, i \<ge> j) else (False, False)"

abbreviation fun_to_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a rel" where
  "fun_to_rel f \<equiv> {(a,b). f a b}"

lemma label_s_impl: assumes "isOK(cS (s,t)) \<Longrightarrow> S s t"
  and "isOK(cNS (s,t)) \<Longrightarrow> NS s t"
  and "fst (label_s_ns_impl cS cNS (s,i) (t,j))"
  shows "((s,i), (t,j)) \<in> lex_two (fun_to_rel S) (fun_to_rel NS) (fun_to_rel (>))" 
  using assms unfolding label_s_ns_impl_def split 
  by (cases "isOK(cS (s,t))", simp, cases "isOK(cNS (s,t))", auto)

lemma label_ns_impl: assumes "isOK(cS (s,t)) \<Longrightarrow> S s t"
  and "isOK(cNS (s,t)) \<Longrightarrow> NS s t"
  and "snd (label_s_ns_impl cS cNS (s,i) (t,j))"
  shows "((s,i), (t,j)) \<in> lex_two (fun_to_rel S) (fun_to_rel NS) (fun_to_rel (\<ge>))" 
  using assms unfolding label_s_ns_impl_def split 
  by (cases "isOK(cS (s,t))", simp, cases "isOK(cNS (s,t))", auto)

definition NST_label_mul_impl :: "(('f,'v)term \<times> nat) list_ext_impl 
  \<Rightarrow> (('f \<times> nat) \<Rightarrow> (nat \<times> nat)list)
  \<Rightarrow> (('f, 'v)rule \<Rightarrow> showsl check) 
  \<Rightarrow> (('f, 'v)rule \<Rightarrow> showsl check)
  \<Rightarrow> ('f :: showl ,'v :: showl)rule \<Rightarrow> showsl check"
  where "NST_label_mul_impl list_ext af cS cNS st \<equiv>
  case st of (Fun f ss, Fun g ts) \<Rightarrow> check (snd (list_ext (label_s_ns_impl cS cNS) (lterms af (Fun f ss)) (lterms af (Fun g ts)))) 
      (showsl (STR ''cannot orient pair '') \<circ> showsl_rule st \<circ> showsl (STR '' weakly:\<newline>'')
       \<circ> showsl_list (lterms af (Fun f ss)) \<circ> showsl (STR '' >=mu '') \<circ> showsl_list (lterms af (Fun g ts)) 
       \<circ> showsl (STR '' could not be ensured''))
  | _ \<Rightarrow> error (showsl (STR ''roots of '') \<circ> showsl_rule st \<circ> showsl (STR '' must be non-variable''))"

definition S_label_mul_impl :: "(('f,'v)term \<times> nat) list_ext_impl
  \<Rightarrow> (('f \<times> nat) \<Rightarrow> (nat \<times> nat)list)
  \<Rightarrow> (('f, 'v)rule \<Rightarrow> showsl check) 
  \<Rightarrow> (('f, 'v)rule \<Rightarrow> showsl check)
  \<Rightarrow> ('f :: showl ,'v :: showl)rule \<Rightarrow> showsl check"
  where "S_label_mul_impl list_ext af cS cNS st \<equiv>
  case st of (Fun f ss, Fun g ts) \<Rightarrow> check (fst (list_ext (label_s_ns_impl cS cNS) (lterms af (Fun f ss)) (lterms af (Fun g ts)))) 
      (showsl_lit (STR ''cannot orient pair '') \<circ> showsl_rule st \<circ> showsl_lit (STR '' strictly:\<newline>'') 
       \<circ> showsl_list (lterms af (Fun f ss)) \<circ> showsl_lit (STR '' >mu '') \<circ> showsl_list (lterms af (Fun g ts)) \<circ> showsl_lit (STR '' could not be ensured''))
  | _ \<Rightarrow> error (showsl_lit (STR ''roots of '') \<circ> showsl_rule st \<circ> showsl_lit (STR '' must be non-variable''))"


definition generate_scnp_rp :: "(('f,'v)term \<times> nat) list_ext_impl \<Rightarrow> showsl \<Rightarrow> 'f scnp_af \<Rightarrow> 
  ('f :: {compare_order,showl},'v :: showl)rel_impl \<Rightarrow> ('f,'v)rel_impl"
  where "generate_scnp_rp list_ext list_ext_name af rt \<equiv> 
     let af' = fun_of_map (ceta_map_of af) [];
         pi = rel_impl.af rt;
         cS = rel_impl.s rt;
         cNS = rel_impl.ns rt
       in \<lparr> 
   rel_impl.valid = rel_impl_redpair rt, 
   standard = error (showsl_lit (STR ''SCNP does not satisfy standard requirements such as S subset NS'')),
   desc = scnp_desc af list_ext_name \<circ> rel_impl.desc rt,
   s = S_label_mul_impl list_ext af' cS cNS, 
   ns = rel_impl.ns rt, 
   nst = NST_label_mul_impl list_ext af' cS cNS, 
   af = pi, 
   top_af = scnp_af_to_af af' pi,
   SN = succeed,
   subst_s = succeed,
   ce_compat = rel_impl.ce_compat rt,
   co_rewr = error (showsl_lit (STR ''SCNP cannot be used as co-rewrite pair'')),
   top_mono = succeed,
   top_refl = error (showsl_lit (STR ''SCNP does not ensure top-non-strict refl.'')),
   mono_af = empty_af,
   mono = (\<lambda> _. error (showsl_lit (STR ''SCNP does not support strictly monotone orders''))),
   not_wst = None,
   not_sst = None,
   cpx = no_complexity_check\<rparr>"


lemma generate_scnp_rp: assumes rp: "rel_impl rp"
  and list_ext: "\<exists> s_ext ns_ext. list_order_extension_impl s_ext ns_ext list_ext"
shows "rel_impl (generate_scnp_rp list_ext list_ext_name af rp)"
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 all)
  let ?rp = "generate_scnp_rp list_ext list_ext_name af rp"
  let ?\<pi> = "rel_impl.af rp"
  let ?af = "fun_of_map (ceta_map_of af) []"
  from list_ext obtain s_ext ns_ext where "list_order_extension_impl s_ext ns_ext list_ext" by blast
  then interpret list_order_extension_impl s_ext ns_ext list_ext .
  have list_ext: "list_order_extension s_ext ns_ext" ..
  note gdef = generate_scnp_rp_def[of list_ext list_ext_name af rp, unfolded Let_def]
  note 1 = 1[unfolded gdef rel_impl_list, simplified]
  from 1 have v: "isOK(rel_impl_redpair rp)" by auto
  let ?cs = "rel_impl.s rp"
  let ?cns = "rel_impl.ns rp"
  let ?cS = "S_label_mul_impl list_ext ?af ?cs ?cns" 
  let ?cNST = "NST_label_mul_impl list_ext ?af ?cs ?cns" 
  let ?all = "(concat o concat) (map (\<lambda>(s,t). map (\<lambda> si. map (Pair si) (map fst (lterms ?af t ))) (map fst (lterms ?af s))) all)"
  let ?all' = "all @ ?all" 
  let ?ns = "filter (\<lambda> sitj. isOK(?cns sitj)) ?all'"  
  let ?s = "filter (\<lambda> sitj. isOK(?cs sitj)) ?all'" 
  have "isOK (check_allm ?cs ?s)" by auto
  hence S: "isOK (rel_impl_s rp ?s)" unfolding rel_impl_list by blast
  have "isOK (check_allm ?cns ?ns)" by auto
  hence NS: "isOK (rel_impl_ns rp ?ns)" unfolding rel_impl_list by blast
  from rel_impl_redpair[OF rp v S NS] obtain S NS 
    where redp: "compat_redpair_order S NS"
    and S: "set ?s \<subseteq> S"
    and NS: "set ?ns \<subseteq> NS" 
    and af: "af_compatible ?\<pi> NS" 
    and ce: "isOK(rel_impl.ce_compat rp) \<Longrightarrow> ce_compatible NS" 
    by blast
  have pi: "rel_impl.af ?rp = ?\<pi>" unfolding gdef by simp
  interpret compat_redpair_order S NS by fact
  interpret af_redpair S NS ?\<pi>
    by (unfold_locales, rule af)
  from check_scnp_af[OF redp af list_ext]
  interpret af_scnp S NS ?af s_ext ns_ext ?\<pi> .
  {
    fix f ss g ts si i tj j
    assume mem: "(Fun f ss,Fun g ts) \<in> set all" and
      mems: "(si,i) \<in> set (lterms ?af (Fun f ss))" and
      memt: "(tj,j) \<in> set (lterms ?af (Fun g ts))"
    have id: "(si,tj) = (si, fst (tj,j))" by simp
    have all: "(si,tj) \<in> set ?all" unfolding o_def set_concat set_map
      by (rule, rule, rule, rule mem, unfold set_map map_map o_def, rule, rule refl, rule mems, unfold set_map fst_conv, rule,
        rule id, rule memt)
    have "isOK(?cs (si,tj)) \<Longrightarrow> (si,tj) \<in> S" "isOK(?cns (si,tj)) \<Longrightarrow> (si,tj) \<in> NS" 
    proof -
      assume "isOK(?cs (si,tj))" with all have "(si,tj) \<in> set ?s" by auto
      with S show "(si,tj) \<in> S" by blast
    next
      assume "isOK(?cns (si,tj))" with all have "(si,tj) \<in> set ?ns" by auto
      with NS show "(si,tj) \<in> NS" by blast
    qed
  } note ok = this
  {
    fix f ss g ts
    assume mem: "(Fun f ss, Fun g ts) \<in> set all"
    have "set (lterms ?af (Fun f ss)) \<times> set (lterms ?af (Fun g ts)) \<inter>
      {(x,y). snd (label_s_ns_impl ?cs ?cns x y)} \<subseteq> label_ns"
    proof (clarify)
      fix si i tj j
      assume rel: "snd (label_s_ns_impl ?cs ?cns (si,i) (tj,j))" and
        mems: "(si,i) \<in> set (lterms ?af (Fun f ss))" and
        memt: "(tj,j) \<in> set (lterms ?af (Fun g ts))"
      have "((si,i),(tj,j)) \<in> lex_two (fun_to_rel (\<lambda> s t. (s,t) \<in> S)) (fun_to_rel (\<lambda> s t. (s,t) \<in> NS)) ge"
        by (rule label_ns_impl[OF _ _ rel])
         (rule ok[OF mem mems memt], simp)+
      then show "((si,i),(tj,j)) \<in> label_ns" unfolding label_ns_def by simp
    qed
  } note non_strict = this
  {
    fix f ss g ts
    assume mem: "(Fun f ss, Fun g ts) \<in> set all"
    have "set (lterms ?af (Fun f ss)) \<times> set (lterms ?af (Fun g ts)) \<inter>
      {(x,y). fst (label_s_ns_impl ?cs ?cns x y)} \<subseteq> label_s"
    proof (clarify)
      fix si i tj j
      assume rel: "fst (label_s_ns_impl ?cs ?cns (si,i) (tj,j))" and
        mems: "(si,i) \<in> set (lterms ?af (Fun f ss))" and
        memt: "(tj,j) \<in> set (lterms ?af (Fun g ts))"
      have "((si,i),(tj,j)) \<in> lex_two (fun_to_rel (\<lambda> s t. (s,t) \<in> S)) (fun_to_rel (\<lambda> s t. (s,t) \<in> NS)) gt"
        by (rule label_s_impl[OF _ _ rel], 
        (rule ok[OF mem mems memt], simp)+)
      then show "((si,i),(tj,j)) \<in> label_s" unfolding label_s_def by simp
    qed
  } note strict = this
  let ?pi' = "scnp_af_to_af (fun_of_map (ceta_map_of af) []) ?\<pi>"
  let ?S = "S_label_mul" 
  let ?NST = "NST_label_mul" 
  let ?NS = NS
  from af_scnp_mul  
  interpret scnp: af_root_redtriple_order ?S ?NS ?NST ?\<pi> ?pi' .    
  show ?case
    unfolding pi
    unfolding generate_scnp_rp_def Let_def rel_impl.simps
  proof (rule exI[of _ ?S], rule exI[of _ ?NS], rule exI[of _ ?NST], intro conjI impI allI
    ctxt_NS subst_NS scnp.subst_S scnp.SN trans_NS refl_NS scnp.subst_NST af_compat scnp.top_mono
    scnp.compat_NST empty_af scnp.af_compat' scnp.trans_NST scnp.trans_S
    )
    show "?S O ?NST \<subseteq> ?S" using scnp_mul by blast
    show "irrefl ?S" using scnp.SN unfolding irrefl_def by fast
    fix st
    assume stall: "st \<in> set all" 
    obtain s t where st: "st = (s,t)" by force
    from NS stall show "isOK (rel_impl.ns rp st) \<Longrightarrow> st \<in> NS" by auto
    {
      assume "isOK (S_label_mul_impl list_ext ?af ?cs ?cns st)" 
      note S' = this[unfolded S_label_mul_impl_def split st]
      from S' obtain f ss where s: "s = Fun f ss" by (cases s, auto)
      from S' obtain g ts where t: "t = Fun g ts" unfolding s by (cases t, auto)
      from S'[unfolded s t]
      have S': "fst (list_ext (label_s_ns_impl ?cs ?cns) (lterms ?af (Fun f ss)) (lterms ?af (Fun g ts)))" by simp
      note all = stall[unfolded st s t]
      show "st \<in> ?S" unfolding st s t S_label_mul_def
      proof (rule, intro exI conjI, rule refl)
        show "(lterms ?af (Fun f ss),
               lterms ?af (Fun g ts)) \<in> s_ext label_s label_ns"
          by (rule s_ext_local_mono, rule strict[OF all], rule non_strict[OF all], unfold list_ext_s, insert S', auto)
      qed
    }
    {
      assume "isOK(NST_label_mul_impl list_ext ?af ?cs ?cns st)" 
      note NST' = this[unfolded NST_label_mul_impl_def split st]
      from NST' obtain f ss where s: "s = Fun f ss" by (cases s, auto)
      from NST' obtain g ts where t: "t = Fun g ts" unfolding s by (cases t, auto)
      from NST'[unfolded s t]
      have NST': "snd (list_ext (label_s_ns_impl ?cs ?cns) (lterms ?af (Fun f ss)) (lterms ?af (Fun g ts)))" by simp
      note all = stall[unfolded st s t]
      show "st \<in> ?NST" unfolding st s t NST_label_mul_def
      proof (rule, intro exI conjI, rule refl)
        show "(lterms ?af (Fun f ss),
               lterms ?af (Fun g ts)) \<in> ns_ext label_s label_ns"
          by (rule ns_ext_local_mono, rule strict[OF all], rule non_strict[OF all], insert NST', unfold list_ext_ns, auto)
      qed
    }
  qed (auto intro: ce simp: no_complexity_check_def)
qed
end
