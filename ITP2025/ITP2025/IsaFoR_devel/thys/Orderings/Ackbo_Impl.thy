(*
Author:  Alexander Lochmann <alexander.lochmann@uibk.ac.at> (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Ackbo_Impl
  imports
    Ackbo_more
    Term_Order_Impl
    First_Order_Rewriting.Term_Impl
    Auxx.Multiset_Code
    Auxx.Map_Choice
    Weighted_Path_Order.Multiset_Extension2_Impl
begin

lemma test:
  assumes "x \<in># filter_fun (actop f (Fun f ts)) P n"
  and "length ts = 2"
shows "Fun f ts \<rhd> x"
  using assms Bin_cases[of "Fun f ts"] list_decomp_2
  by (auto simp add:  actop_mset_elem_subterm)


lemma test2:
  assumes "Fun f ts \<rhd> x"
shows "term_size x \<le> sum_list (map term_size ts)"
  using assms supt_term_size by force
  

locale weight_prec_ac =
  prec pr_strict +
  weight_fun w w0
  for w  :: "'f \<times> nat \<Rightarrow> nat"
    and w0 :: "nat"
    and pr_strict :: "('f \<times> nat) \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool" +
  fixes AC ::"'f set"
begin

function (sequential) ackbo_impl :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  [simp del]: "ackbo_impl s t =  
       (if (vars_term_ms t \<subseteq># vars_term_ms s \<and> weight t \<le> weight s)
        then if (weight t < weight s) then True
             else (case s of Var y \<Rightarrow> False
                   |Fun f ss \<Rightarrow> (case t of Var x \<Rightarrow> True
                                | Fun g ts \<Rightarrow>
                                  if pr_strict (f,length ss) (g,length ts) then True
                                  else if (f, length ss) = (g, length ts)
                                       then if (f \<notin> AC \<or> length ss \<noteq> 2)
                                       then fst (lex_ext (\<lambda> x y. (ackbo_impl x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ss) ss ts)
                                       else let (S,T) = (actop f (Fun f ss), actop f (Fun g ts)) in
                                       let (sr, ns) = mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (S \<restriction>\<^sub>n (f, 2)) (T\<restriction>\<^sub>n (f, 2) + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) in
                                       if sr then True else
                                       if ns \<and> size S > size T then True else
                                       if ns \<and> size S = size T
                                       then smulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (S  \<restriction>\<^sub>p (f, 2)) (T \<restriction>\<^sub>p (f, 2))
                                       else False
                                  else False))
        else False)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda> (s,t). term_size s)")
    apply (auto dest: supt_term_size intro!: le_imp_less_Suc)
     apply (metis elem_le_sum_list length_map nth_map)
apply (metis elem_le_sum_list length_map nth_map)
  by (meson test test2)+
end

sublocale weight_prec_ac \<subseteq> weight_fun .
sublocale admissible_weight_fun_ac \<subseteq> weight_prec_ac .

context admissible_weight_fun_ac
begin

lemma ackbo_impl_ackbo_impl:
  assumes "ackbo s t"
  shows "ackbo_impl s t"
  using assms
proof (induct s arbitrary:t rule: subterm_induct)
  case (subterm s)
  note [simp] = ackbo_impl.simps
  show ?case using subterm(2)
  proof (cases rule: ackbo.cases)
    case (case_2 f ts g ss)
    from subterm(1) have str: "(\<And>s t. s \<in> set ts \<Longrightarrow> t \<in> set ss \<Longrightarrow> ackbo s t \<Longrightarrow> ackbo_impl s t)"
      unfolding case_2(3) by blast
    then have "fst (lex_ext (\<lambda>x y. (ackbo_impl x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ts) ts ss)"
      using case_2(8) lex_ext_local_mono[of ts ss ackbo ackbo_impl] by fastforce
    then show ?thesis using case_2 by auto
  next
    case (case_3 f ts g ys)
    have "(\<And>x x'. x \<in># actop f (Fun f ts) \<Longrightarrow> x' \<in># actop f (Fun f ys) \<Longrightarrow> ackbo x x' \<Longrightarrow> ackbo_impl x x')"
      using subterm(1) case_3(6, 7) using Bin_cases[of "Fun f ts"] unfolding case_3(3, 4)
      apply (auto simp del: ackbo_impl.simps)
        apply (meson actop_mset_subterm_eq list.set_intros(1) set_supteq_into_supt)
      by (metis actop.simps(1) actop_mset_elem_subterm union_iff) (meson list_decomp_2)
    then have "ac_case_filtered_rel (actop f s) (actop f t) (f, length ts) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo_impl x y}"
      using ac_case_filtered_rel_cong[of "actop f s" "actop f s" "actop f t" "actop f t" "{(x,y). ackbo x y}" "{(x,y). ackbo_impl x y}" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" "(f, length ts)"]
      using case_3(9) unfolding case_3 by (auto simp del: ackbo_impl.simps)
    then have "fst (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<or>
               snd (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<and> size (actop f s) > size (actop f t) \<or>
               snd (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<and> size (actop f s) = size (actop f t) \<and>
               smulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s  \<restriction>\<^sub>p (f, 2)) (actop f t \<restriction>\<^sub>p (f, 2))"
      unfolding case_3 ac_case_filtered_rel_def mulextp_def nsmulextp_def smulextp_def by (auto simp del: ackbo_impl.simps)
    then show ?thesis using ackbo_impl.simps[of s t] case_3
      by (auto simp del: ackbo_impl.simps)
  qed (auto split: term.splits)
qed


lemma ackbo_impl_ackbo:
  assumes "ackbo_impl s t"
  shows "ackbo s t"
  using assms
proof (induct s arbitrary:t rule: subterm_induct)
  case (subterm s)
  note [simp] = ackbo_impl.simps
  from subterm(2) have fun_s: "is_Fun s" using  leD weight_w0 by (auto split: if_splits) fastforce 
  from subterm(2) have vars: "vars_term_ms t \<subseteq># vars_term_ms s" and wei: "weight t \<le> weight s" by (auto split: if_splits) 
  then show ?case
  proof (cases "weight t < weight s")
    case False
    then have wei: "weight t = weight s" using wei by auto
    then show ?thesis
    proof (cases "is_Var t")
      case False
      then obtain f g ts ss where s: "s = Fun f ts" and t: "t = Fun g ss" using fun_s by blast
      then show ?thesis
      proof (cases "pr_strict (f, length ts) (g, length ss)")
        case True
        then show ?thesis using vars wei unfolding s t by (auto intro!: case_1)
      next
        case False
        then have root_eq: "f = g \<and> length ts = length ss" using subterm(2) vars wei unfolding s t
          by (auto split: if_splits)
        then show ?thesis
        proof (cases "f \<notin> AC \<or> length ss \<noteq> 2")
          case True
          then have lex: "fst (lex_ext (\<lambda> x y. (ackbo_impl x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ts) ts ss)"
            using ackbo_impl.simps[of s t] subterm(2) root_eq vars wei pr_irr unfolding s t by (auto simp del: ackbo_impl.simps)
          from subterm(1) have str: "(\<And>s t. s \<in> set ts \<Longrightarrow> t \<in> set ss \<Longrightarrow> ackbo_impl s t \<Longrightarrow> ackbo s t)"
            unfolding s t by blast
          then have "fst (lex_ext (\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ts) ts ss)"
            using lex lex_ext_local_mono[of ts ss ackbo_impl ackbo] by fastforce
          then show ?thesis using vars wei root_eq True unfolding s t by (auto intro: case_2)
        next
          case False
          then have "fst (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<or>
             snd (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<and> size (actop f s) > size (actop f t) \<or>
             snd (mulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s \<restriction>\<^sub>n (f, 2)) (actop f t\<restriction>\<^sub>n (f, 2) + (actop f t\<restriction>\<^sub>v - actop f s\<restriction>\<^sub>v))) \<and> size (actop f s) = size (actop f t) \<and>
             smulextp (\<lambda> t u.(ackbo_impl t u, (t,u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (actop f s  \<restriction>\<^sub>p (f, 2)) (actop f t \<restriction>\<^sub>p (f, 2))"
            using ackbo_impl.simps[of s t] subterm(2) wei vars root_eq pr_irr unfolding s t by (auto simp del: ackbo_impl.simps) meson+ 
          then have ac: "ac_case_filtered_rel (actop f s) (actop f t) (f, length ts) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo_impl x y}"
              using False root_eq unfolding s t ac_case_filtered_rel_def mulextp_def nsmulextp_def smulextp_def by (auto simp del: ackbo_impl.simps)
          have "(\<And>x x'. x \<in># actop f (Fun f ts) \<Longrightarrow> x' \<in># actop f (Fun f ss) \<Longrightarrow> ackbo_impl x x' \<Longrightarrow> ackbo x x')"
            using subterm(1) False Bin_cases[of "Fun f ts"] unfolding s t
            apply (auto simp del: ackbo_impl.simps) 
            apply (meson actop_mset_subterm_eq list.set_intros(1) set_supteq_into_supt)
            by (metis actop.simps(1) actop_mset_elem_subterm union_iff) (metis list_decomp_2 root_eq) 
          then have "ac_case_filtered_rel (actop f s) (actop f t) (f, length ts) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y}"
            using ac_case_filtered_rel_cong[of "actop f s" "actop f s" "actop f t" "actop f t" "{(x,y). ackbo_impl x y}" "{(x,y). ackbo x y}" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" "(f, length ts)"]
            using ac root_eq unfolding s t by blast
          then show ?thesis using vars wei False root_eq pr_irr unfolding s t
            by (auto intro: case_3)
        qed
     qed
    qed (auto simp add: fun_s wei vars intro!: case_0)
  qed (auto simp add: vars case_w)
qed

lemma ackbo_impl_eq:
  shows "ackbo s t = ackbo_impl s t"
  using ackbo_impl_ackbo ackbo_impl_ackbo_impl by blast
end

abbreviation ackbo where "ackbo \<equiv> weight_prec_ac.ackbo_impl"

(* for representing concrete instances of ACKBO,
   entries:
    ('f \<times> nat) represents the function symbol with associated arity
    (nat \<times> nat \<times> bool) the first entry represents the precedence where 0 is the lowest 
                        the second entry represents the weight of the symbol
                        the third entry encodes the type of the symbol, if True then it is an AC symbol
    the nat after the list is the value of w0
*)
type_synonym 'f prec_weight_ac_repr = "(('f \<times> nat) \<times> (nat \<times> nat \<times> bool)) list \<times> nat"

fun showsl_ackbo_repr :: "('f :: showl) prec_weight_ac_repr \<Rightarrow> showsl"
  where
    "showsl_ackbo_repr (prs, w0) =
    showsl_lit (STR ''ACKBO with the following precedence and weight function:\<newline>'') \<circ>
    foldr (\<lambda>(fn,(pr, w, ac)).
      showsl_lit (STR ''precedence('') \<circ> showsl_funa fn \<circ> showsl_lit (STR '') = '')
      \<circ> showsl pr \<circ> showsl_nl) prs \<circ>
    showsl_lit (STR ''precedence(_) = 0\<newline>\<newline>'') \<circ>
    foldr (\<lambda>(fn, (pr, w, ac)).
      showsl_lit (STR ''weight('') \<circ> showsl_funa fn \<circ> showsl_lit (STR '') = '')
      \<circ> showsl w \<circ> showsl_nl) prs \<circ>
    showsl_lit (STR ''weight(_) = '') \<circ> showsl (Suc w0) \<circ>
    showsl_lit (STR ''\<newline>w0 = '') \<circ> showsl w0 \<circ> showsl_nl \<circ> showsl_nl \<circ>
    showsl_list_gen (\<lambda>(fn, _). showsl_funa fn)
      (STR ''no AC function symbols'') \<comment> \<open>empty list\<close>
      (STR ''AC function symbols: '') \<comment> \<open>left of list\<close>
      (STR '', '') \<comment> \<open>separator for list items\<close>
      (STR '''') \<comment> \<open>right of list\<close>
      (filter (\<lambda>(_, (_, _, ac)). ac) prs) \<circ> showsl_nl \<circ>
    showsl_list_gen (\<lambda>(fn, _). showsl_funa fn)
      (STR ''no non AC function symbols'') \<comment> \<open>empty list\<close>
      (STR ''non AC function symbols: '') \<comment> \<open>left of list\<close>
      (STR '', '') \<comment> \<open>separator for list items\<close>
      (STR '''') \<comment> \<open>right of list\<close>
      (filter (\<lambda>(_, (_, _, ac)). \<not> ac) prs) \<circ> showsl_nl"

definition prec_ext :: "('a \<Rightarrow> (nat \<times> 'b) option) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "prec_ext prwm = (\<lambda> f g. case prwm f of
    Some pf \<Rightarrow> (case prwm g of Some pg \<Rightarrow> fst pf > fst pg | None \<Rightarrow> True)
    | None \<Rightarrow> False)"

lemma prec_ext_measure:
  fixes prwm :: "('a \<Rightarrow> (nat \<times> 'b) option)"
  defines "m \<equiv> fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
  shows  "prec_ext prwm fn gm = (m fn > m gm)"
proof
  assume s:"prec_ext prwm fn gm"
  from s[unfolded prec_ext_def] obtain pf where pf:"prwm fn = Some pf"
    by (metis (no_types, lifting) option.exhaust option.simps(4))
  show "m fn > m gm"
  proof(cases "prwm gm = None")
    case True
    with pf show "m fn > m gm" unfolding m_def by force
  next
    case False
    then obtain pg where pg:"prwm gm = Some pg" by auto
    from s[unfolded prec_ext_def pf pg option.cases] pf pg show "m fn > m gm" unfolding m_def by auto
  qed
next
  assume m:"m fn > m gm"
  from this[unfolded m_def] have pf:"prwm fn \<noteq> None"
    by (metis fun_of_map_fun'.simps not_less_zero option.simps(4))
  then obtain pf where pf:"prwm fn = Some pf" by auto
  show "prec_ext prwm fn gm" proof(cases "prwm gm = None")
    case False
    then obtain pg where pg:"prwm gm = Some pg" by auto
    from m[unfolded m_def] show ?thesis unfolding prec_ext_def pf pg option.cases using pf pg by force
  next
    case True
    show ?thesis unfolding prec_ext_def pf option.cases True by auto
  qed
qed

(* check whether partially defined prec and weight are admissible, convert to total weight and prec *)
definition
  prec_weight_ac_repr_to_prec_weight_funs :: "('f :: compare_order) prec_weight_ac_repr \<Rightarrow> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool) \<times> ('f \<times> nat \<Rightarrow> nat) \<times> nat \<times> 'f set" 
  where
    "prec_weight_ac_repr_to_prec_weight_funs prw_w0 \<equiv>
    let 
      (prw, w0) = prw_w0;
      prwm    = ceta_map_of prw;
      w_fun   = fun_of_map_fun' prwm (\<lambda> _. Suc w0) (fst o snd);
      p_fun   = prec_ext prwm;
      acset = set (map (fst \<circ> fst) (filter (\<lambda> ((f,n),(p,w,ac)). ac) prw))
      in (p_fun, w_fun, w0, acset)"

definition
  prec_weight_ac_repr_to_prec_weight :: "('f :: {showl,compare_order}) prec_weight_ac_repr \<Rightarrow> showsl check \<times> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool) \<times> ('f \<times> nat \<Rightarrow> nat) \<times> nat \<times> 'f set" 
  where
    "prec_weight_ac_repr_to_prec_weight prw_w0 \<equiv>
    let
      (p_fun, w_fun, w0, acset) = prec_weight_ac_repr_to_prec_weight_funs prw_w0;
      (prw, w0) = prw_w0;
      fs      = map fst prw;
      cw_okay = check_allm (\<lambda> fn. check (snd fn = 0 \<longrightarrow> w_fun fn \<ge> w0) 
          (showsl_lit (STR ''weight of constant '') o showsl (fst fn) o showsl_lit (STR '' must be at least w0''))) fs;
      adm     = check_allm (\<lambda> fn. check (snd fn = 1 \<longrightarrow> w_fun fn = 0 \<longrightarrow> (list_all (\<lambda> x. p_fun fn x \<or> x = fn) fs)) 
         (showsl_lit (STR ''unary symbol '') o showsl (fst fn) o showsl_lit (STR '' with weight 0 does not have maximal precedence''))) (map fst prw);
      irr     = check_allm (\<lambda> fn. check (\<not> p_fun fn fn) (showsl_lit (STR ''function symbol '') o showsl (fst fn) o showsl_lit (STR '' violates irreflexibity''))) fs;
      ok      = (do {
        check (w0 > 0) (showsl_lit (STR ''w0 must be larger than 0''));
        adm;
        cw_okay;
        irr
      })
      in (ok, p_fun, w_fun, w0, acset)"

lemma prec_weight_ac_repr_to_prec_weight: 
  assumes ok: "prec_weight_ac_repr_to_prec_weight prw_w0 = (succeed, p, w, w0, acset)"
  shows "admissible_weight_fun_ac w w0 p"
proof -
  have id: "\<And> b. (b = succeed) = isOK(b)" by auto
  note defs = prec_weight_ac_repr_to_prec_weight_def prec_weight_ac_repr_to_prec_weight_funs_def
  obtain prw w0' where prw_w0: "prw_w0 = (prw, w0')" by force
  obtain cs where cs: "cs = filter (\<lambda> fn. snd fn = 0 \<and> w fn = w0') (map fst prw)" by auto
  note ok' = ok[unfolded defs prw_w0 Let_def split]
  from ok' have w0': "w0' = w0" by simp
  note ok = ok'[unfolded w0']
  obtain fs where fs: "fs = set (map fst prw)" by auto
  note ok = ok[simplified, unfolded id, simplified]
  have w: "w = (\<lambda> fn. case map_of prw fn of Some pw \<Rightarrow> (fst o snd) pw | None \<Rightarrow> Suc w0)" 
    by (rule ext, insert ok, auto)
  from ok have p:"p = prec_ext (map_of prw)" by auto
  from ok have cw_okay: "\<And> fn. fn \<in> fs \<Longrightarrow> snd fn = 0 \<Longrightarrow> w fn \<ge> w0" unfolding w fs by auto
  from ok have "\<And> fn. fn \<in> fs \<Longrightarrow> snd fn = 1 \<longrightarrow> w fn = 0 \<longrightarrow> list_all (\<lambda> x. p fn x \<or> x = fn) (map fst prw)"
    unfolding fs w set_map comp_apply by auto
  hence adm: "\<And> fn gm. fn \<in> fs \<Longrightarrow> gm \<in> fs \<Longrightarrow> snd fn = 1 \<Longrightarrow> w fn = 0 \<Longrightarrow> p fn gm \<or> fn = gm"
    using fs unfolding list.pred_set by force
  from ok have irr:"\<And> fn. fn \<in> fs \<Longrightarrow> \<not> p fn fn" by (meson less_irrefl prec_ext_measure)
  from ok have w0: "w0 > 0" by simp
  {
    fix fn
    assume "fn \<notin> fs"
    hence fn: "\<And> e. (fn,e) \<notin> set prw" unfolding fs by force
    with map_of_SomeD[of prw fn] have l: "map_of prw fn = None" 
      by (cases "map_of prw fn", auto)
    hence "w fn = Suc w0" unfolding p w by auto
  } note not_fs = this
  show ?thesis
  proof
    show "w0 > 0" by (rule w0)
  next
    fix f
    show "w0 \<le> w (f,0)"
    proof (cases "(f,0) \<in> fs")
      case False
      from not_fs[OF this] show ?thesis by simp
    next
      case True
      from cw_okay[OF this] show ?thesis by simp
    qed
  next
    fix f and h ::"('a\<times>nat)"
    assume ass:"w (f,1) = 0 \<and> (f,1) \<noteq> h"
    then have wf: "w (f,1) = 0" by auto
    from ass have nt_eq: "(f,1) \<noteq> h" by auto
    obtain g n where h: "h = (g,n)" using ce_trs.cases by blast 
    with not_fs[of "(f,1)"] have f_fs:"(f,1) \<in> fs" using wf by auto
    obtain pf where f_some:"map_of prw (f, 1) = Some pf"
      using weak_map_of_SomeI[of "(f,1)" _ prw] f_fs[unfolded fs] by fastforce
    show "p (f,1) h"
    proof(cases "(g,n) \<in> fs")
      case False
      then have g_none:"map_of prw (g, n) = None" unfolding fs map_of_eq_None_iff by force
      from not_fs[OF False] show ?thesis unfolding p prec_ext_def g_none f_some h by fastforce
    next
      case True
      from True have "p (g,n) \<in> set (map p (map fst prw))" unfolding fs by force
      from adm[OF f_fs True _ wf] show ?thesis using h nt_eq by auto 
    qed
  next
    let ?m = "fun_of_map_fun' (map_of prw) (\<lambda> _. 0) (Suc \<circ> fst)"
    show "SN {(fn, gm). p fn gm}" unfolding p prec_ext_measure
      using SN_inv_image[OF SN_nat_gt, unfolded inv_image_def, of ?m] by fast
  next
    fix g
    show "\<not> p g g" using irr unfolding p prec_ext_def
      by (metis (no_types, lifting) fs map_of_eq_None_iff option.simps(4) set_map)
  next
    fix s t u
    assume "p s t \<and> p t u"
    then show "p s u" unfolding p prec_ext_def by (smt case_optionE nat_int_comparison(2) option.simps(4) option.simps(5))
  qed
qed


(* checking ackbo constraints: invoke ackbo, and throw error message if terms are not in relation *)
definition
  ackbo_strict :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f set) \<Rightarrow> ('f :: showl,'v :: showl)rule \<Rightarrow> showsl check"
  where
    "ackbo_strict pr w w0 acset \<equiv> \<lambda>(s, t). check (ackbo w w0 pr acset s t) (showsl_lit (STR ''could not orient '')  o showsl s o showsl_lit (STR '' >ACKBO '') o showsl t o showsl_nl)"

lemma ackbo_strict[simp]: "isOK (ackbo_strict pr w w0 ac st) = ackbo w w0 pr ac (fst st) (snd st)" unfolding ackbo_strict_def by (cases st, auto)

definition
  ackbo_nstrict :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f set) \<Rightarrow> ('f :: showl,'v :: showl)rule \<Rightarrow> showsl check"
  where
    "ackbo_nstrict pr w w0 acset \<equiv> \<lambda>(s, t). check (ackbo w w0 pr acset s t \<or> (s,t) \<in> (acstep acset acset)\<^sup>\<leftrightarrow>\<^sup>*) 
    (showsl_lit (STR ''could not orient '')  o showsl s o showsl_lit (STR '' >=ACKBO '') o showsl t o showsl_nl)"

lemma ackbo_nstrict[simp]: "isOK (ackbo_nstrict pr w w0 ac st) = (ackbo w w0 pr ac (fst st) (snd st) \<or> (fst st, snd st) \<in> (acstep ac ac)\<^sup>\<leftrightarrow>\<^sup>*)" unfolding ackbo_nstrict_def by (cases st, auto)

definition create_ACKBO_rel_impl :: "(('f :: showl) prec_weight_ac_repr \<Rightarrow> 'g prec_weight_ac_repr) \<Rightarrow> 'f prec_weight_ac_repr \<Rightarrow> ('g :: {showl,compare_order},'v :: showl)rel_impl"
  where "create_ACKBO_rel_impl f_to_g pr = (let (ch,p,w,w0,ac) = prec_weight_ac_repr_to_prec_weight (f_to_g pr);
   ns = ackbo_nstrict p w w0 ac;
   s =  ackbo_strict p w w0 ac
    in
  \<lparr> rel_impl.valid = ch,
    standard = succeed, 
    desc = showsl_ackbo_repr pr,
    s = s,
    ns = ns,
    nst = ns,
    af = full_af,
    top_af = full_af,
    SN = succeed,
    subst_s = succeed,
    ce_compat = succeed,
    co_rewr = succeed,
    top_mono = succeed,
    top_refl = succeed,
    mono_af = full_af,
    mono = (\<lambda> _. succeed),
    not_wst = Some [],
    not_sst = Some [],
    cpx = no_complexity_check\<rparr>)"

lemma create_ACKBO_rel_impl: "rel_impl (create_ACKBO_rel_impl f_to_g prw :: ('g :: {showl,compare_order},'v :: showl)rel_impl)" 
  unfolding rel_impl_def
proof (intro allI impI, goal_cases)
  case (1 U)
  let ?rp = "create_ACKBO_rel_impl f_to_g prw :: ('g,'v)rel_impl"
  let ?af = "rel_impl.af ?rp :: ('g af)"
  let ?af' = "rel_impl.mono_af ?rp :: ('g af)"
  let ?pr = "prec_weight_ac_repr_to_prec_weight (f_to_g prw)"
  let ?ws = "rel_impl.not_wst ?rp"
  let ?sst = "rel_impl.not_sst ?rp"
  obtain ch "pr" w w0 ac where id: "?pr = (ch,pr,w,w0,ac)" by (cases ?pr, force)
  note defs = create_ACKBO_rel_impl_def Let_def split id rel_impl.simps
  note 1 = 1[unfolded defs rel_impl_list, simplified]
  have af: "?af = full_af" "?af' = full_af" unfolding defs by auto
  from 1 have ch: "ch = succeed" by (cases ch, auto)
  note id = id[unfolded ch]
  interpret admissible_weight_fun_ac w w0 pr ac
    by (rule prec_weight_ac_repr_to_prec_weight[OF id])
  let ?S = "ackbo_S" 
  let ?NS = "NS" 
  from ackbo_redpair
  interpret mono_ce_af_redtriple_order ?S ?NS ?NS full_af .
  have impl: "ackbo_impl (fst x) (snd x) = (x \<in> ?S)" for x :: "('g,'v)rule" unfolding ackbo_impl_eq by fastforce
  show ?case unfolding af 
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI impI allI 
      full_af ctxt_closed_imp_af_monotone[OF ackbo_S_mono] 
      subst_S subst_NS ctxt_NS ctxt_S trans_NS refl_NS SN S_imp_NS compat_S_NS compat_NS_S
      S_ce_compat NS_ce_compat trans_S top_mono_same)
    show "irrefl ?S" using SN irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this compat_NS_S] show "?NS \<inter> ?S^-1 = {}" .
    have suptS: "supt \<subseteq> ?S" using ackbo_S_supt by auto
    hence suptNS: "supt \<subseteq> ?NS" using S_imp_NS by auto
    show "not_subterm_rel_info ?NS (rel_impl.not_wst ?rp)" "not_subterm_rel_info ?S (rel_impl.not_sst ?rp)" 
      by (intro simple_impl_not_subterm_rel_info suptS suptNS)+
  qed (auto simp: create_ACKBO_rel_impl_def id Let_def no_complexity_check_def full_af impl) 
qed

declare weight_fun.weight.simps[code]
declare weight_prec_ac.ackbo_impl.simps[code]

end
