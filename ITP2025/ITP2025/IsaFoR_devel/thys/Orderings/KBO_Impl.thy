(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory KBO_Impl
  imports
    KBO_More
    Term_Order_Impl
    Reduction_Order_Impl
    First_Order_Rewriting.Term_Impl
    Auxx.Multiset_Code
    Auxx.Map_Choice
    Show.Shows_Literal
begin

(* in the implementation, the precedence is determined by a mapping into naturals (0 has least prec.) *)
locale weight_fun_nat_prc =
  fixes w :: "'f \<times> nat \<Rightarrow> nat"
  and w0 :: nat
  and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
  and least :: "'f \<Rightarrow> bool"
  and scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat"

sublocale weight_fun_nat_prc \<subseteq> kbo w w0 scf least "\<lambda>f g. fst (prc f g)" "\<lambda>f g. snd (prc f g)" .

context weight_fun_nat_prc
begin

definition "kbo_impl \<equiv> kbo"

(* main difference to kbo from KBO.thy:
  - only one invocation of precedence function for two symbols 
*)
lemma kbo_impl:
  "kbo_impl s t =
    (let wt = weight t; ws = weight s in
    if (vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> wt \<le> ws) then
      if (wt < ws) then (True, True)
      else (case s of
        Var y \<Rightarrow> (False, (case t of Var x \<Rightarrow> True | Fun g ts \<Rightarrow> ts = [] \<and> least g))
      | Fun f ss \<Rightarrow>
        (case t of
          Var x \<Rightarrow> (True, True)
        | Fun g ts \<Rightarrow>
          let p = prc (f, length ss) (g, length ts) in
          if fst p then (True, True)
          else if snd p then lex_ext_unbounded kbo_impl ss ts
          else (False, False)))
    else (False, False))"
  unfolding kbo_code [of s t] kbo_impl_def Let_def by (rule refl)

end

declare weight_fun_nat_prc.kbo_impl_def [simp]

abbreviation "kbo \<equiv> weight_fun_nat_prc.kbo_impl"
declare weight_fun_nat_prc.kbo_impl [code]


(* for representing concrete instances of KBO, we define precedence, ... for finitely many
   symbols, the remainder obtains default values *)
type_synonym 'f prec_weight_repr = "(('f \<times> nat) \<times> (nat \<times> nat \<times> (nat list option))) list \<times> nat"

fun shows_kbo_repr :: "('f :: showl) prec_weight_repr \<Rightarrow> showsl"
where
  "shows_kbo_repr (prs, w0) =
    showsl (STR ''KBO with the following precedence and weight function\<newline>'') \<circ>
    foldr (\<lambda>((f, n),(pr, w, scf)).
      showsl (STR ''precedence('') \<circ> showsl f \<circ> showsl (STR ''['') \<circ> showsl n \<circ> showsl (STR '']) = '') \<circ> showsl pr \<circ> showsl_nl) prs \<circ>
    showsl (STR  ''\<newline>precedence(_) = 0\<newline>and the following weight\<newline>'') \<circ>
    foldr (\<lambda>((f, n), (pr, w, scf)).
      showsl (STR ''weight('') \<circ> showsl f \<circ> showsl (STR ''['') \<circ> showsl n \<circ> showsl (STR '']) = '') \<circ> showsl w \<circ> showsl_nl) prs \<circ>
    showsl (STR ''\<newline>weight(_) = '') \<circ> showsl (Suc w0) \<circ>
    showsl (STR ''\<newline>w0 = '') \<circ> showsl w0 \<circ>
    showsl (STR ''\<newline>and the following subterm coefficient functions\<newline>'') \<circ>
    foldr (\<lambda>((f, n), (pr, w, scf)).
      showsl (STR ''scf('') \<circ> showsl f \<circ> showsl (STR ''['') \<circ> showsl n \<circ> showsl (STR '']) = '') \<circ>
      (if scf = None then showsl (STR ''all 1'') else showsl_list (the scf)) \<circ> showsl_nl) prs \<circ>
    showsl (STR ''\<newline>scf(_) = all 1\<newline>'')"

definition scf_repr_to_scf :: "('f \<times> nat \<Rightarrow> nat list option) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat \<Rightarrow> nat)" where
  "scf_repr_to_scf scf fn i \<equiv> case scf fn of None \<Rightarrow> 1 | Some xs \<Rightarrow> xs ! i"

fun check_scf_entry :: "('f :: showl) \<times> nat \<Rightarrow> nat list option \<Rightarrow> showsl check" where
  "check_scf_entry fn None = succeed"
| "check_scf_entry (f,n) (Some es) = do {
     check (length es = n) (showsl (STR ''nr of entries should be '') \<circ> showsl n);
     check (\<forall> e \<in> set es. e > 0) (showsl (STR ''all entries must be non-zero''))
   } <+? (\<lambda> s. showsl (STR ''problem with subterm coefficients for '') \<circ> showsl (f,n) \<circ> showsl (STR '': '') \<circ> s \<circ> showsl_nl)"

definition prec_ext :: "('a \<Rightarrow> (nat \<times> 'b) option) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool)"
  where "prec_ext prwm = (\<lambda> f g. case prwm f of
    Some pf \<Rightarrow> (case prwm g of Some pg \<Rightarrow> (fst pf > fst pg, fst pf \<ge> fst pg) | None \<Rightarrow> (True, True))
    | None \<Rightarrow> (False,f=g))"

lemma prec_ext_measure:
  fixes prwm :: "('a \<Rightarrow> (nat \<times> 'b) option)"
  defines "m \<equiv> fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
  shows  "fst (prec_ext prwm fn gm) = (m fn > m gm)"
proof
  assume s:"fst (prec_ext prwm fn gm)"
  from s[unfolded prec_ext_def] obtain pf where pf:"prwm fn = Some pf"
    by (metis (no_types, lifting) option.exhaust option.simps(4) prod.collapse prod.inject)
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
  show "fst (prec_ext prwm fn gm)" proof(cases "prwm gm = None")
    case False
    then obtain pg where pg:"prwm gm = Some pg" by auto
    from m[unfolded m_def] show ?thesis unfolding prec_ext_def pf pg option.cases using pf pg by force
  next
    case True
    show ?thesis unfolding prec_ext_def pf option.cases True by auto
  qed
qed

lemma prec_ext_weak_id: "fn = gm \<Longrightarrow> snd (prec_ext prwm fn gm)"
 unfolding prec_ext_def by (cases "prwm fn", auto)

lemma prec_ext_weak_implies_measure:
  assumes "snd (prec_ext prwm fn gm)"
  shows "(fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst) fn \<ge> fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst) gm)"
  using assms prec_ext_weak_id[of fn gm prwm] unfolding prec_ext_def option.cases
  by (cases "prwm fn", simp, cases "prwm gm", auto)
  
lemma prec_ext_measure_implies_weak:
  fixes prwm :: "('a \<Rightarrow> (nat \<times> 'b) option)"
  defines "m \<equiv> fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
  assumes pf:"prwm fn = Some pf" and m:"(m fn \<ge> m gm)" shows "snd (prec_ext prwm fn gm)"
 using assms unfolding m_def prec_ext_def option.cases pf using pf by (cases "prwm gm", auto)

lemma prec_ext_trans: "trans {(fn, gm). snd (prec_ext prwm fn gm)}" (is "trans ?R")
proof -
  { fix fn gm hk
    assume 1:"snd (prec_ext prwm fn gm)" and 2:"snd (prec_ext prwm gm hk)"
    have "snd (prec_ext prwm fn hk)" proof (cases "prwm fn")
      case None
      from 1[unfolded prec_ext_def None option.cases] 2 show ?thesis by auto
    next
      case (Some pf)
      let ?m = "fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
      from prec_ext_weak_implies_measure[OF 1] prec_ext_weak_implies_measure[OF 2] have "?m fn \<ge> ?m hk" by auto
      from prec_ext_measure_implies_weak[OF Some this] show ?thesis by auto
    qed
  }
  then show ?thesis unfolding trans_def by fast
qed

lemma distinct_map_of:
  assumes distinct:"distinct (map (fst \<circ> snd) prw)"
    and pwf:"map_of prw fn = Some pwf"
    and pwg:"map_of prw gm = Some pwg"
  shows "fn = gm \<or> fst pwf \<noteq> fst pwg"
proof -
  { assume diff:"fn \<noteq> gm"
    from distinct[unfolded distinct_map] have inj:"inj_on (fst \<circ> snd) (set prw)" by auto
    from map_of_SomeD[OF pwf] map_of_SomeD[OF pwg] diff inj
     have "fst pwf \<noteq> fst pwg" using image_set[of snd prw] unfolding inj_on_def by force
  } then show ?thesis by auto
qed  

  
lemma total_prec_ext:
  fixes prw :: "(('f \<times> nat) \<times> nat \<times> 'b) list"
  defines "p \<equiv> prec_ext (map_of prw)"
  assumes distinct:"distinct (map (fst \<circ> snd) prw)"
    and fn:"fn \<in> set (map fst prw)"
    and gm:"gm \<in> set (map fst prw)"
  shows "fn = gm \<or> fst (p fn gm) \<or> fst (p gm fn)"
proof -
  { assume diff:"fn \<noteq> gm"
    let ?m = "fun_of_map_fun' (map_of prw) (\<lambda> _. 0) (Suc \<circ> fst)"
    from fn obtain pwf where pwf:"map_of prw fn = Some pwf" using weak_map_of_SomeI[of fn _ prw] by fastforce
    from gm obtain pwg where pwg:"map_of prw gm = Some pwg" using weak_map_of_SomeI[of gm _ prw] by fastforce
    from distinct_map_of[OF distinct pwf pwg] pwf pwg diff
     have "fst (p fn gm) \<or> fst (p gm fn)" unfolding p_def prec_ext_measure by force
  } then show ?thesis by auto
qed
  
lemma prec_ext_rels:
  fixes prwm :: "('a \<Rightarrow> (nat \<times> 'b) option)"
  defines "p \<equiv> prec_ext prwm"
  shows "fst (p fn gm) = (snd (p fn gm) \<and> \<not> snd (p gm fn))"
proof
  assume s:"fst (p fn gm)"
  note m = s[unfolded p_def prec_ext_measure]
  let ?m = "fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
  have "(?m fn > ?m gm) \<Longrightarrow> snd (prec_ext prwm fn gm)"
    using prec_ext_measure_implies_weak[of "prwm"] by (cases "prwm fn", auto)
  with prec_ext_weak_implies_measure[of prwm gm fn] m show "snd (p fn gm) \<and> \<not> snd (p gm fn)" unfolding p_def by auto
next
  assume w:"snd (p fn gm) \<and> \<not> snd (p gm fn)"
  let ?m = "fun_of_map_fun' prwm (\<lambda> _. 0) (Suc \<circ> fst)"
  from w prec_ext_weak_implies_measure[of prwm fn gm] have m:"?m fn \<ge> ?m gm" unfolding p_def by auto
  from w[unfolded p_def prec_ext_def] obtain pf where pf:"prwm fn = Some pf" by (cases "prwm fn", auto)
  show "fst (p fn gm)" proof (cases "prwm gm")
    case None
    from w show ?thesis unfolding p_def prec_ext_def pf None option.cases by auto
  next
    case (Some pg)
    from w show ?thesis unfolding p_def prec_ext_def pf Some option.cases by auto
  qed
qed

lemma prec_ext_strict_weak_total:
  fixes prw :: "(('f \<times> nat) \<times> nat \<times> 'b) list"
  assumes distinct:"distinct (map (fst \<circ> snd) prw)"
  shows "snd (prec_ext (map_of prw) fn gm) = (fst (prec_ext (map_of prw) fn gm) \<or> fn = gm)"
proof(cases "(map_of prw) fn")
  case None
  show ?thesis unfolding prec_ext_def None option.cases by auto
next
  case (Some pwf)
  note pwf = this
  show ?thesis proof(cases "(map_of prw) gm")
    case None
    show ?thesis unfolding prec_ext_def Some None option.cases by auto
  next
    case (Some pwg)
    from total_prec_ext[OF distinct] map_of_SomeD[OF pwf] map_of_SomeD[OF Some]
    have  "fn = gm \<or> fst (prec_ext (map_of prw) fn gm) \<or> fst (prec_ext (map_of prw) gm fn)"
      by (metis img_fst set_map)
    show ?thesis proof (cases "fn = gm")
      case True
      with prec_ext_weak_id[OF this, of "map_of prw"] show ?thesis by auto
    next
      case False
      with distinct_map_of[OF distinct pwf Some] have "fst pwf \<noteq> fst pwg" by auto
      with False show ?thesis  unfolding prec_ext_def pwf Some option.cases by force
    qed
  qed
qed
  
 
  
    
(* check whether partially defined prec and weight are admissible, convert to total weight and prec *)
definition
  prec_weight_repr_to_prec_weight_funs :: "('f :: compare_order) prec_weight_repr 
  \<Rightarrow> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> nat) \<times> nat \<times> 'f list \<times> ('f \<times> nat \<Rightarrow> nat list option)" 
where
  "prec_weight_repr_to_prec_weight_funs prw_w0 \<equiv>
    let 
      (prw, w0) = prw_w0;
      prwm    = ceta_map_of prw;
      w_fun   = fun_of_map_fun' prwm (\<lambda> _. Suc w0) (fst o snd);
      p_fun   = prec_ext prwm;
      scf_fun = fun_of_map_fun' prwm (\<lambda> _. None) (snd o snd);
      fs      = map fst prw;
      cs      = filter (\<lambda> fn. snd fn = 0 \<and> w_fun fn = w0) fs;
      lcs     = map fst (filter (\<lambda> c. list_all (\<lambda> c'. snd (p_fun c' c)) cs) cs)
      in (p_fun, w_fun, w0, lcs, scf_fun)"

definition
  prec_weight_repr_to_prec_weight :: "('f :: {showl,compare_order}) prec_weight_repr \<Rightarrow> showsl check \<times> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> nat) \<times> nat \<times> 'f list \<times> ('f \<times> nat \<Rightarrow> nat \<Rightarrow> nat)" 
where
  "prec_weight_repr_to_prec_weight prw_w0 \<equiv>
    let
      (p_fun, w_fun, w0, lcs, scf_fun) = prec_weight_repr_to_prec_weight_funs prw_w0;
      (prw, w0) = prw_w0;
  \<comment> \<open>(prw, w0) = prw_w0;
      prwm    = ceta_map_of prw;
      w_fun   = fun_of_map_fun' prwm (\<lambda> _. Suc w0) (fst o snd);
      p_fun   = prec_ext prwm;
      scf_fun = fun_of_map_fun' prwm (\<lambda> _. None) (snd o snd);\<close>
      fs      = map fst prw;
      cw_okay = check_allm (\<lambda> fn. check (snd fn = 0 \<longrightarrow> w_fun fn \<ge> w0) 
        (showsl (STR ''weight of constant '') \<circ> showsl (fst fn) \<circ> showsl (STR '' must be at least w0''))) (map fst prw);
      adm     = check_allm (\<lambda> fn. check (snd fn = 1 \<longrightarrow> w_fun fn = 0 \<longrightarrow> (list_all (snd \<circ> (p_fun fn)) fs )) 
        (showsl (STR ''unary symbol '') \<circ> showsl (fst fn) \<circ> showsl (STR '' with weight 0 does not have maximal precedence''))) (map fst prw);
      scf_ok  = check_allm (\<lambda> fn. check_scf_entry fn (scf_fun fn)) (map fst prw);
   \<comment> \<open>s      = filter (\<lambda> fn. snd fn = 0 \<and> w_fun fn = w0) fs;
      lcs     = map fst (filter (\<lambda> c. list_all (\<lambda> c'. snd (p_fun c' c)) cs) cs);\<close>
      ok      = (do {
        check (w0 > 0) (showsl (STR ''w0 must be larger than 0''));
        adm;
        cw_okay;
        scf_ok
      })
      in (ok, p_fun, w_fun, w0, lcs, scf_repr_to_scf scf_fun)"

lemma prec_weight_repr_to_prec_weight: 
  assumes ok: "prec_weight_repr_to_prec_weight prw_w0 = (succeed,p,w,w0,lcs,scf_fun)"
  shows "admissible_kbo w w0 (\<lambda> fn gm. fst (p fn gm)) (\<lambda> fn gm. snd (p fn gm)) (\<lambda> c. c \<in> set lcs) scf_fun"
proof -
  have id: "\<And> b. (b = succeed) = isOK(b)" by auto
  note defs = prec_weight_repr_to_prec_weight_def prec_weight_repr_to_prec_weight_funs_def
  obtain prw w0' where prw_w0: "prw_w0 = (prw,w0')" by force
  obtain cs where cs: "cs = filter (\<lambda> fn. snd fn = 0 \<and> w fn = w0') (map fst prw)" by auto
  with ok[unfolded defs prw_w0 Let_def split]
   have lcs:"lcs = map fst (filter (\<lambda> c. list_all (\<lambda> c'. snd (p c' c)) cs) cs)" by fast
  note ok' = ok[unfolded defs prw_w0 Let_def split]
  from ok' have w0': "w0' = w0" by simp
  note ok = ok'[unfolded w0']
  obtain fs where fs: "fs = set (map fst prw)" by auto
  note ok = ok[simplified, unfolded id, simplified]
  have w: "w = (\<lambda> fn. case map_of prw fn of Some pw \<Rightarrow> (fst o snd) pw | None \<Rightarrow> Suc w0)" 
    by (rule ext, insert ok, auto)
  from ok have p:"p = prec_ext (map_of prw)" by auto
  let ?scf = "(\<lambda> fn. case map_of prw fn of Some pw \<Rightarrow> (snd o snd) pw | None \<Rightarrow> None)"
  have scf: "scf_fun = scf_repr_to_scf ?scf"
    by (rule ext, insert ok, auto simp: scf_repr_to_scf_def)
  from ok have cw_okay: "\<And> fn. fn \<in> fs \<Longrightarrow> snd fn = 0 \<Longrightarrow> w fn \<ge> w0" unfolding w fs by auto
  from ok have "\<And> fn. fn \<in> fs \<Longrightarrow> snd fn = 1 \<longrightarrow> w fn = 0 \<longrightarrow> list_all (snd \<circ> (p fn)) (map fst prw)"
    unfolding fs w set_map comp_apply by auto
  then have adm: "\<And> fn gm. fn \<in> fs \<Longrightarrow> gm \<in> fs \<Longrightarrow> snd fn = 1 \<Longrightarrow> w fn = 0 \<Longrightarrow> snd (p fn gm) "
    using fs unfolding list.pred_set by force
  from ok have w0: "w0 > 0" by simp
  let ?least = "\<lambda> c. c \<in> set lcs"
  {
    fix fn
    assume "fn \<notin> fs"
    then have fn: "\<And> e. (fn,e) \<notin> set prw" unfolding fs by force
    with map_of_SomeD[of prw fn] have l: "map_of prw fn = None" 
      by (cases "map_of prw fn", auto)
    then have "w fn = Suc w0 \<and> ?scf fn = None" unfolding p w by auto
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
    fix f
    have cmp:"\<And>f. list_all (\<lambda>c'. snd (p c' (f,0))) cs = (\<forall>g. w (g,0) = w0 \<longrightarrow> snd (p (g,0) (f,0)))"
      unfolding cs fs list.pred_set set_filter using not_fs[unfolded fs] w0' by force
    show "?least f = (w (f,0) = w0 \<and> (\<forall> g. w (g,0) = w0 \<longrightarrow> snd (p (g,0) (f,0))))" (is "_ = ?r")
      unfolding lcs cmp[symmetric] cs using not_fs[unfolded fs] w0' by (cases "(f,0) \<in> fs", force+)
  next
    fix f g and n::nat
    assume wf:"w (f,1) = 0"
    with not_fs[of "(f,1)"] have f_fs:"(f,1) \<in> fs" by auto
    obtain pf where f_some:"map_of prw (f, 1) = Some pf"
      using weak_map_of_SomeI[of "(f,1)" _ prw] f_fs[unfolded fs] by fastforce
    show "snd(p (f,1) (g,n))" proof(cases "(g,n) \<in> fs")
      case False
      then have g_none:"map_of prw (g, n) = None" unfolding fs map_of_eq_None_iff by force
      from not_fs[OF False] show ?thesis unfolding p prec_ext_def g_none f_some by fastforce
    next
      case True
      from True have "p (g,n) \<in> set (map p (map fst prw))" unfolding fs by force
      from adm[OF f_fs True _ wf] show ?thesis by simp
    qed
  next
    fix f and n i :: nat
    assume i: "i < n"
    define scffn where "scffn = ?scf (f,n)"
    show "0 < scf_fun (f,n) i"
    proof (cases "map_of prw (f, n)")
      case None
      then show ?thesis unfolding scf scf_repr_to_scf_def by auto
    next
      case (Some e)
      define s where "s = (snd o snd) e"
      from map_of_SomeD[OF Some]
      have "((f,n),e) \<in> set prw" by force
      then have "isOK(check_scf_entry (f,n) (?scf (f,n)))"
        using ok by auto
      also have "?scf (f,n) = s" unfolding s_def Some by simp
      finally have ok: "isOK(check_scf_entry (f,n) s)" .
      show ?thesis unfolding scf scf_repr_to_scf_def Some option.simps s_def[symmetric]
        using ok i by (cases s, auto)
    qed
  next
    let ?m = "fun_of_map_fun' (map_of prw) (\<lambda> _. 0) (Suc \<circ> fst)"
    show "SN {(fn, gm). fst (p fn gm)}" unfolding p prec_ext_measure
      using SN_inv_image[OF SN_nat_gt, unfolded inv_image_def, of ?m] by fast
  next
    show "\<And>fn gm hk. snd (p fn gm) \<Longrightarrow> snd (p gm hk) \<Longrightarrow> snd (p fn hk)"
      using prec_ext_trans[unfolded trans_def, of "map_of prw"] unfolding p by blast
  next
    fix fn
    show "snd (p fn fn)" unfolding p prec_ext_def by (cases "map_of prw fn", auto)
  next
    from prec_ext_rels show "\<And>fn gm. fst (p fn gm) = (snd (p fn gm) \<and> \<not> snd (p gm fn))" unfolding p by fast
  qed
qed

(* checking kbo constraints: invoke kbo, and throw error message if terms are not in relation *)                  
definition
  kbo_strict :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('f :: showl,'v :: showl)rule \<Rightarrow> showsl check"
where
  "kbo_strict pr w w0 least scf \<equiv> \<lambda>(s, t). check (fst (kbo w w0 pr least scf s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >KBO '') \<circ> showsl t \<circ> showsl_nl)"

lemma kbo_strict[simp]: "isOK (kbo_strict pr w w0 least scf st) = fst (kbo w w0 pr least scf (fst st) (snd st))" unfolding kbo_strict_def by (cases st, auto)


definition
  kbo_nstrict :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('f :: showl,'v :: showl)rule \<Rightarrow> showsl check"
where
  "kbo_nstrict pr w w0 least scf \<equiv> \<lambda>(s, t). check (snd (kbo w w0 pr least scf s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >=KBO '') \<circ> showsl t \<circ> showsl_nl)"

lemma kbo_nstrict[simp]: "isOK (kbo_nstrict pr w w0 least scf st) = snd (kbo w w0 pr least scf (fst st) (snd st))" unfolding kbo_nstrict_def by (cases st, auto)

definition create_KBO_rel_impl :: "(('f :: showl)prec_weight_repr \<Rightarrow> 'g prec_weight_repr) \<Rightarrow> 'f prec_weight_repr \<Rightarrow> ('g :: {showl,compare_order},'v :: showl)rel_impl"
where "create_KBO_rel_impl f_to_g pr = (let (ch,p,w,w0,lcs,scf) = prec_weight_repr_to_prec_weight (f_to_g pr);
   ns = kbo_nstrict p w w0 (\<lambda>c. c \<in> set lcs) scf;
   s =  kbo_strict p w w0 (\<lambda>c. c \<in> set lcs) scf
    in
  \<lparr> rel_impl.valid = ch, 
    standard = succeed,
    desc = shows_kbo_repr pr, 
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

lemma create_KBO_rel_impl: "rel_impl (create_KBO_rel_impl f_to_g prw :: (_,'v :: showl) rel_impl)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  note [simp] = create_KBO_rel_impl_def
  let ?rp = "create_KBO_rel_impl f_to_g prw :: (_,'v) rel_impl"
  let ?af = "rel_impl.af ?rp"
  let ?af' = "rel_impl.mono_af ?rp"
  let ?pr = "prec_weight_repr_to_prec_weight (f_to_g prw)"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
  let ?ws = "rel_impl.not_wst ?rp"
  let ?sst = "rel_impl.not_sst ?rp"
  obtain ch "pr" w w0 lcs scf where id: "?pr = (ch,pr,w,w0,lcs,scf)" by (cases ?pr, force)
  note valid = 1(1)
  have af: "?af = full_af" "?af' = full_af" by (simp_all add: id Let_def)
  from valid have "isOK(ch)" by (simp add: id Let_def)
  then have ch: "ch = succeed" by (cases ch, auto)
  have cpx: "?cpx' = no_complexity" by (simp add: id Let_def)
  note id = id[unfolded ch cpx]
  let ?least = "\<lambda>f. f \<in> set lcs"
  interpret admissible_kbo w w0 "\<lambda> fn gm. fst (pr fn gm)" "\<lambda> fn gm. snd (pr fn gm)" ?least scf
    by (rule prec_weight_repr_to_prec_weight[OF id])
  let ?S = kbo_S
  let ?NS = kbo_NS
  from kbo_redpair 
  interpret mono_ce_af_redtriple_order ?S ?NS ?NS full_af .
  show ?case
    unfolding af cpx
  proof (rule exI[of _ ?S], intro exI[of _ ?NS], intro exI conjI impI allI
    SN ctxt_NS subst_NS full_af compat_S_NS compat_NS_S S_imp_NS ctxt_S trans_S subst_S NS_ce_compat S_ce_compat trans_NS refl_NS
    top_mono_same)
    show "irrefl ?S" using SN irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this compat_NS_S] show "?NS \<inter> ?S^-1 = {}" .    
    show "af_monotone full_af ?S" using ctxt_closed_imp_af_monotone[OF ctxt_S] .
    have suptS: "supt \<subseteq> ?S"
      using kbo_S_supteq by auto
    hence suptNS: "supt \<subseteq> ?NS" using S_imp_NS by auto
    show "not_subterm_rel_info ?NS (rel_impl.not_wst ?rp)" "not_subterm_rel_info ?S (rel_impl.not_sst ?rp)" 
      by (intro simple_impl_not_subterm_rel_info suptS suptNS)+
  qed (auto simp: id isOK_no_complexity Let_def full_af)
qed


(* total_well_order_extension  *)
definition create_KBO_redord ::
  "(('f :: {showl,compare_order} \<times> nat) \<times> nat \<times> nat \<times> nat list option) list \<times> nat \<Rightarrow>
    ('f \<times> nat) list \<Rightarrow>  ('f, 'v) redord"
  where
    "create_KBO_redord pr fs =
      (let (ch, p, w, w0, lcs, scf) = prec_weight_repr_to_prec_weight pr;
      valid = do {
        ch;
        check_same_set fs (map fst (fst pr)) <+? (\<lambda>fs. showsl (STR '' signature does not match ''));
        check (length lcs > 0) (showsl (STR ''there must be a minimal constant with weight w0''));
        check (distinct (map (fst \<circ> snd) (fst pr)))
          (showsl (STR ''the given precedence is not injective''))
      }
    in
    \<lparr>
      redord.valid = valid,
      redord.less = (\<lambda>s t. fst (weight_fun_nat_prc.kbo_impl w w0 p (\<lambda>f. f \<in> set lcs) scf s t)),
      redord.min_const = lcs ! 0
    \<rparr>)"

lemma ext_admissible_weight_fun_prc:
  assumes ok: "prec_weight_repr_to_prec_weight (prw, w0) = (succeed, p, w, w0, lcs, scf_fun)"
    and distinct:"distinct (map (fst \<circ> snd) prw)"
    and s:"\<And>fn gm. fst (p fn gm) \<Longrightarrow> (gm, fn) \<in> S - Id"
    and w:"\<And>fn gm. snd (p fn gm) \<Longrightarrow> (gm, fn) \<in> S"
    and wo:"Well_order S"
    and univ:"Field S = UNIV"
  shows "admissible_kbo w w0 (\<lambda> fn gm. (gm,fn) \<in> (S - Id)) (\<lambda> fn gm. (gm,fn) \<in> S) (\<lambda>f. f \<in> set lcs) scf_fun"
proof -
  from ok prec_weight_repr_to_prec_weight[OF ok] have 
    adm:"admissible_kbo w w0 (\<lambda> fn gm. fst (p fn gm)) (\<lambda> fn gm. snd (p fn gm)) (\<lambda> c. c \<in> set lcs) scf_fun" by auto
  note adm = adm[unfolded admissible_kbo_def]
  note pw_defs = prec_weight_repr_to_prec_weight_funs_def prec_weight_repr_to_prec_weight_def
  note ok = ok[unfolded pw_defs split Let_def]
  from ok have p:"p = prec_ext (map_of prw)" by auto
  from wo[unfolded well_order_on_def] have lin:"Linear_order S" by auto
  let ?F = "set (map fst prw)"
  let ?map = "map_of prw"
  let ?w = "(\<lambda> fn gm. (gm,fn) \<in> S)"
  let ?s = "(\<lambda> fn gm. (gm,fn) \<in> S - Id)"
  show ?thesis proof
    fix f g n
    assume wf0:"w (f,1) = 0"
    from adm wf0 w show "?w (f,1) (g,n)" by metis
  next
    fix f
    let ?lcs_cond = "\<lambda> wp. w (f,0) = w0 \<and> (\<forall>g. w (g,0) = w0 \<longrightarrow> wp (g,0) (f,0))"
    show "f \<in> set lcs = ?lcs_cond ?w"
    proof
      assume f_lcs:"f \<in> set lcs"
      from adm f_lcs have "?lcs_cond (\<lambda> fn gm. snd (p fn gm))" by auto
      with w show "?lcs_cond ?w" by blast
    next
      assume fw0:"?lcs_cond ?w"
      from ok[unfolded Let_def] have "w (f,0) = fun_of_map_fun' ?map (\<lambda> _. Suc w0) (fst o snd) (f,0)" by auto
      from this fw0 obtain pwf where pwf:"?map (f,0) = Some pwf" by (cases "?map (f,0)", auto)
      from map_of_SomeD [OF this] have fF:"(f,0) \<in> ?F" by auto
      define cs where "cs = [fn\<leftarrow>map fst prw . snd fn = 0 \<and> w fn = w0]"
      from fF fw0 have f_cs:"(f,0) \<in> set cs" unfolding cs_def by auto
      from ok have lcs:"lcs = map fst [c\<leftarrow>cs. list_all (\<lambda>c'. snd (p c' c)) cs]" unfolding cs_def by blast
      { fix c
        assume ccs:"(c,0) \<in> set cs"
        with fw0 have cf:"?w (c,0) (f, 0)" unfolding cs_def by auto
        from ccs have cF:"(c,0) \<in> ?F" unfolding cs_def by auto
        { assume "(c,0) = (f,0)"
          with prec_ext_weak_id have "snd (p (c,0) (f,0))" unfolding p by fast
        } note 1 = this
        { assume "fst (p (c,0) (f,0))"
          with prec_ext_strict_weak_total[OF distinct] have "snd (p (c,0) (f,0))" unfolding p by fast
        } note 2 = this
        { assume neq:"(c,0) \<noteq> (f,0)" and pfc:"fst (p (f,0) (c,0))"
          with s have sfc:"?s (f,0) (c,0)" by auto
          from Linear_order_in_diff_Id[OF lin, unfolded univ] sfc cf neq have False by blast
        }
        with 1 2 total_prec_ext[OF distinct cF fF] have "snd (p (c,0) (f,0))" unfolding p by auto
      }
      then have "list_all (\<lambda>c'. snd (p c' (f,0))) cs" unfolding list_all_iff cs_def by simp
      with f_cs show "f \<in> set lcs" unfolding lcs by auto
    qed
  next
    from wo have wf_R: "wf (S - Id)" unfolding well_order_on_def by auto
    then show "SN {(fn,gm). (gm,fn) \<in> (S - Id)}" unfolding SN_iff_wf pair_set_inverse wf_def 
      by (metis (mono_tags, lifting) mem_Collect_eq split_conv)
  next
    from wo univ show "\<And>fn. (fn,fn) \<in> S" unfolding well_order_on_def linear_order_on_def
        partial_order_on_def preorder_on_def refl_on_def by auto
  next
    from wo show "\<And>fn gm hk. (gm,fn) \<in> S \<Longrightarrow> (hk,gm) \<in> S \<Longrightarrow> (hk,fn) \<in> S"
      unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def trans_def
      by blast
  next
    from Linear_order_in_diff_Id[OF lin] univ
    show "\<And>fn gm. ((gm,fn) \<in> S - Id) = ((gm,fn) \<in> S \<and> (fn,gm) \<notin> S)" by blast
  qed (insert adm, auto)
qed

lemma ground_total_extension:
  fixes fs :: "('f :: {showl,compare_order} \<times> nat) list"
    and prw_w0 :: "(('f \<times> nat) \<times> nat \<times> nat \<times> nat list option) list \<times> nat"
  defines "(ro :: ('f, 'v) redord) \<equiv> create_KBO_redord prw_w0 fs"
  assumes ok: "isOK (redord.valid ro)"
    and id: "prec_weight_repr_to_prec_weight prw_w0 = (ch, pr, w, w0', lcs, scf)"
shows "\<exists>S' W'.
    let less' = (\<lambda>s t. (fst (kbo.kbo w w0' scf (\<lambda>c. c \<in> set lcs) S' W' s t))) in
    (fgtotal_reduction_order less' UNIV \<and>
    (\<forall>s t. redord.less ro s t \<longrightarrow> less' s t) \<and>
    (\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun (redord.min_const ro) [])) \<and>
    admissible_kbo w w0' S' W' (\<lambda>c. c \<in> set lcs) scf \<and>
    (\<forall>f g. (fst (pr f g) \<longrightarrow> S' f g) \<and> (snd (pr f g) \<longrightarrow> W' f g)))"
proof -
  obtain prw w0 where prw_w0: "prw_w0 = (prw, w0)" by fastforce
  let ?F = "map fst prw"
  let ?map = "map_of prw"
  let ?min = "redord.min_const ro"
  let ?prw = "prec_weight_repr_to_prec_weight (prw, w0)"
  note valid = ok [unfolded ro_def id create_KBO_redord_def, simplified]

  from id have w0': "w0' = w0"
    unfolding prec_weight_repr_to_prec_weight_def
    prec_weight_repr_to_prec_weight_funs_def prw_w0 Let_def by fast
  from valid have "isOK (check_same_set fs (map fst prw))" by (simp add: prw_w0)
  then have fs: "set ?F = set fs" by auto
  from valid have ch_ok: "isOK ch" by auto
  let ?least = "\<lambda>c. c \<in> (set lcs)"
  let ?prs = "\<lambda>fn gm. fst (pr fn gm)"
  let ?prw = "\<lambda>fn gm. snd (pr fn gm)"
  interpret kbo1: admissible_kbo w w0 ?prs ?prw ?least scf
    using prec_weight_repr_to_prec_weight [of prw_w0 pr w w0' lcs scf, unfolded id] and ch_ok
    unfolding isOK_def w0' by (cases ch, auto)
  let ?kbo1S = "kbo1.S :: ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _"
  let ?S = "\<lambda>(s::('f, 'v) term) t. (s, t) \<in> kbo1.kbo_S"
  let ?W = "?S\<^sup>=\<^sup>="

  (* S is a reduction order *)
  interpret reduction_order ?S
  proof
    show "SN {(x, y). (x, y) \<in> kbo1.kbo_S}" using kbo1.kbo_strongly_normalizing unfolding SN_defs by blast
  qed (insert kbo1.S_ctxt kbo1.S_trans kbo1.S_subst, auto)

  (* S is F-ground total *)
  from id [unfolded prw_w0, unfolded prec_weight_repr_to_prec_weight_funs_def prec_weight_repr_to_prec_weight_def Let_def]
    have pr: "pr = prec_ext (map_of prw)" by auto
  from valid have distinct: "distinct (map (fst \<circ> snd) prw)" unfolding prw_w0 by auto
  note prec_ftotal = total_prec_ext [OF this]
  from prec_ext_strict_weak_total [OF distinct]
    have pr_sw: "(\<lambda>fn gm. snd (pr fn gm)) = (\<lambda>fn gm. fst (pr fn gm))\<^sup>=\<^sup>=" unfolding pr by auto
  { fix s t :: "('f, 'v) term"
    assume fg:"funas_term s \<subseteq> set ?F" "ground s" "funas_term t \<subseteq> set ?F" "ground t"
    with kbo1.S_ground_total[OF pr_sw, of "set ?F" s t] prec_ftotal 
      have oriented:"s = t \<or> ?S s t \<or> ?S t s" unfolding pr by simp
  }
  then have fgtotal: "fground (set ?F) s \<Longrightarrow> fground (set ?F) t \<Longrightarrow> s = t \<or> ?S s t \<or> ?S t s"
    for s t :: "('f, 'v) term"
    unfolding fground_def by auto

  (* extend precedence to a total one *)
  let ?m = "fun_of_map_fun' (map_of prw) (\<lambda>_. 0) (Suc \<circ> fst)"
  have sn: "SN {(fn, gm). fst (pr fn gm)}" (is "SN ?P") unfolding pr prec_ext_measure
    using SN_inv_image [OF SN_nat_gt, unfolded inv_image_def, of ?m] by fast
  from SN_imp_wf [OF sn] have wf: "wf {(gm,fn). ?prs fn gm}" by auto
  from wf total_well_order_extension obtain Pt where Pt: "{(gm,fn). ?prs fn gm} \<subseteq> Pt"
    and wo: "Well_order Pt" and univ: "Field Pt = (UNIV :: ('f \<times> nat) set)" by metis
  let ?psx = "\<lambda>(fn :: 'f \<times> nat) gm. (gm,fn) \<in> Pt - Id"
  let ?pwx = "\<lambda>fn gm. (gm,fn) \<in> Pt"
  from wo [unfolded well_order_on_def] have lin: "Linear_order Pt" by auto
  from Linear_order_in_diff_Id[OF this] univ have ptotal: "\<And>fn gm. fn = gm \<or> ?psx fn gm \<or> ?psx gm fn" by blast
  from lin [unfolded linear_order_on_def partial_order_on_def preorder_on_def refl_on_def] univ
  have refl: "\<And>x. (x,x) \<in> Pt" by blast
  from Pt kbo1.pr_strict_irrefl have S_ext: "\<forall>f g. fst (pr f g) \<longrightarrow> ?psx f g" by auto
  from Pt prec_ext_strict_weak_total[OF distinct] refl pr have "\<forall>f g. (snd (pr f g) \<longrightarrow> ?pwx f g)"
    by auto
  with S_ext have ext_sw: "(\<forall>f g. (fst (pr f g) \<longrightarrow> ?psx f g) \<and> (snd (pr f g) \<longrightarrow> ?pwx f g))" by auto

  (* there exists a ground-total extension of S *)
  from Pt wf_not_refl [OF wf] have ext_s: "\<And>fn gm. ?prs fn gm \<Longrightarrow> ?psx fn gm" by blast
  with ext_s prec_ext_strict_weak_total [OF distinct] refl
    have ext_w: "\<And>fn gm. ?prw fn gm \<Longrightarrow> ?pwx fn gm" unfolding pr by blast
  interpret kbox: admissible_kbo w w0 ?psx ?pwx ?least scf
    using ext_admissible_weight_fun_prc [OF _ distinct ext_s ext_w wo univ, of w0 pr w lcs scf]
      and id and ch_ok
    unfolding isOK_iff prw_w0 w0' by force
  let ?kboxS = "kbox.S :: ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"

  have pr_swx: "?pwx = ?psx\<^sup>=\<^sup>=" by force

  (* S is a ground-total reduction order *)
  { fix s t :: "('f, 'v) term"
    assume ground: "ground s" "ground t"
    with kbox.S_ground_total [OF pr_swx, of UNIV] ptotal
    have total: "s = t \<or> kbox.S s t \<or> kbox.S t s" by blast
  } note gtotal = this
  interpret redordx: reduction_order ?kboxS
  proof
    show "SN {(x, y). kbox.S x y}" using kbox.kbo_strongly_normalizing unfolding SN_defs by blast
  qed (insert kbox.S_ctxt kbox.S_trans kbox.S_subst, auto)
  interpret admx_gtredord: fgtotal_reduction_order ?kboxS UNIV using gtotal
    by (unfold_locales, auto simp:fground_def)
  have gred_ord: "fgtotal_reduction_order ?kboxS UNIV" ..
  have red_ord: "reduction_order ?S" ..
  from two_kbos.kbo_prec_mono [of ?least ?least ?prs ?psx ?prw ?pwx w w0 scf, OF _ ext_s ext_w]
  have ext: "kbo1.S s t \<longrightarrow> kbox.S s t" for s t :: "('f, 'v) term" by blast
  note pw_defs = prec_weight_repr_to_prec_weight_def prec_weight_repr_to_prec_weight_funs_def

  (* the minimal constant is in the signature *)
  obtain cs where cs: "cs = filter (\<lambda> fn. snd fn = 0 \<and> w fn = w0) ?F" by auto
  with ch_ok and id [unfolded pw_defs prw_w0 Let_def split]
  have lcs: "lcs = map fst (filter (\<lambda> c. list_all (\<lambda> c'. snd (pr c' c)) cs) cs)" by fast
  then have min: "?min = lcs ! 0" by (auto simp: ro_def create_KBO_redord_def id)
  from valid have len:"length lcs > 0" unfolding lcs by auto
  from cs have const:"\<And>c. c \<in> (set cs) \<Longrightarrow> snd c = 0" by auto
  from cs have "set cs \<subseteq> set ?F" by auto
  with lcs const have "\<And>c. c \<in> set lcs \<Longrightarrow> (c, 0) \<in> set ?F" by force
  from this[OF nth_mem[OF len]] have min_fs: "(?min, 0) \<in> set ?F" unfolding min .

  (* the minimal constant is smaller than any other term *)
  have min_ext: "\<forall>(t::('f, 'v) term). ground t \<longrightarrow> kbox.S\<^sup>=\<^sup>= t (Fun ?min [])"
  proof (rule, rule)
    fix t :: "('f, 'v) term"
    assume t:"ground t"
    let ?c = "Fun ?min [] :: ('f,'v) term"
    from len have "lcs ! 0 \<in> set lcs" by auto
    from kbox.NS_all_least[OF this] have ns:"kbox.NS t ?c" unfolding min .
    have "ground ?c" by auto
    from gtotal[OF t this] consider "t = ?c" | "kbox.S t ?c" | "kbox.S ?c t" by blast
    then show "kbox.S\<^sup>=\<^sup>= t ?c" using kbox.S_NS_compat[OF _ ns, of ?c] kbox.S_irrefl[of ?c] by auto
  qed

  (* combine to requirements for ordered rewriting *)
  let ?l = "redord.less ro"
  let ?c = "redord.min_const ro"
  define psx where "psx = (\<lambda>fn gm. (gm, fn) \<in> Pt - Id)"
  define pwx where "pwx = (\<lambda>fn gm. (gm, fn) \<in> Pt)"
  define goal where "goal \<equiv>
    let less' = (\<lambda>(s::('f, 'v) term) t. fst (kbo.kbo w w0 scf (\<lambda>c. c \<in> set lcs) psx pwx s t)) in
    fgtotal_reduction_order less' UNIV \<and>
    (\<forall>s t. redord.less (create_KBO_redord prw_w0 fs) s t \<longrightarrow> less' s t) \<and>
    (\<forall>t. ground t \<longrightarrow> less'\<^sup>=\<^sup>= t (Fun (redord.min_const ro) [])) \<and>
    admissible_kbo w w0 psx pwx (\<lambda>c. c \<in> set lcs) scf \<and>
    (\<forall>f g. (fst (pr f g) \<longrightarrow> psx f g) \<and> (snd (pr f g) \<longrightarrow> pwx f g))"
  have less: "redord.less ro = ?S"
    by (auto simp: ro_def create_KBO_redord_def id w0')
  from prw_w0 have prw: "prw = fst prw_w0" by auto
  have g: goal
    unfolding goal_def Let_def
    apply (rule, insert gred_ord, unfold pwx_def psx_def, simp)
    apply (rule, unfold less [unfolded ro_def], insert ext, force)
    apply (rule, insert min_ext, assumption)
    apply (rule, insert kbox.admissible_kbo_axioms, simp)
    apply (insert ext_sw, auto)
    done
  show ?thesis
    unfolding w0' and Let_def
    apply (rule exI [of _ psx], rule exI [of _ pwx])
    apply (insert g[unfolded goal_def Let_def], fastforce simp: ro_def)
    done
qed

interpretation KBO_redord: reduction_order_impl create_KBO_redord
proof
  fix fs :: "('a :: {showl,compare_order} \<times> nat) list"
    and prw_w0 :: "(('a \<times> nat) \<times> nat \<times> nat \<times> nat list option) list \<times> nat"
  obtain prw w0 where prw_w0: "prw_w0 = (prw, w0)" by fastforce
  define ro :: "('a, 'b) redord" where "ro = create_KBO_redord prw_w0 fs"
  let ?F = "map fst prw"
  let ?map = "map_of prw"
  let ?min = "redord.min_const ro"
  let ?prw = "prec_weight_repr_to_prec_weight (prw, w0)"
  assume ok: "isOK (redord.valid ro)"
  note valid = this [unfolded prw_w0 ro_def create_KBO_redord_def]

  obtain ch pr w w0' lcs scf where id: "?prw = (ch,pr,w,w0',lcs,scf)" by (cases ?prw, force)
  then have w0':"w0' = w0" unfolding prec_weight_repr_to_prec_weight_def
    prec_weight_repr_to_prec_weight_funs_def prw_w0 Let_def by fast
  from valid have "isOK (check_same_set fs (map fst prw))" unfolding id Let_def split fst_conv by simp
  then have fs: "set ?F = set fs" by auto
  note valid = valid [unfolded id Let_def prw_w0 split] 
  from valid have ch_ok: "isOK ch" by auto
  let ?least = "\<lambda>c. c \<in> (set lcs)"
  let ?prs = "\<lambda> fn gm. fst (pr fn gm)"
  let ?prw = "\<lambda> fn gm. snd (pr fn gm)"
  interpret kbo: admissible_kbo w w0 ?prs ?prw ?least scf
    using prec_weight_repr_to_prec_weight[of prw_w0, unfolded prw_w0 id w0'] ch_ok by auto
  let ?S = "\<lambda>(s::('a, 'b) term) t. (s,t) \<in> kbo.kbo_S"
  let ?W = "?S\<^sup>=\<^sup>="

  (* S is a reduction order *)
  interpret reduction_order ?S
  proof
    show "SN {(x, y). (x, y) \<in> kbo.kbo_S}"
      using kbo.kbo_strongly_normalizing
      unfolding SN_defs by blast
  qed (insert kbo.S_ctxt kbo.S_trans kbo.S_subst, auto)

  (* S is F-ground total *)
  from id[unfolded prec_weight_repr_to_prec_weight_funs_def prec_weight_repr_to_prec_weight_def Let_def]
  have pr: "pr = prec_ext (map_of prw)" by auto
  from valid have distinct: "distinct (map (fst \<circ> snd) prw)" by auto
  note prec_ftotal = total_prec_ext [OF this]
  from prec_ext_strict_weak_total [OF distinct]
  have pr_sw: "(\<lambda>fn gm. snd (pr fn gm)) = (\<lambda>fn gm. fst (pr fn gm))\<^sup>=\<^sup>=" unfolding pr by auto
  { fix s t :: "('a, 'b) term"
    assume fg: "funas_term s \<subseteq> set ?F" "ground s" "funas_term t \<subseteq> set ?F" "ground t"
    with kbo.S_ground_total [OF pr_sw, of "set ?F" s t] and prec_ftotal
    have oriented:"s = t \<or> ?S s t \<or> ?S t s" unfolding pr by simp
  }
  then have fgtotal: "fground (set ?F) s \<Longrightarrow> fground (set ?F) t \<Longrightarrow> s = t \<or> ?S s t \<or> ?S t s"
    for s t :: "('a, 'b) term"
    unfolding fground_def by auto

  (* extend precedence to a total one *)
  let ?m = "fun_of_map_fun' (map_of prw) (\<lambda> _. 0) (Suc \<circ> fst)"
  have sn: "SN {(fn, gm). fst (pr fn gm)}" (is "SN ?P") unfolding pr prec_ext_measure
    using SN_inv_image [OF SN_nat_gt, unfolded inv_image_def, of ?m] by fast
  from SN_imp_wf [OF sn] have wf: "wf {(gm,fn). ?prs fn gm}" by auto
  from wf total_well_order_extension obtain Pt where Pt: "{(gm, fn). ?prs fn gm} \<subseteq> Pt"
    and wo: "Well_order Pt" and univ: "Field Pt = (UNIV :: ('a \<times> nat) set)" by metis
  let ?psx = "\<lambda>(fn :: 'a \<times> nat) gm. (gm, fn) \<in> Pt - Id"
  let ?pwx = "\<lambda>fn gm. (gm, fn) \<in> Pt"
  from wo [unfolded well_order_on_def] have lin: "Linear_order Pt" by auto
  from Linear_order_in_diff_Id [OF this] and univ
  have ptotal:"\<And>fn gm. fn = gm \<or> ?psx fn gm \<or> ?psx gm fn" by blast
  from lin [unfolded linear_order_on_def partial_order_on_def preorder_on_def refl_on_def] and univ
  have refl: "(x, x) \<in> Pt" for x by blast

  (* there exists a ground-total extension of S *)
  from Pt wf_not_refl [OF wf] have ext_s: "\<And>fn gm. ?prs fn gm \<Longrightarrow> ?psx fn gm" by blast
  with ext_s prec_ext_strict_weak_total[OF distinct] refl
    have ext_w:"\<And>fn gm. ?prw fn gm \<Longrightarrow> ?pwx fn gm" unfolding pr by blast
  interpret kbox: admissible_kbo w w0 ?psx ?pwx ?least scf
    using ext_admissible_weight_fun_prc [OF _ distinct ext_s ext_w wo univ, of w0 pr w lcs scf]
      and id and ch_ok
    unfolding isOK_iff w0' by force
  let ?kboxS = "kbox.S :: ('a, 'b) term \<Rightarrow> _ \<Rightarrow> _"
  have pr_swx:"?pwx = ?psx\<^sup>=\<^sup>=" by force

  (* S is a ground-total reduction order *)
  { fix s t :: "('a, 'b) term"
    assume ground:"ground s" "ground t"
    with kbox.S_ground_total[OF pr_swx, of UNIV] ptotal
      have total:"s = t \<or> kbox.S s t \<or> kbox.S t s" by blast
  } note gtotal = this
  interpret redordx: reduction_order ?kboxS
  proof
    show "SN {(x, y). kbox.S x y}" using kbox.kbo_strongly_normalizing unfolding SN_defs by blast
  qed (insert kbox.S_ctxt kbox.S_trans kbox.S_subst, auto)
  interpret admx_gtredord: gtotal_reduction_order ?kboxS using gtotal
    by (unfold_locales, auto simp:fground_def)
  have gred_ord: "gtotal_reduction_order ?kboxS" ..
  have red_ord: "reduction_order ?S" ..
  from two_kbos.kbo_prec_mono [of ?least ?least ?prs ?psx ?prw ?pwx w w0 scf, OF _ ext_s ext_w]
  have ext: "(\<And>s t. kbo.S s t \<longrightarrow> ?kboxS s t)" by blast
  note pw_defs = prec_weight_repr_to_prec_weight_def prec_weight_repr_to_prec_weight_funs_def

  (* the minimal constant is in the signature *)
  obtain cs where cs: "cs = filter (\<lambda> fn. snd fn = 0 \<and> w fn = w0) ?F" by auto
  with ch_ok and id [unfolded pw_defs prw_w0 Let_def split]
  have lcs: "lcs = map fst (filter (\<lambda> c. list_all (\<lambda> c'. snd (pr c' c)) cs) cs)" by fast
  then have min: "?min = lcs ! 0"
    by (auto simp: ro_def prw_w0 create_KBO_redord_def id)
  from valid have len:"length lcs > 0" unfolding lcs by auto
  from cs have const:"\<And>c. c \<in> (set cs) \<Longrightarrow> snd c = 0" by auto
  from cs have "set cs \<subseteq> set ?F" by auto
  with lcs const have "\<And>c. c \<in> set lcs \<Longrightarrow> (c,0) \<in> set ?F" by force
  from this [OF nth_mem [OF len]] have min_fs: "(?min, 0) \<in> set ?F" unfolding min .

  (* the minimal constant is smaller than any other term *)
  have min_ext: "\<forall>t. ground t \<longrightarrow> ?kboxS\<^sup>=\<^sup>= t (Fun ?min [])"
  proof (intro impI allI)
    fix t :: "('a, 'b) term"
    assume t: "ground t"
    let ?c = "Fun ?min [] :: ('a, 'b) term"
    from len have "lcs ! 0 \<in> set lcs" by auto
    from kbox.NS_all_least[OF this] have ns:"kbox.NS t ?c" unfolding min .
    have "ground ?c" by auto
    from gtotal [OF t this] consider "t = ?c" | "kbox.S t ?c" | "kbox.S ?c t" by blast
    then show "kbox.S\<^sup>=\<^sup>= t ?c" using kbox.S_NS_compat[OF _ ns, of ?c] kbox.S_irrefl[of ?c] by auto
  qed

  (* combine to requirements for ordered rewriting *)
  let ?l = "redord.less ro"
  let ?c = "redord.min_const ro"
  let ?g = "(?c, 0) \<in> (set fs) \<and> reduction_order ?l \<and>
            (\<forall>s t. fground (set fs) s \<and> fground (set fs) t \<longrightarrow> s = t \<or> ?l s t \<or> ?l t s) \<and>
            (\<exists>lt. gtotal_reduction_order lt \<and> (\<forall>s t. ?l s t \<longrightarrow> lt s t) \<and> (\<forall>t. ground t \<longrightarrow> lt\<^sup>=\<^sup>= t (Fun ?c [])))"
  have less: "redord.less ro = ?S"
    by (auto simp: ro_def create_KBO_redord_def prw_w0 id w0')
  from prw_w0 have prw: "prw = fst prw_w0" by auto
  from ok show ?g
    using min_fs fgtotal gtotal red_ord gred_ord ext min_ext
    unfolding less fs by auto
qed
end
