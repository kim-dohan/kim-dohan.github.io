(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Size_Change_Termination_Processors_Impl
imports
  Framework.QDP_Framework_Impl
  TRS.Q_Restricted_Rewriting_Impl
  Size_Change_Termination_Processors
  Generic_Usable_Rules_Impl
  Subterm_Criterion_Impl
  Dependency_Graph_Impl
begin

subsection \<open>Definitions of Processors\<close>

definition check_sct_entry where
  "check_sct_entry is_def S NST s t stri nstri \<equiv> do {
    check_no_var s;
    check_no_var t;
    check_no_defined_root is_def t;
    let m  = num_args t;
    let n  = num_args s;
    check_allm
      (\<lambda>i. check (i \<le> n) (showsl_lit (STR ''left-index to large'') \<circ> showsl i \<circ> showsl_nl))
      (remdups (map fst (stri @ nstri)));
    check_allm
      (\<lambda>j. check (j \<le> m)
        (showsl_lit (STR ''right-index to large or argument violates usable-rules condition'') \<circ> showsl j))
      (remdups (map snd (stri @ nstri)));
    let ss = args s;
    let ts = args t;
    check_allm
      (\<lambda>(i, j). check (isOK(S (get_arg s i, get_arg t j)))
                      (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' -S-> '') \<circ> showsl j)) stri;
    check_allm
      (\<lambda>(i, j). check (isOK(NST (get_arg s i, get_arg t j)))
                      (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' -NS-> '') \<circ> showsl j)) nstri
  } <+? (\<lambda>m. showsl_lit (STR ''problems with DP '') \<circ> showsl_rule (s, t) \<circ> showsl_nl \<circ> m)"

definition sct_entry_to_sts where
  "sct_entry_to_sts s t stri nstri \<equiv> let
      js = remdups (map snd (stri @ nstri))
      in map (\<lambda> j. (s, get_arg t j)) js"

definition "fun_of_default m d \<equiv> let mm = map_of m in (\<lambda> i. case mm i of None \<Rightarrow> d | Some e \<Rightarrow> e)"

(* TODO: use remdups_sort when building size-change graphs *)
definition
  sct_ur_af_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> 
     (('f, string) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list  \<Rightarrow> 
     ('f, string) rules option \<Rightarrow> 'dpp \<Rightarrow>
     showsl check"
where
  "sct_ur_af_proc I rp Gs U_opt dpp \<equiv> do {
       rel_impl_redtriple rp;
       let is_def = dpp_spec.is_defined I dpp;
       let \<pi> = rel_impl.af rp;
       let S = rel_impl.s rp;
       let NS = rel_impl.ns rp;
       let NST = rel_impl.nst rp;
       let P = dpp_ops.pairs I dpp;
       let GGs = filter (\<lambda> G. fst G \<in> set P) Gs; \<comment> \<open>we filter here, so that later on the index lookup will always succeed\<close>
       check_allm (\<lambda> (l,r). check_no_var l) (dpp_ops.rules I dpp);
       check_allm (\<lambda>((s,t),(stri,nstri)). check_sct_entry is_def S NST s t stri nstri) GGs;
       let sts = concat (map (\<lambda>((s,t),(stri,nstri)). sct_entry_to_sts s t stri nstri) GGs);
       U \<leftarrow> smart_usable_rules_checker_impl I dpp (isOK (rel_impl.ce_compat rp)) \<pi> U_opt sts;
       check_allm NS U
          <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
       let eidg = is_iedg_edge_dpp I dpp;
       check_subseteq P (map fst Gs)
         <+? (\<lambda>s. showsl_lit (STR ''there is no size-change graph for DP '') \<circ> showsl_rule s);
       let n = length P;
       let nums = [0 ..< n];
       let numPs = zip P nums;
       let num_of = fun_of_default numPs n; 
       check (check_SCT (\<lambda>(st,succs) (uv,_). uv \<in> set succs) (map (\<lambda>(st,(stri,nstri)). 
         let eidg_st = eidg st;
             i = num_of st;
             e = (i,map snd (filter (eidg_st o fst o fst) numPs)) in Scg e e stri nstri) GGs))
           (showsl_lit (STR ''size-change analysis failed\<newline>''))
     } <+? (\<lambda>s. showsl_lit (STR ''could not apply the size-change processor with the following\<newline>'') \<circ>
       rel_impl.desc rp \<circ> showsl_lit (STR ''\<newline>for the following reason\<newline>'') \<circ> s)
     "

(* takes dependency graph for connection *)
definition
  sct_subterm_precise_proc ::
    "('dpp, 'f::{showl, compare_order}, string) dpp_ops \<Rightarrow>
     (('f, string) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list \<Rightarrow>
     'dpp \<Rightarrow> showsl check"
where
  "sct_subterm_precise_proc I Gs dpp = do {
    let P      = dpp_ops.pairs I dpp;
    let is_def = dpp_spec.is_defined I dpp;
    let eidg = is_iedg_edge_dpp I dpp;
    check_subseteq P (map fst Gs)
      <+? (\<lambda>s. showsl_lit (STR ''there is no size-change graph for the pair '') \<circ> showsl_rule s);
    let GGs = filter (\<lambda> G. fst G \<in> set P) Gs; \<comment> \<open>we filter here, so that later on the index lookup will always succeed\<close>
    check (dpp_ops.minimal I dpp \<or> dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''minimality or innermost required''));
    check_allm (\<lambda> (l,r). check_no_var l) (dpp_ops.rules I dpp);
    check_allm (\<lambda>((s, t), (stri, nstri)). do {
      check_no_var s;
      check_no_var t;
      check_no_defined_root is_def t;
      let m = num_args t;
      let n = num_args s;
      check_allm (\<lambda>(i, j). check
        (i \<le> n \<and> j \<le> m \<and> isOK (check_supt (get_arg s i) (get_arg t j)))
        (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' |> '') \<circ> showsl j \<circ> showsl_nl)) stri;
      check_allm (\<lambda>(i, j). check
        (i \<le> n \<and> j \<le> m \<and> isOK (check_supteq (get_arg s i) (get_arg t j)))
        (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' |>= '') \<circ> showsl j \<circ> showsl_nl)) nstri
    } <+? (\<lambda>m. showsl_lit (STR ''problem with pair '') \<circ> showsl_rule (s, t) \<circ> showsl_nl \<circ> m)) GGs;
     let n = length P;
     let nums = [0 ..< n];
     let numPs = zip P nums;
     let num_of = fun_of_default numPs n; 
     check (check_SCT (\<lambda>(st,succs) (uv,_). uv \<in> set succs) (map (\<lambda> (st,(stri,nstri)). 
       let eidg_st = eidg st;
           i = num_of st;
           e = (i,map snd (filter (eidg_st o fst o fst) numPs)) in Scg e e (remdups_sort  stri) (remdups_sort nstri)) GGs))
         (showsl_lit (STR ''size-change analysis failed\<newline>''))
  } <+? (\<lambda>s. showsl_lit (STR ''could not apply the size-change processor based on the subterm-relation\<newline>'') \<circ> s)"

(* takes root-symbols for connection relation *)
definition
  sct_subterm_approx_proc ::
    "('dpp, 'f::{showl, compare_order}, string) dpp_ops \<Rightarrow>
     (('f, string) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list \<Rightarrow>
     'dpp \<Rightarrow> showsl check"
where
  "sct_subterm_approx_proc I Gs dpp = do {
    let P      = dpp_ops.pairs I dpp;
    let is_def = dpp_spec.is_defined I dpp;
    check_subseteq P (map fst Gs)
      <+? (\<lambda>s. showsl_lit (STR ''there is no size-change graph for the pair '') \<circ> showsl_rule s);
    let GGs = filter (\<lambda> G. fst G \<in> set P) Gs; \<comment> \<open>we filter here, so that later on the index lookup will always succeed\<close>
    check (dpp_ops.minimal I dpp \<or> dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''minimality or innermost required''));
    check_allm (\<lambda> (l,r). check_no_var l) (dpp_ops.rules I dpp);
    check_allm (\<lambda>((s, t), (stri, nstri)). do {
      check_no_var s;
      check_no_var t;
      check_no_defined_root is_def t;
      let m = num_args t;
      let n = num_args s;
      check_allm (\<lambda>(i, j). check
        (i \<le> n \<and> j \<le> m \<and> isOK (check_supt (get_arg s i) (get_arg t j)))
        (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' |> '') \<circ> showsl j \<circ> showsl_nl)) stri;
      check_allm (\<lambda>(i, j). check
        (i \<le> n \<and> j \<le> m \<and> isOK (check_supteq (get_arg s i) (get_arg t j)))
        (showsl_lit (STR ''problem with edge '') \<circ> showsl i \<circ> showsl_lit (STR '' |>= '') \<circ> showsl j \<circ> showsl_nl)) nstri
    } <+? (\<lambda>m. showsl_lit (STR ''problem with pair '') \<circ> showsl_rule (s, t) \<circ> showsl_nl \<circ> m)) GGs;
     check (check_SCT (\<lambda>(_,g) (h,_). g = h) (remdups (map (\<lambda> (st,(stri,nstri)). 
       let e = (the (root (fst st)), the (root (snd st))) in Scg e e (remdups_sort  stri) (remdups_sort nstri)) GGs)))
         (showsl_lit (STR ''size-change analysis failed\<newline>''))
  } <+? (\<lambda>s. showsl_lit (STR ''could not apply the size-change processor based on the subterm-relation\<newline>'') \<circ> s)"

definition
  sct_subterm_proc ::
    "('dpp, 'f::{showl, compare_order}, string) dpp_ops \<Rightarrow>
     (('f, string) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list \<Rightarrow>
     'dpp \<Rightarrow> showsl check" where
  "sct_subterm_proc  I Gs dpp = (if isOK(sct_subterm_approx_proc I Gs dpp) then succeed else
     sct_subterm_precise_proc I Gs dpp)"


subsection \<open>Soundness Proofs\<close>

lemma fun_of_default_index: assumes index: "indexed = zip as [0 ..< length as]"
  and mem: "a \<in> set as"
  shows "fun_of_default indexed d a < length as" 
  "as ! fun_of_default indexed d a = a" 
  "indexed ! fun_of_default indexed d a = (a,fun_of_default indexed d a)"
proof -
  {
    assume "map_of indexed a = None"
    from this[unfolded map_of_eq_None_iff] mem have False
      unfolding index set_conv_nth by force
  }
  then obtain i where i: "map_of indexed a = Some i" by auto
  from map_of_SomeD[OF this, unfolded index] 
  have "i < length as" and "as ! i = a" unfolding set_conv_nth by auto
  then show "fun_of_default indexed d a < length as" 
  "as ! fun_of_default indexed d a = a" 
  "indexed ! fun_of_default indexed d a = (a,fun_of_default indexed d a)"
    using i unfolding fun_of_default_def index by auto
qed  

lemma sct_subterm_precise_proc_sound: assumes I: "dpp_spec I"
  and check: "isOK (sct_subterm_precise_proc I Gs d)"
  shows "finite_dpp (dpp_ops.dpp I d)"
proof (rule ccontr)
  interpret dpp_spec I by fact
  assume not_finite: "\<not> finite_dpp (dpp_ops.dpp I d)"
  obtain P where P: "P = dpp_ops.pairs I d" by auto
  obtain R where R: "R = dpp_ops.rules I d" by auto
  obtain Q where Q: "Q = dpp_ops.Q I d" by auto
  define GGs where "GGs = filter (\<lambda> G. fst G \<in> set P) Gs"
  let ?m = "M d"
  from not_finite obtain s t \<sigma>
    where mchain: "min_ichain (dpp_ops.dpp I d) s t \<sigma>" by (auto simp: finite_dpp_def)
  let ?n = "length P"
  define numPs where "numPs = zip P [0 ..< ?n]"
  let ?rd = remdups_sort
  let ?entry = "\<lambda> st. (fun_of_default numPs ?n st,map snd (filter (is_iedg_edge_dpp I d st o fst o fst) numPs))"
  let ?Gs    = "map (\<lambda>(st, (stri, nstri)). Scg (?entry st) (?entry st) (?rd stri) (?rd nstri)) GGs"
  let ?conn = "\<lambda>(st,i_st) (uv,i_uv). uv \<in> set i_st"
  note check = check[unfolded sct_subterm_precise_proc_def Let_def, folded P, folded numPs_def GGs_def]
  from check
    have 1: "set P \<subseteq> fst ` set Gs \<and> check_SCT ?conn ?Gs" and nvar: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> is_Fun l"
      and min_or_inn: "?m \<or> NF_terms (set Q) \<subseteq> NF_trs (set R)"
    unfolding sct_subterm_precise_proc_def Let_def R Q by auto
  let ?check2'' = "\<lambda>f g s t stri nstri.
    is_Fun s
    \<and> is_Fun t
    \<and> \<not> defined (set R) (the (root t))
    \<and> (\<forall>(i, j)\<in>set stri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> f (get_arg s i, get_arg t j))
    \<and> (\<forall>(i, j)\<in>set nstri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> g (get_arg s i, get_arg t j))"
  let ?check2' = "?check2'' (\<lambda>r. isOK (check_supt (fst r) (snd r)))
                            (\<lambda>r. isOK (check_supteq (fst r) (snd r)))"
  let ?check2  = "?check2'' (\<lambda>r. r \<in> {\<rhd>}) (\<lambda>r. r \<in> {\<unrhd>})"
  from check have "\<forall>((s, t), (stri, nstri)) \<in> set GGs. ?check2' s t stri nstri"
    by (force simp: sct_subterm_precise_proc_def Let_def R)
  then have 2: "\<forall>((s, t), (stri, nstri))\<in>set GGs. ?check2 s t stri nstri"
    unfolding split_def unfolding isOK_check_supt isOK_check_supteq
    unfolding fst_conv snd_conv .
  let ?tuple = "\<lambda> s t. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t))"
  let ?graph = "\<lambda> s t. \<exists>stri nstri. (
    Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd nstri) \<in> set ?Gs
    \<and> (\<forall>(i, j)\<in>set stri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> get_arg s i \<rhd> get_arg t j)
    \<and> (\<forall>(i, j)\<in>set nstri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> get_arg s i \<unrhd> get_arg t j))"
  {
    fix s t
    assume memP: "(s,t) \<in> set P"
    from memP 1 obtain stri nstri
      where mem: "((s,t), (stri, nstri)) \<in> set Gs" by auto
    with memP have memGs: "Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd nstri) \<in> set ?Gs" unfolding GGs_def
      by force
    from mem memP and 2 have ch: "?check2 s t stri nstri" unfolding GGs_def by force
    from ch have tuple: "?tuple s t" by force
    from ch memGs have "?graph s t" unfolding split_def by auto
    with tuple have "?tuple s t \<and> ?graph s t" by auto
  }
  then have tuple_graph: "\<forall> (s,t)\<in>set P. ?tuple s t \<and> ?graph s t" by auto
  from tuple_graph have tuple: "\<forall> (s,t)\<in>set P. ?tuple s t" by auto
  from tuple_graph have graph: "\<forall> (s,t)\<in>set P. ?graph s t" by auto
  have min: "min_ichain (NFS d, ?m, set P, {}, set Q, set R, {}) s t \<sigma>"
    unfolding P Q R
    by (rule min_ichain_mono[OF mchain[unfolded dpp_spec_sound]], unfold dpp_spec_sound, auto)
  show False 
  proof (rule sct_with_subterm[where info = ?entry and edg = ?conn, OF min tuple graph _ min_or_inn])
    show "\<forall>(l, r)\<in>set R. is_Fun l" using nvar by auto
  next
    fix st uv
    assume mem: "(st,uv) \<in> DG (NFS d) (M d) (set P) (set Q) (set R)"
    obtain s t u v where st: "st = (s,t)" "uv = (u,v)" by force
    from mem[unfolded DG_def st] have mem_uv: "(u,v) \<in> set P" by auto
    note * = is_iedg_edge_dpp_DG_sound[OF I mem[unfolded Q R st]] 
      fun_of_default_index[OF numPs_def mem_uv]
    show "?conn (?entry st) (?entry uv)" unfolding o_def st split
      unfolding set_map set_filter 
      unfolding set_conv_nth
    proof (rule image_eqI)
      show "fun_of_default numPs ?n (u, v) = snd (numPs ! (fun_of_default numPs ?n  (u,v)))"
        using * by auto
      show "numPs ! fun_of_default numPs ?n  (u, v) \<in> {x \<in> {numPs ! i |i. i < length numPs}. is_iedg_edge_dpp I d (s, t) (fst (fst x))}"
        by (auto intro!: exI[of _ "fun_of_default numPs ?n  (u,v)"], insert *, auto simp: numPs_def)
    qed
  qed (insert 1, auto) 
qed

lemma sct_subterm_approx_proc_sound: assumes I: "dpp_spec I"
  and check: "isOK (sct_subterm_approx_proc I Gs d)"
  shows "finite_dpp (dpp_ops.dpp I d)"
proof (rule ccontr)
  interpret dpp_spec I by fact
  assume not_finite: "\<not> finite_dpp (dpp_ops.dpp I d)"
  obtain P where P: "P = dpp_ops.pairs I d" by auto
  obtain R where R: "R = dpp_ops.rules I d" by auto
  obtain Q where Q: "Q = dpp_ops.Q I d" by auto
  define GGs where "GGs = filter (\<lambda> G. fst G \<in> set P) Gs"
  let ?m = "M d"
  from not_finite obtain s t \<sigma>
    where mchain: "min_ichain (dpp_ops.dpp I d) s t \<sigma>" by (auto simp: finite_dpp_def)
  let ?rd = remdups_sort
  let ?entry = "\<lambda> st. (the (root (fst st)), the (root (snd st)))"
  let ?Gs    = "remdups (map (\<lambda>(st, (stri, nstri)). Scg (?entry st) (?entry st) (?rd stri) (?rd nstri)) GGs)"
  let ?conn = "\<lambda>(_,f) (g,_). f = g"
  note check = check[unfolded sct_subterm_approx_proc_def Let_def, folded P, folded GGs_def]
  from check
    have 1: "set P \<subseteq> fst ` set Gs \<and> check_SCT ?conn ?Gs" and nvar: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> is_Fun l"
      and min_or_inn: "?m \<or> NF_terms (set Q) \<subseteq> NF_trs (set R)"
    unfolding sct_subterm_approx_proc_def Let_def R Q by auto
  let ?check2'' = "\<lambda>f g s t stri nstri.
    is_Fun s
    \<and> is_Fun t
    \<and> \<not> defined (set R) (the (root t))
    \<and> (\<forall>(i, j)\<in>set stri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> f (get_arg s i, get_arg t j))
    \<and> (\<forall>(i, j)\<in>set nstri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> g (get_arg s i, get_arg t j))"
  let ?check2' = "?check2'' (\<lambda>r. isOK (check_supt (fst r) (snd r)))
                            (\<lambda>r. isOK (check_supteq (fst r) (snd r)))"
  let ?check2  = "?check2'' (\<lambda>r. r \<in> {\<rhd>}) (\<lambda>r. r \<in> {\<unrhd>})"
  from check have "\<forall>((s, t), (stri, nstri)) \<in> set GGs. ?check2' s t stri nstri"
    by (force simp: sct_subterm_approx_proc_def Let_def R)
  then have 2: "\<forall>((s, t), (stri, nstri))\<in>set GGs. ?check2 s t stri nstri"
    unfolding split_def unfolding isOK_check_supt isOK_check_supteq
    unfolding fst_conv snd_conv .
  let ?tuple = "\<lambda> s t. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t))"
  let ?graph = "\<lambda> s t. \<exists>stri nstri. (
    Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd nstri) \<in> set ?Gs
    \<and> (\<forall>(i, j)\<in>set stri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> get_arg s i \<rhd> get_arg t j)
    \<and> (\<forall>(i, j)\<in>set nstri.
      i \<le> length (args s) \<and> j \<le> length (args t) \<and> get_arg s i \<unrhd> get_arg t j))"
  {
    fix s t
    assume memP: "(s,t) \<in> set P"
    from memP 1 obtain stri nstri
      where mem: "((s,t), (stri, nstri)) \<in> set Gs" by auto
    with memP have memGs: "Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd nstri) \<in> set ?Gs" unfolding GGs_def
      by force
    from mem memP and 2 have ch: "?check2 s t stri nstri" unfolding GGs_def by force
    from ch have tuple: "?tuple s t" by force
    from ch memGs have "?graph s t" unfolding split_def by auto
    with tuple have "?tuple s t \<and> ?graph s t" by auto
  }
  then have tuple_graph: "\<forall> (s,t)\<in>set P. ?tuple s t \<and> ?graph s t" by auto
  from tuple_graph have tuple: "\<forall> (s,t)\<in>set P. ?tuple s t" by auto
  from tuple_graph have graph: "\<forall> (s,t)\<in>set P. ?graph s t" by auto
  have min: "min_ichain (NFS d, ?m, set P, {}, set Q, set R, {}) s t \<sigma>"
    unfolding P Q R
    by (rule min_ichain_mono[OF mchain[unfolded dpp_spec_sound]], unfold dpp_spec_sound, auto)
  show False 
  proof (rule sct_with_subterm[where info = ?entry and edg = ?conn, OF min tuple graph _ min_or_inn])
    show "\<forall>(l, r)\<in>set R. is_Fun l" using nvar by auto
  next
    fix st uv
    assume mem: "(st,uv) \<in> DG (NFS d) (M d) (set P) (set Q) (set R)"
    obtain s t u v where st: "st = (s,t)" "uv = (u,v)" by force
    from mem[unfolded DG_def st] have mem_uv: "(u,v) \<in> set P" and mem_st: "(s,t) \<in> set P" by auto
    from tuple mem_st obtain f ts where t: "t = Fun f ts" "\<not> defined (set R) (f, length ts)" by (cases t, auto)
    from tuple mem_uv obtain g us where u: "u = Fun g us" by (cases u, auto)
    from mem[unfolded DG_def st] obtain \<sigma> \<tau>  where steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep (NFS d) (set Q) (set R))\<^sup>*" by auto
    have "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (nrqrstep (NFS d) (set Q) (set R))\<^sup>*"
      by (rule qrsteps_imp_nrqrsteps[OF _ _ steps], insert nvar t, auto simp: applicable_rules_def defined_def)
    from nrqrsteps_preserve_root[OF this]
    show "?conn (?entry st) (?entry uv)" unfolding st t u by simp
  qed (insert 1, auto) 
qed

lemma sct_subterm_proc_sound: assumes I: "dpp_spec I"
  and check: "isOK (sct_subterm_proc I Gs d)"
  shows "finite_dpp (dpp_ops.dpp I d)"
  using sct_subterm_approx_proc_sound[OF I, of Gs d]
    sct_subterm_precise_proc_sound[OF I, of Gs d]
    check unfolding sct_subterm_proc_def
    by (auto split: if_splits)

lemma sct_ur_af_proc: assumes I: "dpp_spec I"
  and rp: "rel_impl rp"
  and check: "isOK(sct_ur_af_proc I rp Gs U_opt d)"
  shows "finite_dpp (dpp_ops.dpp I d)"
proof -
  interpret dpp_spec I by fact
  let ?Pd = P
  let ?Rd = R
  show ?thesis
  proof -
    let ?R = "dpp_ops.rules I d"
    let ?rd = "\<lambda> x. x"
    obtain strict nstrict nstrict_top \<pi> where ids: "rel_impl.s rp = strict" and 
      idn: "rel_impl.ns rp = nstrict" and idnt: "rel_impl.nst rp = nstrict_top" and idp: "rel_impl.af rp = \<pi>" by auto
    obtain P where P: "P = dpp_ops.pairs I d" by auto
    obtain R where R: "R = dpp_ops.rules I d" by auto
    obtain Q where Q: "Q = dpp_ops.Q I d" by auto
    define GGs where "GGs = filter (\<lambda> G. fst G \<in> set P) Gs"
    let ?n = "length P"
    let ?ce = "isOK (rel_impl.ce_compat rp)" 
    define numPs where "numPs = zip P [0 ..< ?n]"
    let ?entry = "\<lambda> st. (fun_of_default numPs ?n  st,map snd (filter (is_iedg_edge_dpp I d st o fst o fst) numPs))"
    let ?Gs    = "map (\<lambda>(st, (stri, nstri)). Scg (?entry st) (?entry st) (?rd stri) (?rd nstri)) GGs"
    let ?conn = "\<lambda>(st,i_st) (uv,i_uv). uv \<in> set i_st"
    note check = check[unfolded sct_ur_af_proc_def Let_def, folded P, folded GGs_def numPs_def, simplified, unfolded ids idn idnt idp Let_def]
    let ?sts = "concat (map (\<lambda>((s,t),(stri,nstri)). sct_entry_to_sts s t stri nstri) GGs)"
    let ?uchecker = "smart_usable_rules_checker_impl I d ?ce \<pi> U_opt ?sts"
    from check have "isOK(?uchecker)" by simp
    then obtain ur where uchecker: "?uchecker = return ur" by (cases ?uchecker, auto)
    note check = check[unfolded uchecker, simplified]
    let ?lhss = "concat (map (\<lambda> ((s,t),_). map (\<lambda> i. get_arg s i) [0 ..< Suc (length (args s))]) GGs)" 
    let ?rhss = "concat (map (\<lambda> ((s,t),_). map (\<lambda> i. get_arg t i) [0 ..< Suc (length (args t))]) GGs)" 
    let ?pairs = "concat (map (\<lambda> t. map (\<lambda> s. (s,t)) ?lhss) ?rhss)"
    let ?stri = "filter (\<lambda> r. isOK(strict r)) ?pairs"
    let ?nstri = "filter (\<lambda> r. isOK(nstrict r)) ?pairs"
    let ?nstri_top = "filter (\<lambda> r. isOK(nstrict_top r)) ?pairs"
    have stri: "isOK(check_allm strict ?stri)" by auto
    from check have valid: "isOK(rel_impl_redtriple rp)" and check1: "set P \<subseteq> fst ` set Gs"
      "isOK(check_allm nstrict ur)"
      "isOK(check_allm nstrict_top ?nstri_top)"
      "check_SCT ?conn ?Gs"
      by (auto simp: Let_def P)
    from stri have stri: "isOK(rel_impl_s rp ?stri)" unfolding ids rel_impl_list by blast
    from check1(2) have nstri: "isOK(rel_impl_ns rp ur)" unfolding idn rel_impl_list by blast
    from check1(3) have nstrit: "isOK(rel_impl_nst rp ?nstri_top)" unfolding idnt rel_impl_list by blast
    from check have var: "\<And> l r. (l,r) \<in> set ?R \<Longrightarrow> is_Fun l" by auto
    from rel_impl_redtriple[OF rp valid stri nstri nstrit, unfolded idp]
      obtain S NS NST where
      redtriple: "af_redtriple_order S NS NST \<pi>" and
      ce: "?ce \<Longrightarrow> ce_compatible NS" and 
      S: "set ?stri \<subseteq> S" and NS: "set ur \<subseteq> NS" and NST: "set ?nstri_top \<subseteq> NST" by blast
    interpret af_redtriple_order S NS NST \<pi> by fact
    have rt: "af_redtriple S NS NST \<pi>" ..
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?wwf = "wwf_qtrs (set Q) (set R)"
    from smart_usable_rules_checker_impl[OF I uchecker] have ur: "smart_usable_rules_checker ?nfs ?m ?ce ?wwf \<pi> (set Q) (rules d) U_opt (set ?sts) = Some ur" unfolding Q R by auto
    note sct = generic_sct_redtriple[where info = ?entry and edg = ?conn and Gs = ?Gs]
    note sct = sct[OF _ _ smart_usable_rules_checker NS rt ce] 
    note check_sct = check1(4)
    let ?check2b = "\<lambda> s t stri nstri. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t)) \<and> 
      (\<forall> i \<in> fst ` set (stri @ nstri).  i \<le> length (args s)) \<and>
      (\<forall> j \<in> snd ` set (stri @ nstri).  j \<le> length (args t)) \<and> 
      (\<forall> (i,j) \<in> set stri.  isOK(strict (get_arg s i,get_arg t j))) \<and>
      (\<forall> (i,j) \<in> set nstri. isOK(nstrict_top (get_arg s i,get_arg t j)))"
    let ?check2a = "\<lambda> s t stri nstri. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t)) \<and> 
      (\<forall> i \<in> fst ` set (stri @ nstri).  i \<le> length (args s)) \<and>
      (\<forall> j \<in> snd ` set (stri @ nstri).  j \<le> length (args t)) \<and> 
      (\<forall> (i,j) \<in> set stri. (get_arg s i,get_arg t j) \<in> S) \<and>
      (\<forall> (i,j) \<in> set nstri. (get_arg s i,get_arg t j) \<in> NST)"
    let ?check2 = "\<lambda> s t stri nstri. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t)) \<and> 
      (\<forall> i \<in> fst ` set (stri @ nstri).  i \<le> length (args s)) \<and>
      (\<forall> j \<in> snd ` set (stri @ nstri).  j \<le> length (args t)) \<and> 
      (\<forall> (i,j) \<in> set stri. (get_arg s i, get_arg t j) \<in> S) \<and>
      (\<forall> (i,j) \<in> set nstri. (get_arg s i, get_arg t j) \<in> NST)"
    let ?is_def = "defined (set R)"
    { 
      fix s t stri nstri
      assume g: "((s,t),(stri,nstri)) \<in> set GGs"
      with check
      have "isOK(check_sct_entry ?is_def strict nstrict_top s t stri nstri)" by (auto simp: R)
      then have check2b: "?check2b s t stri nstri"
        unfolding check_sct_entry_def by (force simp: Let_def simp del: set_append map_append)
      then have i: "\<And> ij. ij \<in> set stri \<union> set nstri \<Longrightarrow> fst ij \<le> length (args s)" 
        and j: "\<And> ij. ij \<in> set stri \<union> set nstri \<Longrightarrow> snd ij \<le> length (args t)" 
        by auto
      {
        fix i j
        assume "(i,j) \<in> set stri \<union> set nstri"
        from i[OF this] j[OF this] have i: "i \<le> length (args s)" and j: "j \<le> length (args t)" 
          by auto
        from i have "i \<in> set [0 ..< Suc (length (args s))]" by auto
        then have "get_arg s i \<in> set (map (get_arg s) [0..<Suc (length (args s))])" by auto
        then have i: "get_arg s i \<in> set ?lhss" using g by force 
        from j have "j \<in> set [0 ..< Suc (length (args t))]" by auto
        then have "get_arg t j \<in> set (map (get_arg t) [0..<Suc (length (args t))])" by auto
        then have j: "get_arg t j \<in> set ?rhss" using g by force
        from i j have "(get_arg s i, get_arg t j) \<in> set ?pairs" by (simp,blast)
      } note ij_pairs = this
      have stri: "\<forall> (i,j) \<in> set stri. (get_arg s i, get_arg t j) \<in> S"
      proof (intro ballI, clarify)
        fix i j
        assume ij: "(i,j) \<in> set stri"
        from ij check2b have ok: "isOK(strict (get_arg s i,get_arg t j))" by auto
        from ij have ij: "(i,j) \<in> set stri \<union> set nstri" by auto
        show "(get_arg s i, get_arg t j) \<in> S"
          by (rule set_mp[OF S], insert ok ij_pairs[OF ij], simp)        
      qed
      have nstri: "\<forall> (i,j) \<in> set nstri. (get_arg s i, get_arg t j) \<in> NST"
      proof (intro ballI, clarify)
        fix i j
        assume ij: "(i,j) \<in> set nstri"
        from NST have NST: "set ?nstri_top \<subseteq> NST" by blast
        from ij check2b have ok: "isOK(nstrict_top (get_arg s i,get_arg t j))" by auto
        from ij have ij: "(i,j) \<in> set stri \<union> set nstri" by auto
        show "(get_arg s i, get_arg t j) \<in> NST"
          by (rule set_mp[OF NST], insert ok ij_pairs[OF ij], simp)
      qed
      from check2b stri nstri
      have check2a: "?check2a s t stri nstri" by blast
      then have "?check2 s t stri nstri" by blast
    } note check2 = this
    let ?tuple = "\<lambda> s t. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t))"
    let ?pgraph = "\<lambda> s t stri non_stri. (
      Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd non_stri) \<in> set ?Gs \<and>
      (\<forall> (i,j) \<in> set stri. i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> S) \<and> 
      (\<forall> (i,j) \<in> set non_stri. i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> NST))"
    let ?graph = "\<lambda> s t. \<exists> stri non_stri. ?pgraph s t stri non_stri"
    {
      fix s t
      assume "(s,t) \<in> set P"
      with check1 obtain stri nstri where mem: "((s,t),(stri,nstri)) \<in> set GGs" unfolding GGs_def by auto
      then have memGs: "Scg (?entry (s,t)) (?entry (s,t)) (?rd stri) (?rd nstri) \<in> set ?Gs" by force
      from check2[OF mem] have ch: "?check2 s t stri nstri" by blast
      from ch have stri_ur: "\<forall> (i,j) \<in> set stri. i \<le> length (args s) \<and> j \<le> length (args t)"
        unfolding is_Fun_Fun_conv by force
      from ch have nstri_ur: "\<forall> (i,j) \<in> set nstri. i \<le> length (args s) \<and> j \<le> length (args t)"
        unfolding is_Fun_Fun_conv by force
      from ch have tuple: "?tuple s t" by force
      from ch memGs stri_ur nstri_ur have "?pgraph s t stri nstri" by auto
      then have "?graph s t" by blast
      with tuple have "?tuple s t \<and> ?graph s t" by auto
    }
    then have  tuple_graph:  "\<forall> (s,t) \<in> set P. ?tuple s t \<and> ?graph s t" by auto
    from tuple_graph have tuple: "\<forall> (s,t) \<in> set P. ?tuple s t" by blast
    note sct = sct[OF tuple] 
    from tuple_graph have graph: "\<forall> (s,t) \<in> set P. ?graph s t" by blast
    note sct = sct[unfolded R, OF var _ _ graph]
    note sct = sct[where U_opt = U_opt and ?ce = ?ce]
    show ?thesis unfolding dpp_spec_sound
      apply (rule sct)
            apply (unfold ur[symmetric] Q[symmetric] R[symmetric])
            apply force
           apply force
          apply (rule arg_cong[where f = "smart_usable_rules_checker ?nfs ?m ?ce ?wwf \<pi> (set Q) R U_opt"])
          apply (unfold R, unfold set_map)
    proof -
      note sts = sct_entry_to_sts_def[unfolded Let_def]
      let ?one_cond = "\<lambda> s t j.  \<exists>st ns. Scg (?entry (s, t)) (?entry (s, t)) st ns
             \<in> (\<lambda>(st, x, y). Scg (?entry st) (?entry st) (?rd x) (?rd y)) `
                set GGs \<and>
             j \<in> snd ` set st \<union> snd ` set ns"
      let ?one = "{(s, get_arg t j) | s t j . ?one_cond s t j}"
      {
        fix s t j
        assume "?one_cond s t j"
        then obtain st ns
          where scg: "Scg (?entry (s,t)) (?entry (s,t)) st ns \<in> (\<lambda>(st', st, ns). Scg (?entry st') (?entry st') (?rd st) (?rd ns)) ` set GGs" 
          and j: "j \<in> snd ` set st \<union> snd ` set ns" by blast
        {
          fix s' t' st' ns'
          assume mem: "((s',t'),st',ns') \<in> set GGs"
          let ?zip = "zip P [0 ..< ?n]"
          assume eq: "fun_of_default ?zip ?n (s,t) = fun_of_default ?zip ?n (s',t')"
          from mem have "(s',t') \<in> set P" unfolding GGs_def by force
          note * = fun_of_default_index[OF refl this, of ?n]
          from * eq have "fun_of_default ?zip ?n (s,t) < ?n" by auto
          then have "map_of ?zip (s,t) = Some (fun_of_default ?zip ?n (s,t))"
            unfolding fun_of_default_def by (cases "map_of ?zip (s,t)", auto)
          from map_of_SomeD[OF this, unfolded eq, unfolded set_zip] * 
          have "(s,t) = (s',t')" by auto
          then have "s = s'" "t = t'" by auto
        }
        with scg have scg: "((s,t),?rd st,?rd ns) \<in> set GGs" unfolding numPs_def 
          by auto
        have "(s, get_arg t j) \<in> set ?sts" unfolding set_concat set_map
          by (rule, rule, rule scg, unfold sts, insert j, auto)
      }
      then have one: "?one \<subseteq> set ?sts" by blast
      {
        fix s tj
        assume "(s,tj) \<in> set ?sts"
        from this[unfolded sts] obtain t st ns j where 
          mem: "((s,t),st,ns) \<in> set GGs" and j: "j \<in> snd ` set st \<union> snd ` set ns" and tj: "tj = get_arg t j" 
          by force
        have "(s,tj) \<in> ?one" unfolding tj
          by (rule, intro exI conjI, rule refl, rule image_eqI[OF _ mem], insert j, auto)
      }
      then have two: "set ?sts \<subseteq> ?one" ..
      from one two show "?one = set ?sts" by blast
    next
      show "set P = set (?Pd d) \<union> set (Pw d)" unfolding P by simp
    next
      show "set (rules d) = set (?Rd d) \<union> set (Rw d)" by simp
    next
      fix st uv
      assume mem: "(st,uv) \<in> DG (NFS d) (M d) (set P) (set Q) (set (rules d))"
      obtain s t u v where st: "st = (s,t)" "uv = (u,v)" by force
      from mem[unfolded DG_def st] have mem_uv: "(u,v) \<in> set P" by auto
      note * = is_iedg_edge_dpp_DG_sound[OF I mem[unfolded Q R st]] 
        fun_of_default_index[OF numPs_def mem_uv]
      show "?conn (?entry st) (?entry uv)" unfolding o_def st split
        unfolding set_map set_filter 
        unfolding set_conv_nth 
      proof (rule image_eqI)
        show "fun_of_default numPs ?n  (u, v) = snd (numPs ! (fun_of_default numPs ?n  (u,v)))"
          using * by auto
        show "numPs ! fun_of_default numPs ?n  (u, v) \<in> {x \<in> {numPs ! i |i. i < length numPs}. is_iedg_edge_dpp I d (s, t) (fst (fst x))}"
          by (auto intro!: exI[of _ "fun_of_default numPs ?n  (u,v)"], insert *, auto simp: numPs_def)
      qed
    qed (insert check_sct, auto)
  qed
qed

end
