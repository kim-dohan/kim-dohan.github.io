(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory WPO_Impl
  imports
    Weighted_Path_Order.WPO
    Efficient_Weighted_Path_Order.WPO_Mem_Impl
    Term_Order_Impl
    Status_Impl
    First_Order_Rewriting.Term_Impl
    Auxx.Name
    Show.Shows_Literal
begin

lemma (in wpo_with_assms)  wpo_rewrite_order: "rewrite_order WPO_S WPO_NS" 
proof -
  interpret order_pair WPO_S WPO_NS by (rule wpo_order_pair)
  show ?thesis
  proof
    show "subst.closed WPO_S" using wpo_stable by auto
    show "subst.closed WPO_NS" using wpo_stable by auto
    show "ctxt.closed WPO_NS" using wpo_ns_mono one_imp_ctxt_closed[of WPO_NS] by blast
  qed
qed


lemma (in wpo_with_assms) wpo_co_rewrite_pair: "co_rewrite_pair WPO_S WPO_NS"
proof -
  interpret rewrite_order WPO_S WPO_NS by (rule wpo_rewrite_order)
  interpret order_pair WPO_S WPO_NS by (rule wpo_order_pair)
  show ?thesis
  proof (unfold_locales, rule refl_NS, rule trans_NS)
    show "WPO_NS \<inter> WPO_S\<inverse> = {}" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      then obtain a where "(a,a) \<in> WPO_S" using compat_S_NS by blast
      thus False using wpo_irrefl unfolding irrefl_def by auto
    qed
  qed
qed

context wpo_with_SN_assms
begin

lemma wpo_redtriple_order: "redtriple_order WPO_S WPO_NS WPO_NS"
proof -
  interpret rewrite_order WPO_S WPO_NS by (rule wpo_rewrite_order)
  interpret SN_order_pair WPO_S WPO_NS by (rule wpo_SN_order_pair)
  show ?thesis
  proof (unfold_locales; (intro trans_NS refl_NS compat_NS_S WPO_S_subset_WPO_NS)?)
    show "subst.closed WPO_NS" using wpo_stable by auto
  qed
qed
end


definition af_compatible_status :: "'f af \<Rightarrow> 'f status \<Rightarrow> bool"
where
  "af_compatible_status \<pi> \<sigma> \<longleftrightarrow> (\<forall> f m. set (status \<sigma> (f, m)) \<subseteq> \<pi> (f, m))"

lemma af_compatible_status_full_af: "af_compatible_status full_af \<sigma>"
  unfolding af_compatible_status_def full_af_def using status[of \<sigma>] by auto

locale wpo_params = ws_rewrite_order S NS \<sigma>\<sigma> + precedence prc prl
  for NS S :: "('f, 'v) trs" 
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and ssimple :: bool
    and large :: "'f \<times> nat \<Rightarrow> bool" 
    and c :: "'f \<times> nat \<Rightarrow> order_tag"
    and n :: nat
    and \<sigma>\<sigma> :: "'f status" +
  assumes large: "ssimple \<Longrightarrow> large fn \<Longrightarrow> fst (prc fn gm) \<or> snd (prc fn gm) \<and> status \<sigma>\<sigma> gm = []"  
  and large_trans: "ssimple \<Longrightarrow> large fn \<Longrightarrow> snd (prc gm fn) \<Longrightarrow> large gm"  
  and strictly_simple: "ssimple \<Longrightarrow> ss_rewrite_order S NS \<sigma>\<sigma>" 
  and irrefl_S: "irrefl S" 
begin

sublocale wpo_with_assms
proof (unfold_locales; (intro S_imp_NS large ws_status S_stable NS_stable NS_mono irrefl_S; assumption)?)
  assume ssimple
  show "large fn \<Longrightarrow> snd (prc gm fn) \<Longrightarrow> large gm" for fn gm by (rule large_trans[OF `ssimple`])
  interpret ss_rewrite_order S NS \<sigma>\<sigma> by (rule strictly_simple[OF `ssimple`])
  show "S \<noteq> {}" by (rule S_non_empty)
  show "i \<in> set (status \<sigma>\<sigma> fn) \<Longrightarrow> simple_arg_pos S fn i " for fn i by (rule ss_status)
qed

lemma wpo_with_SN_assms: assumes "SN S" 
  shows "wpo_with_SN_assms S NS prc prl \<sigma>\<sigma> ssimple large" 
  by (unfold_locales, rule assms)

lemma ce_\<sigma>: assumes "{0,1} \<subseteq> set (\<sigma> (f,Suc (Suc k)))"
  shows "ce_trs (f,k) \<subseteq> WPO_S \<and> ce_trs (f,k) \<subseteq> WPO_NS"
proof -
  {
    fix s t :: "('f,'v)term"
    assume "(s,t) \<in> ce_trs (f,k)"
    from this[unfolded ce_trs.simps] 
    obtain u v where s: "s = Fun f (u # v # replicate k (Var undefined))" (is "_ = Fun _ ?ss")
      and t: "t = u \<or> t = v" by auto
    from t subterm_wpo_s_arg[of 0 f ?ss] subterm_wpo_s_arg[of 1 f ?ss] assms 
    have "(s,t) \<in> WPO_S" unfolding s by (cases, auto)
  }
  then show ?thesis using wpo_s_imp_ns by blast
qed

context
  fixes \<pi> :: "'f af"
  assumes af_NS: "af_compatible \<pi> NS"
  and af_\<sigma>: "af_compatible_status \<pi> \<sigma>\<sigma>"
begin

lemma af_\<sigma>: "i < m \<Longrightarrow> i \<in> \<pi> (f,m) \<or> i \<notin> set (\<sigma> (f,m))"
  using af_\<sigma>[unfolded af_compatible_status_def] by blast

lemma wpo_af_compatible: "af_compatible \<pi> WPO_NS"
  unfolding af_compatible_def
proof (intro allI)
  fix f and bef aft :: "('f,'v)term list" and s t
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  let ?\<sigma> = "\<sigma> (f,?n)"
  show "?i \<in> \<pi> (f, ?n) \<or> (?s, ?t) \<in> WPO_NS" 
  proof (cases "?i \<in> \<pi> (f, ?n)")
    case False
    have i: "?i < ?n" by auto
    from af_\<sigma>[OF i, of f] False have i\<sigma>: "?i \<notin> set ?\<sigma>" by auto
    from af_NS[unfolded af_compatible_def, rule_format, of bef f aft s t] False
    have id: "((?s, ?t) \<in> NS) = True" "length ?ss = ?n" "length ?ts = ?n" by auto
    have "\<forall>j\<in>set ?\<sigma>. wpo_s ?s (?ts ! j)" (is ?one)
    proof
      fix j
      assume j: "j \<in> set ?\<sigma>"
      with i\<sigma> have ji: "j \<noteq> ?i" by auto
      then have id: "?ts ! j = ?ss ! j" by (rule append_Cons_nth_not_middle)      
      show "wpo_s ?s (?ts ! j)" unfolding id 
        by (rule subterm_wpo_s_arg, insert j, auto)
    qed
    then have one: "?one = True" by simp
    have two: "map ((!) ?ts) ?\<sigma> = map ((!) ?ss) ?\<sigma>" (is "?mts = ?mss")
    proof (rule nth_equalityI, force, unfold length_map)
      fix i
      assume i: "i < length ?\<sigma>"
      with i\<sigma> have "?\<sigma> ! i \<noteq> ?i" unfolding set_conv_nth by auto
      then show "?mts ! i = ?mss ! i" using i by (simp add: nth_append)
    qed
    have "snd (lex_ext wpo n ?mss ?mts)" unfolding two
      by (rule all_nstri_imp_lex_nstri, insert wpo_ns_refl, auto)
    moreover have "snd (mul_ext wpo ?mss ?mts)" unfolding two
      by (rule all_nstri_imp_mul_nstri, insert wpo_ns_refl, auto) 
    ultimately have "wpo_ns ?s ?t" unfolding wpo.simps[of ?s ?t] term.simps id one
      prc_refl by (cases "c (f,?n)", auto simp: Let_def)
    then show ?thesis by blast
  qed simp
qed
end

lemma wpo_ce_compat: 
  assumes ce: "\<exists>n. \<forall>m\<ge>n. \<forall> f. {0,1} \<subseteq> set (\<sigma> (f, Suc (Suc m)))"
  shows "ce_compatible WPO_NS" "ce_compatible WPO_S" 
proof -
  from assms obtain n where "\<And> m f. m \<ge> n \<Longrightarrow> {0,1} \<subseteq> set (\<sigma> (f, Suc (Suc m)))" by blast
  from ce_\<sigma>[OF this] show "ce_compatible WPO_NS" "ce_compatible WPO_S" 
    unfolding ce_compatible_def by blast+ 
qed
  

lemma wpo_ce_af_redtriple_order: 
  assumes ce: "\<exists>n. \<forall>m\<ge>n. \<forall> f. {0,1} \<subseteq> set (\<sigma> (f, Suc (Suc m)))"
  and pi: "af_compatible \<pi> NS" "af_compatible_status \<pi> \<sigma>\<sigma>"
  and SN: "SN S" 
  shows "ce_af_redtriple_order WPO_S WPO_NS WPO_NS \<pi>"
proof -
  from wpo_with_SN_assms[OF SN]
  interpret wpo_with_SN_assms n S NS prc prl \<sigma>\<sigma> c ssimple large .
  interpret redtriple_order WPO_S WPO_NS WPO_NS by (rule wpo_redtriple_order)
  from wpo_ce_compat[OF ce] have "ce_compatible WPO_NS" "ce_compatible WPO_S" by auto
  with wpo_af_compatible[OF pi]
  show ?thesis using full_af by (unfold_locales, blast+)
qed 
    
  
context
  assumes \<sigma>_full: "\<And> f k. set (\<sigma> (f,k)) = {0 ..< k}"
begin

lemma ctxt_closed_WPO_S: "ctxt.closed WPO_S" 
  using one_imp_ctxt_closed[OF WPO_S_ctxt[OF \<sigma>_full]] by blast

lemma wpo_mono_ce_af_redtriple_order: 
  assumes ce: "\<exists>n. \<forall>m\<ge>n. \<forall> f. {0,1} \<subseteq> set (\<sigma> (f, Suc (Suc m)))"
  and pi: "af_compatible \<pi> NS" "af_compatible_status \<pi> \<sigma>\<sigma>"
  and SN: "SN S" 
shows "mono_ce_af_redtriple_order WPO_S WPO_NS WPO_NS \<pi>"
proof -
  interpret ce_af_redtriple_order WPO_S WPO_NS WPO_NS \<pi>
    by (rule wpo_ce_af_redtriple_order[OF ce pi SN])
  show ?thesis
  proof (unfold_locales)
    show "ctxt.closed WPO_S" by (rule ctxt_closed_WPO_S)
    show "ce_compatible WPO_S" unfolding ce_compatible_def
      using ce_\<sigma>[unfolded \<sigma>_full] by auto
  qed
qed
    
end
end

definition af_wpo :: "'f af \<Rightarrow> 'f status \<Rightarrow> 'f af"
  where
    "af_wpo \<pi> \<sigma> f = set (status \<sigma> f) \<union> \<pi> f"

lemma af_wpo_compat: "af_compatible \<pi> NS \<Longrightarrow> af_compatible (af_wpo \<pi> \<sigma>) NS"
  unfolding af_compatible_def af_wpo_def by auto

lemma af_wpo_status: "af_compatible_status (af_wpo \<pi> \<sigma>) \<sigma>"
  unfolding af_compatible_status_def af_wpo_def by auto

abbreviation var_x_i :: "nat => ('f, string) term"
  where
    "var_x_i i == Var (''x'' @ show i)"

fun check_status_ws_info :: "'f status \<Rightarrow> (('f, string) rule \<Rightarrow> showsl check) \<Rightarrow> (('f :: showl) \<times> nat) list option \<Rightarrow> showsl check"
  where
    "check_status_ws_info \<sigma> cns None = error (showsl_lit (STR ''missing weak-subterm status of base reduction pair''))"
  | "check_status_ws_info \<sigma> cns (Some fs) = check_allm (\<lambda>(f, n).
      check_allm (\<lambda>i.
        let s = Fun f (map var_x_i [0..<n]); t = var_x_i i in
        cns (s, t)
        <+? (\<lambda>_. showsl_lit (STR ''argument #'') \<circ> showsl (Suc i) \<circ>
          showsl_lit (STR '' is in status of '') \<circ> showsl_funa (f, n) \<circ> showsl_nl \<circ>
          showsl_lit (STR ''but '') \<circ> showsl s \<circ> showsl_lit (STR '' >= '') \<circ> showsl_nat_var i \<circ>
          showsl_lit (STR '' is not satisfied''))) (status \<sigma> (f, n))) fs"

type_synonym 'f wpo_params = "(('f \<times> nat) \<times> (nat \<times> nat list \<times> order_tag)) list"

definition showsl_wpo_params :: "('f :: showl) wpo_params \<Rightarrow> showsl" where
  "showsl_wpo_params params = showsl_lit (STR ''status and precedence:\<newline>'') \<circ>
    showsl_sep (\<lambda>(f, (p, s, lm)).
      showsl_lit (STR ''precedence('') \<circ> showsl_funa f \<circ> showsl_lit (STR '') = '') \<circ> showsl p \<circ> showsl_nl \<circ>
      showsl_lit (STR ''  status('') \<circ> showsl_funa f \<circ> showsl_lit (STR '') = '') \<circ> showsl_list s \<circ> showsl_nl o
      showsl_lit (STR ''  arg-status('') \<circ> showsl_funa f \<circ> showsl_lit (STR '') = '') \<circ> showsl (case lm of Mul \<Rightarrow> STR ''mul'' | Lex \<Rightarrow> STR ''lex'') \<circ> showsl_nl
    ) showsl_nl params"

definition large_of where 
  "large_of pr \<sigma> fs = (let m = max_list (map pr fs);
     ls = filter (\<lambda> f. pr f = m) fs
     in if m > 0 \<and> (\<forall> f \<in> set ls. status \<sigma> f = []) then Some m else None)" 

definition wpo_rel_impl :: "('f :: {compare_order, showl}, string) rel_impl \<Rightarrow> 'f wpo_params \<Rightarrow> ('f, string) rel_impl"
  where
    "wpo_rel_impl rt params \<equiv>
      (let
        stat = map (\<lambda> (f,ps). (f, fst (snd ps))) params;
        mparams = ceta_map_of params;
        pr = fun_of_map_fun' mparams (\<lambda> _. 0) fst;
        ot = fun_of_map_fun' mparams (\<lambda> _. Lex) (snd o snd);
        desc1 = showsl_lit (STR ''WPO '');
        desc2 = showsl_lit (STR ''with '') o showsl_wpo_params params \<circ>
          showsl_lit (STR ''\<newline>over the following reduction pair:\<newline>'') \<circ> rel_impl.desc rt
      in
        (case status_of stat of
          None \<Rightarrow> faulty_rel_impl (TYPE('f)) (TYPE(string)) (showsl_lit (STR ''problem with indices in status of WPO!'')) (desc1 o desc2)
        | Some \<sigma> \<Rightarrow>
          let
            large_opt = large_of pr \<sigma> (map fst params);
            ssimple = \<not> is_None large_opt \<and> isOK(check_status_ws_info \<sigma> (rel_impl.s rt) (rel_impl.not_sst rt));
            large = (if ssimple then \<lambda> f. pr f = the large_opt else (\<lambda> _. False));
            s = (\<lambda> s t. isOK (rel_impl.s rt (s, t)));
            ns = (\<lambda> s t. isOK (rel_impl.ns rt (s, t)));
            wpo = wpo_ub (prc_nat pr) (prl_nat pr) ssimple large s ns \<sigma> ot;
            wpo_s = (\<lambda> (s,t). check (fst (wpo s t)) (showsl s \<circ> showsl_lit (STR '' >wpo '') \<circ> showsl t \<circ> showsl_lit (STR '' could not be ensured'')));
            wpo_ns = (\<lambda> (s,t). check (snd (wpo s t)) (showsl s \<circ> showsl_lit (STR '' >=wpo '') \<circ> showsl t \<circ> showsl_lit (STR '' could not be ensured'')))
          in \<lparr>
            rel_impl.valid = do { 
              rel_impl.valid rt; 
              rel_impl.standard rt; 
              rel_impl.subst_s rt <+? (\<lambda> e. showsl_lit (STR ''WPO requires stability of strict base relation\<newline>'') o e);
              check_status_ws_info \<sigma> (rel_impl.ns rt) (rel_impl.not_wst rt) 
            },
            standard = succeed,
            desc = if ssimple then desc1 o showsl_lit (STR ''(strictly simple) '') o desc2 else desc1 o desc2,
            s = wpo_s,
            ns = wpo_ns,
            nst = wpo_ns,
            af = af_wpo (rel_impl.af rt) \<sigma>,
            top_af = af_wpo (rel_impl.af rt) \<sigma>,
            SN = rel_impl.SN rt,
            subst_s = succeed,
            ce_compat = succeed,
            co_rewr = succeed,
            top_mono = succeed,
            top_refl = succeed,
            mono_af = empty_af, \<comment> \<open>TODO: this is too crude\<close>
            mono = (\<lambda>_. check_allm (\<lambda>((f, n), idx). check (set idx = set [0..<n]) (
              showsl_lit (STR ''for monotonicity, status must be complete, but status of '') \<circ>
              showsl_funa (f, n) \<circ> showsl_lit (STR '' is '') \<circ> showsl (map Suc idx))) stat),
            not_wst = Some (map fst stat),
            not_sst = Some (map fst stat),
            cpx = no_complexity_check
          \<rparr>))"

lemma wpo_rel_impl: assumes rt: "rel_impl rt"
  shows "rel_impl (wpo_rel_impl rt param)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?rp = "wpo_rel_impl rt param"
  let ?pi = "rel_impl.af ?rp"
  let ?mpi = "rel_impl.mono_af ?rp"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?Cpx = "\<lambda> cm cc. isOK(?cpx cm cc)"
  let ?s = "\<lambda> s t. isOK(rel_impl.s ?rp (s,t))"
  let ?ns = "\<lambda> s t. isOK(rel_impl.ns ?rp (s,t))"
  let ?stat = "map (\<lambda> (f,ps). (f, fst (snd ps))) param"
  let ?ot = "fun_of_map_fun' (ceta_map_of param) (\<lambda> _. Lex) (snd o snd)" 
  let ?rp' = "rt"
  let ?pi' = "rel_impl.af ?rp'"
  let ?mpi' = "rel_impl.mono_af ?rp'"
  let ?cpx' = "rel_impl.cpx ?rp'"
  let ?Cpx' = "\<lambda> cm cc. isOK(?cpx' cm cc)"
  let ?s' = "\<lambda> s t. isOK(rel_impl.s ?rp' (s,t))"
  let ?ns' = "\<lambda> s t. isOK(rel_impl.ns ?rp' (s,t))"
  let ?pr = "fun_of_map_fun' (ceta_map_of param) (\<lambda> _. 0) fst"
  let ?ws' = "rel_impl.not_wst ?rp'"
  let ?ss' = "rel_impl.not_sst ?rp'"
  define pr where "pr = ?pr" 
  define ot where "ot = ?ot" 
  let ?prc = "prc_nat pr"
  let ?prl = "prl_nat pr"
  note d = wpo_rel_impl_def[of rt param, unfolded Let_def]
  from 1 d obtain \<sigma> where stat: "status_of ?stat = Some \<sigma>" by (cases "status_of ?stat", auto)
  note d = d[unfolded stat option.simps rel_impl.simps]
  have top_af: "rel_impl.top_af ?rp = ?pi" unfolding d by auto
  let ?large_opt = "large_of pr \<sigma> (map fst param)" 
  define ssimple where "ssimple = (\<not> is_None ?large_opt \<and> isOK (check_status_ws_info \<sigma> (rel_impl.s rt) (rel_impl.not_sst rt)))" 
  define large where "large = (if ssimple then \<lambda> f. pr f = (the ?large_opt) else (\<lambda> _ :: ('a \<times> nat). False))" 
  note d = d[folded pr_def, folded ssimple_def, folded large_def, folded ot_def]
  
  note 1 = 1[unfolded d, simplified]
  let ?wpo = "wpo_ub (prc_nat pr) (prl_nat pr) ssimple large ?s' ?ns' \<sigma> ot"
  from 1 have status_ws: "isOK(check_status_ws_info \<sigma> (rel_impl.ns ?rp') ?ws')" 
    and "isOK(rel_impl.valid ?rp')" by auto
  note rt = rt[unfolded rel_impl_def, rule_format, OF this(2)]
  from status_ws obtain fs where ws': "?ws' = Some fs" by (cases ?ws', auto)
  from status_ws[unfolded ws']
  have status_ws: "\<And>f n i. (f, n) \<in> set fs \<Longrightarrow> i \<in> set (status \<sigma> (f, n)) \<Longrightarrow>
    ?ns' (Fun f (map var_x_i [0..<n])) (var_x_i i)" by auto
  have status_ss: "\<And>f n i. ssimple \<Longrightarrow> (f, n) \<in> set (the ?ss') \<Longrightarrow> i \<in> set (status \<sigma> (f, n)) \<Longrightarrow>
    ?s' (Fun f (map var_x_i [0..<n])) (var_x_i i)" unfolding ssimple_def by (cases ?ss', auto)
  define subts where "subts = [(u,v) . (s,t) <- U, u <- supteq_list s, v <- supteq_list t]"
  define s where "s = subts @ [(Fun f (map var_x_i [0..<n]), var_x_i i :: ('a, _) Term.term). (f, n) <- the ?ss', i <- status \<sigma> (f, n)]" 
  define ns where "ns = subts @ [(Fun f (map var_x_i [0..<n]), var_x_i i). (f, n) <- fs, i <- status \<sigma> (f, n)]"
  let ?U = "s @ ns" 
  from rt[of ?U] obtain S NS NST where rt: "rel_impl_prop rt ?U S NS NST" by presburger
  from rt 1 have
      *: "S \<subseteq> NS" "irrefl S" "ctxt.closed NS" "S O NS \<subseteq> S" "NS O S \<subseteq> S" "trans NS" "refl NS"
    and subst_NS: "subst.closed NS"  
    and subst_S: "subst.closed S" 
    and af_compat: "af_compatible (rel_impl.af rt) NS" 
    and ws: "not_subterm_rel_info NS ?ws'" 
    and sst: "not_subterm_rel_info S ?ss'"
    and SN: "isOK( rel_impl.SN rt) \<Longrightarrow> SN S" 
    by (auto simp: rel_impl_def)
  have "set s \<subseteq> set ?U" "set ns \<subseteq> set ?U"
    by (auto simp: ns_def)
  with rt[THEN conjunct1] 
  have orient: "\<And> l r. ?s' l r \<Longrightarrow> (l,r) \<in> set s \<Longrightarrow> (l,r) \<in> S" 
     "\<And> l r. ?ns' l r \<Longrightarrow> (l,r) \<in> set ns \<Longrightarrow> (l,r) \<in> NS" 
    by auto
  define n where "n = max_list [ length (status \<sigma> f) . (s,t) <- U, f <- funas_term_list t]"
  interpret precedence ?prc ?prl ..
  note cb = compare_bools_def
  let ?wpoo = "wpo_orig ?prc ?prl ssimple large \<sigma> ot n S NS"
  {
    fix s t
    assume st: "(s,t) \<in> set U"
    have "?wpo s t \<le>\<^sub>c\<^sub>b ?wpoo s t"
    proof (rule wpo_ub)
      fix si tj
      assume "s \<unrhd> si" "t \<unrhd> tj"
      with st have sitj: "(si,tj) \<in> set subts" unfolding subts_def by force
      with orient
      show "(?s' si tj, ?ns' si tj)
       \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)" unfolding s_def ns_def cb by auto
    next
      fix f
      assume f: "f \<in> funas_term t"
      show "length (status \<sigma> f) \<le> n" unfolding n_def
        by (rule max_list, insert f st, auto)
    qed
  } note cb_all = this[unfolded cb]
  interpret wpo_params NS S ?prc ?prl ssimple large ot n \<sigma> 
  proof (unfold_locales; (intro subst_S subst_NS *)?)
    from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> show "trans S" unfolding trans_def by auto  
    show "trans S" by fact
    fix i fn 
    assume i: "i \<in> set (status \<sigma> fn)"
    obtain f n where f: "fn = (f,n)" by force
    show "simple_arg_pos NS fn i"
    proof (cases "fn \<in> set fs")
      case False
      with ws[unfolded ws'] show ?thesis by (auto simp: f)
    next
      case True
      let ?l = "Fun f (map var_x_i [0..<n])"
      let ?r = "var_x_i i"
      have ns: "(?l, ?r) \<in> NS" using orient(2)[OF status_ws] i True unfolding ns_def f by force
      show ?thesis unfolding f
      proof (rule simple_arg_posI)
        fix ts :: "('a,string)term list"
        assume len: "length ts = n" and i: "i < n"
        define inv where "inv = (\<lambda>s. ts ! the_inv show (tl s))"
        {
          fix i
          have "inv (the_Var (var_x_i i)) = ts ! i" unfolding inv_def
            using the_inv_f_f[OF inj_show_nat] by auto
        }
        with subst.closedD[OF subst_NS ns, of inv]
        show "(Fun f ts, ts ! i) \<in> NS"
          by (auto simp: o_def len[symmetric] map_nth)
      qed
    qed
    show "simple_arg_pos NS fn i" by fact
  next
    assume ssimple: ssimple
    then obtain gs where sst': "?ss' = Some gs" unfolding ssimple_def by (cases ?ss', auto)
    {
      fix i fn 
      assume i: "i \<in> set (status \<sigma> fn)"
      obtain f n where f: "fn = (f,n)" by force
      show "simple_arg_pos S fn i"
      proof (cases "fn \<in> set gs")
        case False
        with sst[unfolded sst'] show ?thesis by (auto simp: f)
      next
        case True
        let ?l = "Fun f (map var_x_i [0..<n])"
        let ?r = "var_x_i i"
        have s: "(?l, ?r) \<in> S" using orient(1)[OF status_ss[OF ssimple]] i True unfolding s_def f sst' by force
        show ?thesis unfolding f
        proof (rule simple_arg_posI)
          fix ts :: "('a,string)term list"
          assume len: "length ts = n" and i: "i < n"
          define inv where "inv = (\<lambda>s. ts ! the_inv show (tl s))"
          {
            fix i
            have "inv (the_Var (var_x_i i)) = ts ! i" unfolding inv_def
              using the_inv_f_f[OF inj_show_nat] by auto
          }
          with subst.closedD[OF subst_S s, of inv]
          show "(Fun f ts, ts ! i) \<in> S"
            by (auto simp: o_def len[symmetric] map_nth)
        qed
      qed
    }
    {
      obtain f :: 'a where True by auto
      define n where "n = 1 + max_list (map snd gs)" 
      have "(f,n) \<notin> set gs"
      proof
        assume "(f,n) \<in> set gs" 
        hence "n \<in> set (map snd gs)" by auto
        from max_list[OF this] show False unfolding n_def by simp
      qed
      from sst[unfolded sst', simplified, rule_format, OF this]
      have "simple_arg_pos S (f, n) 0" unfolding n_def by auto
      from this[unfolded simple_arg_pos_def, simplified, rule_format, of "replicate n undefined"]
      obtain a b where ab: "(a,b) \<in> S" unfolding n_def by auto
      thus "S \<noteq> {}" by auto
    }
    from ssimple obtain m where large_opt: "?large_opt = Some m" unfolding ssimple_def by (cases ?large_opt, auto)
    fix f g
    assume lf: "large f" 
    have large: "\<And> g. large g = (pr g = m)" unfolding large_def large_opt using ssimple by auto
    note large_opt = large_opt[unfolded large_of_def Let_def]
    from large_opt have m: "m > 0" by (auto split: if_splits)
    have snd: "snd (?prc g f) = (pr g \<ge> pr f)" for g f unfolding prc_nat_def Let_def by simp
    have fst: "fst (?prc g f) = (pr g > pr f)" for g f unfolding prc_nat_def Let_def by simp
    from large_opt have max: "\<And> f. f \<in> set (map fst param) \<Longrightarrow> pr f \<le> m"
      by (force split: if_splits option.splits intro!: max_list) 
    have 0: "\<And> f. f \<notin> set (map fst param) \<Longrightarrow> pr f = 0" unfolding pr_def ceta_map_of fun_of_map_fun'.simps
      using map_of_eq_None_iff[of param] by force
    from large_opt have status: "\<And> f. f \<in> set (map fst param) \<Longrightarrow> pr f = m \<Longrightarrow> status \<sigma> f = []"
      by (auto split: if_splits)
    show "snd (?prc g f) \<Longrightarrow> large g" using max[of g] 0 lf unfolding large fst snd by fastforce
    thus "fst (?prc f g) \<or> snd (?prc f g) \<and> status \<sigma> g = []" using status[of g] max[of g] m 0
      unfolding large fst snd by (metis large lf status nat_le_linear nat_less_le)
    
  qed
  from af_compat have "af_compatible ?pi' NS" .
  from af_wpo_compat[OF this, of \<sigma>] have pi: "af_compatible ?pi NS"
    unfolding param d split by auto
  from af_wpo_status[of ?pi' \<sigma>] have pi2: "af_compatible_status ?pi \<sigma>"
    unfolding param d split by auto
  let ?m = "max_list (map (snd o fst) ?stat)"
  have \<sigma>: "\<exists>n. \<forall>m\<ge>n. \<forall>f. {0, 1} \<subseteq> set (status \<sigma> (f, Suc (Suc m)))"
  proof (rule exI[of _ ?m], intro allI impI)
    fix k f
    assume k: "?m \<le> k"
    let ?k = "Suc (Suc k)"
    from k have "?m < ?k" by auto
    with max_list[of ?k "map (snd o fst) ?stat"] 
    have "(f,?k) \<notin> fst ` set ?stat" by force
    from status_of_default[OF stat this]
    show "{0,1} \<subseteq> set (status \<sigma> (f,Suc (Suc k)))" by auto
  qed
  let ?S = WPO_S
  let ?NS = WPO_NS
  from wpo_rewrite_order 
  interpret rewrite_order WPO_S WPO_NS .
  from wpo_co_rewrite_pair
  interpret co_rewrite_pair WPO_S WPO_NS .
  from wpo_order_pair
  interpret order_pair WPO_S WPO_NS .
  have mpi: "?mpi = empty_af" unfolding wpo_rel_impl_def Let_def stat
    by simp
  let ?ws = "rel_impl.not_wst ?rp"
  let ?ss = "rel_impl.not_sst ?rp"
  have "not_subterm_rel_info ?NS (Some (map fst ?stat)) \<and> not_subterm_rel_info ?S (Some (map fst ?stat))" 
    unfolding not_subterm_rel_info.simps
  proof (intro allI impI conjI)
    fix fk i
    assume nmem: "fk \<notin> set (map fst ?stat)"
    obtain f k where f: "fk = (f,k)" by force
    with nmem have "(f,k) \<notin> fst ` set ?stat" by force
    from status_of_default[OF stat this]
      subterm_wpo_s_arg[of _ f] subterm_wpo_ns_arg[of _ f] 
    show "simple_arg_pos ?S fk i" "simple_arg_pos ?NS fk i" unfolding f
      by (intro simple_arg_posI, auto)+
  qed
  then have 4: "not_subterm_rel_info ?NS ?ws" 
    and 5: "not_subterm_rel_info ?S ?ss" by (auto simp add: d)
  show ?case unfolding top_af mpi
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI 4 5 impI allI
     S_imp_NS ctxt_NS refl_NS trans_NS trans_S compat_NS_S compat_S_NS subst_S subst_NS 
     af_compat empty_af top_mono_same irrefl_S disj_NS_S)
    {
      fix st
      assume stU: "st \<in> set U" 
      obtain s t where st: "st = (s,t)" by force
      hence "(s,t) \<in> set U" using stU by auto
      note cb_all = cb_all[OF this]
      show "isOK (rel_impl.s ?rp st) \<Longrightarrow> st \<in> WPO_S" 
        using cb_all unfolding d st by auto
      show "isOK (rel_impl.ns ?rp st) \<Longrightarrow> st \<in> WPO_NS"
        using cb_all unfolding d st by auto
      show "isOK (rel_impl.nst ?rp st) \<Longrightarrow> st \<in> WPO_NS" 
        using cb_all unfolding d st by auto
    }
    {
      fix sig
      assume mono: "isOK (rel_impl.mono ?rp sig)"
      have "set (status \<sigma> (f, m)) = {0..<m}" for f m
      proof (cases "map_of ?stat (f,m)")
        case None
        from status_of_default[OF stat this[unfolded map_of_eq_None_iff]] 
        show ?thesis by auto
      next
        case (Some idx)
        from map_of_SomeD[OF this] mono show ?thesis
          by (auto simp: d status_of_Some[OF stat] Some)
      qed
      from ctxt_closed_WPO_S[OF this] 
      show "ctxt.closed ?S" .
    }
    show "ce_compatible ?NS" "ce_compatible ?S" using wpo_ce_compat[OF \<sigma>] by auto
    show "af_compatible ?pi ?NS" "af_compatible ?pi ?NS" using wpo_af_compatible[OF pi pi2] by auto
    show "WPO_S \<subseteq> WPO_NS" by (rule WPO_S_subset_WPO_NS)
    {
      assume "isOK (rel_impl.SN ?rp)" 
      hence "isOK (rel_impl.SN rt)" unfolding d by auto
      from SN[OF this] have SN: "SN S" .
      from wpo_with_SN_assms.WPO_S_SN[OF wpo_with_SN_assms[OF this], of]
      show "SN ?S" .
    }     
    show "irrefl WPO_S" using wpo_irrefl unfolding irrefl_on_def by auto
  qed (auto simp: wpo_rel_impl_def stat Let_def isOK_no_complexity)
qed

end