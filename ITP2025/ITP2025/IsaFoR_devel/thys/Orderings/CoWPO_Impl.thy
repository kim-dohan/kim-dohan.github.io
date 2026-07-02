(*
  René Thiemann
*)
theory CoWPO_Impl
  imports
    WPO_Impl
    CoWPO
begin

locale co_wpo_params = order_pair' S NS + precedence prc "\<lambda> _. False"
  for NS S :: "('f, 'v) trs" 
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and n :: nat
    and \<sigma>\<sigma> :: "'f status" +
  assumes ws_status: "i \<in> set (status \<sigma>\<sigma> f) \<Longrightarrow> simple_arg_pos NS f i"
    and S_imp_NS: "S \<subseteq> NS"
    and subst_S: "subst.closed S" 
    and subst_NS: "subst.closed NS" 
    and ctxt_NS: "ctxt.closed NS" 
begin


abbreviation invS where "invS \<equiv> {(s,t). \<forall> \<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> S}" 
abbreviation invNS where "invNS \<equiv> {(s,t). \<forall> \<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> NS}"

sublocale co: cowpo_with_assms S NS n \<sigma>\<sigma> "\<lambda> _. Lex" invNS invS "\<lambda> fn gn. \<not> snd (prc gn fn)" "\<lambda> fn gn. \<not> fst (prc gn fn)" "\<lambda> fn gn. fst (prc fn gn)" "\<lambda> fn gn. snd (prc fn gn)" 
proof (unfold_locales; (intro refl_NS trans_NS refl S_imp_NS ws_status subst.closedD[OF subst_S] subst.closedD[OF subst_NS] ctxt_closed_one[OF ctxt_NS]; assumption)?; 
    (unfold fst_conv snd_conv)?; (elim FalseE)?)
  show "(fst (prc f f), snd (prc f f)) = (False, True)" for f
    by (simp add: prc_refl)
  show "fst (prc f g) \<Longrightarrow> snd (prc f g)" for f g by (rule prc_stri_imp_nstri)
  show "(fst (prc f g), snd (prc f g)) = (s1, ns1) \<Longrightarrow>
       (fst (prc g h), snd (prc g h)) = (s2, ns2) \<Longrightarrow>
       (fst (prc f h), snd (prc f h)) = (s, ns) \<Longrightarrow> (ns1 \<and> ns2 \<longrightarrow> ns) \<and> (ns1 \<and> s2 \<longrightarrow> s) \<and> (s1 \<and> ns2 \<longrightarrow> s)" 
    for f g s1 ns1 h s2 ns2 s ns by (metis prc_compat prod.collapse)
qed 

lemma cowpo_corewrite_pair: "co_rewrite_pair co.COWPO_S co.WPO_NS" 
proof (rule co.co_rewrite_pair_wpo_cowpo[OF _ ctxt_NS])
  show "prc_compat' (\<lambda>fn gn. fst (prc fn gn)) (\<lambda>fn gn. snd (prc fn gn))" 
    by (smt (verit) co.prc_stri_imp_nstri prc_compat prc_compat'_def prod.collapse)
  show "strictly_simple_status \<sigma>\<sigma> NS" 
    unfolding strictly_simple_status_def
  proof (intro allI impI, goal_cases) 
    case (1 f ts i)
    thus ?case using 
        ws_status[unfolded simple_arg_pos_def, of i "(f,length ts)"] 
        status[of \<sigma>\<sigma> f "length ts"]
      by auto
  qed
qed simp
end


definition cowpo_rel_impl :: "('f :: {compare_order, showl}, string) rel_impl \<Rightarrow> 'f wpo_params \<Rightarrow> ('f, string) rel_impl"
  where
    "cowpo_rel_impl rt params \<equiv>
      (let
        stat = map (\<lambda> (f,ps). (f, fst (snd ps))) params;
        mparams = ceta_map_of params;
        pr = fun_of_map_fun' mparams (\<lambda> _. 0) fst;
        ot = (\<lambda> _. Lex);
        desc1 = showsl_lit (STR ''Co-WPO '');
        desc2 = showsl_lit (STR ''with '') o showsl_wpo_params params \<circ>
          showsl_lit (STR ''\<newline>over the following relation:\<newline>'') \<circ> rel_impl.desc rt
      in
        (case status_of stat of
          None \<Rightarrow> faulty_rel_impl (TYPE('f)) (TYPE(string)) (showsl_lit (STR ''problem with indices in status of co-WPO!'')) (desc1 o desc2)
        | Some \<sigma> \<Rightarrow>
          let
            large = (\<lambda> _. False);
            ssimple = False;
            s = (\<lambda> s t. isOK (rel_impl.s rt (s, t)));
            ns = (\<lambda> s t. isOK (rel_impl.ns rt (s, t)));
            wpo = wpo_ub (prc_nat pr) (\<lambda> _. False) ssimple large s ns \<sigma> ot;
            invS = ns; \<comment> \<open>this is just a sufficient criterion\<close>
            invNS = s; \<comment> \<open>this is just a sufficient criterion\<close>
            cowpo = wpo_ub (\<lambda>f g. (\<not> snd (prc_nat pr g f), \<not> fst (prc_nat pr g f))) (\<lambda> _. False) ssimple large invNS invS \<sigma> ot;
            wpo_s = (\<lambda> (s,t). check (fst (cowpo s t)) (showsl s \<circ> showsl_lit (STR '' >co-wpo '') \<circ> showsl t \<circ> showsl_lit (STR '' could not be ensured'')));
            wpo_ns = (\<lambda> (s,t). check (snd (wpo s t)) (showsl s \<circ> showsl_lit (STR '' >=wpo '') \<circ> showsl t \<circ> showsl_lit (STR '' could not be ensured'')))
          in \<lparr>
            rel_impl.valid = do { 
              rel_impl.valid rt; 
              rel_impl.standard rt; 
              rel_impl.subst_s rt <+? (\<lambda> e. showsl_lit (STR ''Co-WPO requires stability of strict base relation\<newline>'') o e);
              check_status_ws_info \<sigma> (rel_impl.ns rt) (rel_impl.not_wst rt) 
            },
            standard = error (showsl_lit (STR ''Co-WPO does not support standard properties'')),
            desc = desc1 o desc2,
            s = wpo_s,
            ns = wpo_ns,
            nst = (\<lambda> _. error (showsl_lit (STR ''Co-WPO does not support nst-comparisons''))),
            af = full_af,
            top_af = full_af,
            SN = error (showsl_lit (STR ''Co-WPO does not support SN'')),
            subst_s = succeed,
            ce_compat = error (showsl_lit (STR ''Co-WPO does not support Ce'')),
            co_rewr = succeed,
            top_mono = error (showsl_lit (STR ''Co-WPO does not support top-mono'')),
            top_refl = error (showsl_lit (STR ''Co-WPO does not support top-refl'')),
            mono_af = empty_af, 
            mono = (\<lambda> _. error (showsl_lit (STR ''Co-WPO does not support strong monotonicity''))),
            not_wst = None,
            not_sst = None,
            cpx = no_complexity_check
          \<rparr>))"

lemma cowpo_rel_impl: assumes rt: "rel_impl rt"
  shows "rel_impl (cowpo_rel_impl rt param)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?rp = "cowpo_rel_impl rt param"
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
  note d = cowpo_rel_impl_def[of rt param, unfolded Let_def]
  from 1 d obtain \<sigma> where stat: "status_of ?stat = Some \<sigma>" by (cases "status_of ?stat", auto)
  note d = d[unfolded stat option.simps rel_impl.simps, folded pr_def]  
  note 1 = 1[unfolded d, simplified]
  from 1 have status_ws: "isOK(check_status_ws_info \<sigma> (rel_impl.ns ?rp') ?ws')" 
    and "isOK(rel_impl.valid ?rp')" by auto
  note rt = rt[unfolded rel_impl_def, rule_format, OF this(2)]
  from status_ws obtain fs where ws': "?ws' = Some fs" by (cases ?ws', auto)
  from status_ws[unfolded ws']
  have status_ws: "\<And>f n i. (f, n) \<in> set fs \<Longrightarrow> i \<in> set (status \<sigma> (f, n)) \<Longrightarrow>
    ?ns' (Fun f (map var_x_i [0..<n])) (var_x_i i)" by auto
  define subts where "subts = [(u,v) . (s,t) <- U, u <- supteq_list s, v <- supteq_list t]"
  define s where "s = subts" 
  define ns where "ns = subts @ [(Fun f (map var_x_i [0..<n]), var_x_i i). (f, n) <- fs, i <- status \<sigma> (f, n)]"
  let ?U = "s @ ns" 
  from rt[of ?U] obtain S NS NST where rt: "rel_impl_prop rt ?U S NS NST" by presburger
  from rt 1 have
      *: "S \<subseteq> NS" "irrefl S" "ctxt.closed NS" "S O NS \<subseteq> S" "NS O S \<subseteq> S" "trans NS" "refl NS"
    and subst_NS: "subst.closed NS"  
    and subst_S: "subst.closed S" 
    and ws: "not_subterm_rel_info NS ?ws'" 
    by (auto simp: rel_impl_def)
  have "set s \<subseteq> set ?U" "set ns \<subseteq> set ?U"
    by (auto simp: ns_def)
  with rt[THEN conjunct1] 
  have orient: "\<And> l r. ?s' l r \<Longrightarrow> (l,r) \<in> set s \<Longrightarrow> (l,r) \<in> S" 
     "\<And> l r. ?ns' l r \<Longrightarrow> (l,r) \<in> set ns \<Longrightarrow> (l,r) \<in> NS" 
    by auto
  define n where "n = max_list [ length (status \<sigma> f) . (s,t) <- U, f <- funas_term_list t]"
  interpret pr: precedence ?prc ?prl ..
  note cb = compare_bools_def
  interpret co_wpo_params NS S ?prc n \<sigma>
  proof (unfold_locales; (intro subst_S subst_NS * 
        precedence_nat.prc_refl precedence_nat.prc_stri_imp_nstri precedence_nat.prc_SN
        precedence_nat.prc_compat)?; (elim FalseE)?)
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
  qed auto
  let ?S = "co.COWPO_S" 
  let ?NS = "co.WPO_NS" 
  let ?NST = Id
  interpret co_rewrite_pair co.COWPO_S co.WPO_NS by (rule cowpo_corewrite_pair)
  show ?case
  proof (rule exI[of _ ?S], rule exI[of _ ?NS], rule exI[of _ ?NST], intro conjI allI impI
      ctxt_NS refl_NS subst_NS trans_NS trans_S subst_S full_af disj_NS_S)
    show "irrefl ?S" using disj_NS_S refl_NS unfolding refl_on_def irrefl_on_def by auto
    {
      fix st
      assume stU: "st \<in> set U" 
      obtain s t where st: "st = (s,t)" by force
      hence stU: "(s,t) \<in> set U" using stU by auto
      show "isOK (rel_impl.nst ?rp st) \<Longrightarrow> st \<in> ?NST" unfolding d by auto

      let ?wpo = "wpo_ub (prc_nat pr) (\<lambda> _. False) False (\<lambda> _. False) ?s' ?ns' \<sigma> (\<lambda> _. Lex)"
      let ?wpoo = "wpo_orig ?prc (\<lambda> _. False) False (\<lambda> _. False) \<sigma> (\<lambda> _. Lex) n S NS"
      have "?wpo s t \<le>\<^sub>c\<^sub>b ?wpoo s t"
      proof (rule wpo_ub)
        fix si tj
        assume "s \<unrhd> si" "t \<unrhd> tj"
        with stU have sitj: "(si,tj) \<in> set subts" unfolding subts_def by force
        with orient
        show "(?s' si tj, ?ns' si tj)
       \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)" unfolding s_def ns_def cb by auto
      next
        fix f
        assume f: "f \<in> funas_term t"
        show "length (status \<sigma> f) \<le> n" unfolding n_def
          by (rule max_list, insert f stU, auto)
      qed
      from this[unfolded cb]
      show "isOK (rel_impl.ns ?rp st) \<Longrightarrow> st \<in> ?NS" 
        unfolding d st by auto
      {
        fix s t
        assume "(s,t) \<in> S" 
        hence "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S" for \<sigma> by (rule co.subst_S)
        hence "(s,t) \<in> invNS" by auto (insert S_O_NS(1) co.refl_nltA_point, blast)
      } note invNSI = this
      {
        fix s t
        assume "(s,t) \<in> NS" 
        hence "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" for \<sigma> by (rule co.subst_NS)
        hence "(s,t) \<in> invS" by auto (insert S_O_NS(1) co.refl_nltA_point, blast)
      } note invSI = this

      let ?pr = "(\<lambda>f g. (\<not> snd (prc_nat pr g f), \<not> fst (prc_nat pr g f)))" 
      let ?wpo = "wpo_ub ?pr (\<lambda> _. False) False (\<lambda> _. False) ?s' ?ns' \<sigma> (\<lambda> _. Lex)"
      let ?wpoo = "wpo_orig ?pr (\<lambda> _. False) False (\<lambda> _. False) \<sigma> (\<lambda> _. Lex) n invNS invS"
      have "?wpo s t \<le>\<^sub>c\<^sub>b ?wpoo s t" 
      proof (rule wpo_ub)
        fix si tj
        assume "s \<unrhd> si" "t \<unrhd> tj"
        with stU have sitj: "(si,tj) \<in> set subts" unfolding subts_def by force
        with orient
        show "(?s' si tj, ?ns' si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> invNS, (si, tj) \<in> invS)" 
          unfolding s_def ns_def cb using invNSI invSI by auto
      next
        fix f
        assume f: "f \<in> funas_term t"
        show "length (status \<sigma> f) \<le> n" unfolding n_def
          by (rule max_list, insert f stU, auto)
      qed
      from this[unfolded cb]
      show "isOK (rel_impl.s ?rp st) \<Longrightarrow> st \<in> ?S" 
        unfolding d st by auto
    }
  qed (auto simp: d no_complexity_check_def intro: full_af empty_af)
qed

end