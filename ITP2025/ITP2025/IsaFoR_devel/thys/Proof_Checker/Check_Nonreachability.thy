(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2017)
         René Thiemann (2023)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Nonreachability\<close>

theory Check_Nonreachability
  imports
    Nonreach.Gtcap_Impl
    TRS.Rule_Map
    TA.Exact_Tree_Automata_Completion_Impl
    CR.Ordered_Completion_Impl
    Check_Equational_Proof
begin

hide_const (open) Ground_Context_Impl.match_list
hide_fact (open) Ground_Context_Impl.match_list_sound Ground_Context_Impl.match_list_complete

lemma rsteps_imp_rev_rsteps:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(t, s) \<in> (rstep (R\<inverse>))\<^sup>*"
using assms using rtrancl_converse by force

lemma rstep_subst_overapproximation:
  assumes "\<forall>(l, r) \<in> R. \<exists>(l', r') \<in> R'. \<exists>\<sigma>. l = l' \<cdot> \<sigma> \<and> r = r' \<cdot> \<sigma>"
  shows "rstep R \<subseteq> rstep R'"
using assms by force

definition "is_instance_rule r r' \<longleftrightarrow>
  (case match_list Var [(fst r', fst r), (snd r', snd r)] of
    Some \<sigma> \<Rightarrow> True
  | None \<Rightarrow> False)"

lemma is_instance_rule [simp]:
  "is_instance_rule r r' \<longleftrightarrow> (\<exists>\<sigma>. fst r = fst r' \<cdot> \<sigma> \<and> snd r = snd r' \<cdot> \<sigma>)"
by (auto simp: is_instance_rule_def dest!: match_list_sound match_list_complete split: option.splits)
   metis

definition "check_subst_overapproximation R R' =
  check_allm (\<lambda>r. check_exm (\<lambda>r'.
    check (is_instance_rule r r') id
  ) R' (\<lambda>_. showsl_lit (STR ''growing rule for '') \<circ> showsl_rule r \<circ> showsl_lit (STR '' is missing\<newline>''))) R
  <+? (\<lambda>e. showsl_trs R' \<circ>
        showsl_lit (STR ''\<newline>is not an overapproximation of\<newline>'') \<circ> showsl_trs R \<circ> showsl_nl \<circ> e)"

lemma check_subst_overapproximation [simp]:
  "isOK (check_subst_overapproximation R R') \<longleftrightarrow>
    (\<forall>(l, r) \<in> set R. \<exists>(l', r') \<in> set R'. \<exists>\<sigma>. l = l' \<cdot> \<sigma> \<and> r = r' \<cdot> \<sigma>)"
by (force simp: check_subst_overapproximation_def)

datatype ('f, 'v, 'rp, 'l) nonreachability_proof =
  Nonreachable_Tcap
| Nonreachable_Gtcap
| Nonreachable_ETAC "(('f, 'l) lab \<times> nat) list" "('f, 'l) lab" "('f, 'l) lab" "(('f, 'l) lab, 'v) etac_ta"
| Nonreachable_Subst_Approx "(('f, 'l) lab, 'v) rules" "('f, 'v, 'rp, 'l) nonreachability_proof"
| Nonreachable_Reverse "('f, 'v, 'rp, 'l) nonreachability_proof"
| Nonreachable_FGCR
    "('f, 'l) lab" "('f, 'l) lab" "('f, 'l) lab" \<comment> \<open>function symbols for equality, true, and false\<close>
    "(('f, 'l) lab, 'v) rules" "(('f, 'l) lab, 'v) rules" \<comment> \<open>equations and rules of complete system\<close>
    "('f, 'l) lab reduction_order_input" \<comment> \<open>reduction order\<close>
    "(('f, 'l) lab, 'v) ordered_completion_proof"
| Nonreachable_Co_Rewrite_Pair "(('f, 'l) lab,'v,'rp) rel_impl_type" 'rp
| Nonreachable_Equational_Disproof "('f, 'l, 'v) equational_disproof"

context co_rewrite_pair
begin

context
  fixes R :: "('f,'v)trs" 
  assumes R: "R \<subseteq> NS"
begin

lemma rstep_imp_NS: "rstep R \<subseteq> NS" 
  using subst_NS ctxt_NS R by fast

lemma rsteps_imp_NS: "(rstep R)^* \<subseteq> NS" 
  using refl_NS trans_NS rstep_imp_NS
  by (metis rtrancl_mono trans_refl_imp_rtrancl_id)

lemma co_rewrite_non_reach: assumes "(t,s) \<in> S" 
  shows "\<not> (\<exists> \<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)^*)" 
proof (intro notI, elim exE)
  fix \<sigma>
  assume "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*" 
  with rsteps_imp_NS have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" by auto
  with disj_NS_S have "(t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> S" by auto
  with assms subst_S show False by blast
qed
end
end

definition check_non_reach_co_rewrite_pair ::
    "('f::{showl,compare_order}, 'v:: showl) rel_impl \<Rightarrow> ('f,'v)rules \<Rightarrow>
     ('f,'v)term \<Rightarrow>
     ('f,'v)term \<Rightarrow>     
     showsl check" where
  "check_non_reach_co_rewrite_pair rp R s t \<equiv> 
    do {
        rel_impl_co_rewrite_pair rp;
        rel_impl_ns rp R;
        rel_impl.s rp (t, s)
     } <+? (\<lambda> s. showsl_lit (STR ''problem in disproving non-reachability via co-rewrite pairs'') \<circ> showsl_nl \<circ> s)"

lemma check_non_reach_co_rewrite_pair: assumes rp: "rel_impl rp"
  and ok: "isOK(check_non_reach_co_rewrite_pair rp R s t)"
  shows "\<not> (\<exists> \<sigma>. (s \<cdot> \<sigma> ,t \<cdot> \<sigma>) \<in> (rstep (set R))^*)"
proof -
  note ok = ok[unfolded check_non_reach_co_rewrite_pair_def, simplified]
  from ok have valid: "isOK(rel_impl_co_rewrite_pair rp)" by simp
  from ok have ns: "isOK (rel_impl_ns rp R)" by simp
  from ok have s: "isOK (rel_impl_s rp ([(t,s)]))" by (simp add: rel_impl_list)
  from rel_impl_co_rewrite_pair[OF rp valid s ns]
  obtain S NS where crp: "co_rewrite_pair S NS"  
    and NS: "set R \<subseteq> NS" and S: "(t,s) \<in> S" by auto
  from co_rewrite_pair.co_rewrite_non_reach[OF crp NS S]
  show ?thesis .
qed
 


definition "rule_map R fn =
  case_option [] (map snd) (rm.lookup fn (insert_rules () R (rm.empty ())))"

hide_const NthRoot.root

lemma rule_map:
  "set (rule_map R fn) = {(l, r) \<in> set R. root l = Some fn}" (is "?A = ?B")
proof
  let ?rm = "insert_rules () R (rm.empty ())"
  have rm_inj: "rm_inj ?rm" by (simp)
  show "?A \<subseteq> ?B"
  proof
    fix l r assume *: "(l, r) \<in> set (rule_map R fn)"
    then show "(l, r) \<in> ?B"
    proof (cases "rm.lookup fn ?rm")
      case (Some rs)
      with * have 2: "(l, r) \<in> snd `set rs" by (simp add: rule_map_def)
      from Some and rm_inj have "\<forall>r\<in>set rs. key r = Some fn"
        by (metis (no_types, lifting) mmap_inj_def rm.correct(5) rm.invar rm_inj_def)
      moreover from 2 obtain a where "(a, l, r) \<in> set rs" by auto
      ultimately have "key ((), l, r) = Some fn" by simp
      then have root: "root l = Some fn" by (cases l, simp_all)
      from Some_in_values[OF Some] have "set rs \<subseteq> set (values ?rm)" .
      then have "(l, r) \<in> snd ` set (values ?rm)" using 2 by auto
      then have "(l, r) \<in> set R" by (auto simp: values_rules_with_conv_unit)
      with root show ?thesis by simp
    qed (simp add: rule_map_def)
  qed
next
  let ?rm = "insert_rules () R (rm.empty ())"
  have rm_inj: "rm_inj ?rm" by (simp)
  show "?B \<subseteq> ?A"
  proof
    fix l r assume "(l, r) \<in> ?B"
    then have 1: "(l, r) \<in> set R" and "root l = Some fn" by auto
    from \<open>root l = Some fn\<close> obtain f and n and ts where [simp]: "fn = (f, n)" "length ts = n"
      and l: "l = Fun f ts" by (cases l) auto
    from 1
    have "(l, r) \<in> set (Rule_Map.rules ?rm)"
      unfolding l by (auto simp: values_rules_with_conv_unit)
    then have "((), l, r) \<in> set (values ?rm)" by auto
    from this[unfolded values_ran[unfolded ran_def]]
    obtain k vs where lookup: "rm.lookup k ?rm = Some vs"
      and "((), l, r) \<in> set vs" by (auto simp: rm.correct)
    then have 2: "(l, r) \<in> set (rule_map R k)" by (force simp: rule_map_def)
    have k: "k = (f, n)"
    proof -
      from \<open>root l = Some fn\<close> have "length ts = n" by (simp add: l)
      from lookup and \<open>((), l, r) \<in> set vs\<close>
      have "key ((), l, r) = Some k"
        apply (auto simp: rm.correct)
        by (meson mmap_inj_def rm_inj rm_inj_def)
      then show ?thesis by (simp add: l)
    qed
    from 2 show "(l, r) \<in> ?A" unfolding k by simp
  qed
qed

(*TODO: move*)
lemma funas_trs_Req [simp]:
  "funas_trs (Req x R eq true false s t) =
    {(eq, 2), (true, 0), (false, 0)} \<union> funas_term s \<union> funas_term t \<union> funas_trs R"
  by (auto simp: Req_def funas_defs)

definition "Req_list x (R :: ('f, 'v) rules) eq true false s t =
  (Fun eq [Var x, Var x], Fun true []) #
  (Fun eq [s, t], Fun false []) # R"

lemma Req_list [simp]: "set (Req_list x R eq true false s t) = Req x (set R) eq true false s t"
  by (auto simp: Req_list_def Req_def)

fun check_nonreachable
where
  "check_nonreachable a i I J R s t Nonreachable_Tcap =
    check (\<not> Ground_Context.match (tcapI R s) t)
      (showsl_lit (STR ''could not show nonreachability via tcap''))"
| "check_nonreachable a i I J R s t Nonreachable_Gtcap = do {
    let nlv = (\<forall>lr \<in> set R. is_Fun (fst lr));
    let fs = funas_trs_list R in
    check (\<not> Ground_Context.match (tcapI R s) t \<or>
           nonreachable_gtcapRM fs nlv (R \<noteq> []) (mk_gt_fun R) (rule_map R) s t)
      (showsl_lit (STR ''could not show nonreachability via generalized tcap''))
  }"
| "check_nonreachable _ _ _ _ R s t (Nonreachable_ETAC F a c A) =
    check_etac_nonreachable F a c A R s t"
| "check_nonreachable a i I J R s t (Nonreachable_Subst_Approx R' p) =
  check_subst_overapproximation R R' \<then> check_nonreachable a i I J R' s t p"
| "check_nonreachable a i I J R s t (Nonreachable_Reverse p) =
  check_nonreachable a i I J (map (\<lambda>(x, y). (y, x)) R) t s p"
| "check_nonreachable a i I J R s t (Nonreachable_FGCR eq tr fa E' R' ro ocp) = do {
    let R_eq = Req_list ''x'' R eq tr fa s t;
    check_equational_disproof_oc ((+) STR '''') (Fun tr [], Fun fa []) R_eq E' R' ro ocp
  }"
| "check_nonreachable a i I J R s t (Nonreachable_Co_Rewrite_Pair grt rp) = do {
                 check_non_reach_co_rewrite_pair (rel_impl_of grt rp) R s t
                   <+? (\<lambda> e. (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' cannot reach '') \<circ> showsl t \<circ> showsl_nl \<circ> e))
                }"
| "check_nonreachable a i I J R s t (Nonreachable_Equational_Disproof v) =
    (if ground s \<and> ground t
      then check_equational_disproof False i I J R (s, t) v \<comment> \<open>TODO: do not ignore a\<close>
      else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' must be both ground'')))"

datatype ('f, 'v, 'rp, 'l) nonjoinability_proof =
  Nonjoinable_Tcap
| Nonjoinable_Ground_NF "('f, 'v, 'rp, 'l) nonreachability_proof"

fun check_nonjoinable
where
  "check_nonjoinable a i I J R s t Nonjoinable_Tcap =
    check (\<not> Ground_Context.unifiable (tcapI R s) (tcapI R t))
      (showsl_lit (STR ''could not show nonjoinability via tcap''))"
| "check_nonjoinable a i I J R s t (Nonjoinable_Ground_NF p) =
    (if is_NF_trs R s \<and> ground s then check_nonreachable a i I J R t s p
    else if is_NF_trs R t \<and> ground t then check_nonreachable a i I J R s t p
    else error (showsl_lit (STR ''non NF'')))"

lemma check_nonreachable: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
  shows "isOK (check_nonreachable a i I J R s t p) \<Longrightarrow> \<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*)"
proof (induct p arbitrary: R s t)
  case Nonreachable_Tcap
  with match_tcap_sound [of s _ t _ "set R"] show ?case by auto
next
  case Nonreachable_Gtcap
  with match_tcap_sound [of s _ t _ "set R"]
       nonreach_gtcap [OF refl rule_map, of R s t]
  show ?case by auto
next
  case (Nonreachable_ETAC F a c A)
  with check_etac_nonreachable [of F a c A R s t] show ?case by auto
next
  case (Nonreachable_Subst_Approx R' p)
  then have "(\<forall>(l, r) \<in> set R. \<exists>(l', r') \<in> set R'. \<exists>\<sigma>. l = l' \<cdot> \<sigma> \<and> r = r' \<cdot> \<sigma>)"
    and "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R'))\<^sup>*)" by auto
  with rstep_subst_overapproximation [OF this(1), THEN rtrancl_mono] show ?case by blast
next
  case *: (Nonreachable_Reverse p)
  have [simp]: "(\<lambda>(x, y). (y, x)) ` set R = (set R)\<inverse>" by auto
  have "\<not> (\<exists>\<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> (rstep ((set R)\<inverse>))\<^sup>*)" using * by force
  with rsteps_imp_rev_rsteps [of "s \<cdot> \<sigma>" "t \<cdot> \<sigma>" "set R" for \<sigma>]
  show ?case by auto
next
  case *: (Nonreachable_FGCR eq tr fa S T ro ocp)
  let ?R = "Req_list ''x'' R eq tr fa s t"
  obtain ro_kbo where [simp]: "ro = KBO_Input ro_kbo"
    and ok': "isOK (check_equational_disproof_oc ((+) STR '''') (Fun tr [], Fun fa []) ?R S T ro ocp)"
    using * by (cases ro) (auto simp: check_equational_disproof_oc_def)
  define F where "F = set (precw_w0_sig ro_kbo)"
  define ord :: "(_, string) term \<Rightarrow> _ \<Rightarrow> _"
    where
      "ord = redord.less (create_KBO_redord ro_kbo (precw_w0_sig ro_kbo))"

  note ok = check_equational_disproof_for_infeasibility [OF ok' [simplified], folded F_def ord_def]
  then interpret reduction_order ord by blast

  define fgordstep where "fgordstep = FGROUND F (ordstep less_set ((set S)\<^sup>\<leftrightarrow> \<union> set T))"

  from ok obtain u and v where **: "(Fun tr [], u) \<in> fgordstep\<^sup>!" "(Fun fa [], v) \<in> fgordstep\<^sup>!"
    "u \<noteq> v" by (auto simp: fgordstep_def)

  have "funas_term s \<subseteq> F" and "funas_term t \<subseteq> F" and "funas_trs (set ?R) \<subseteq> F"
    and "{(eq, 2), (tr, 0), (fa, 0)} \<subseteq> funas_trs (set ?R)"
    using * and ok by (auto simp: funas_defs Req_def)
  then show ?case
    using ok and **
    by (intro infeasibility_via_FGCR [where R = "set R" and S = "((set S)\<^sup>\<leftrightarrow> \<union> set T)" and u = u and v = v])
      (auto simp: fgordstep_def)
next
  case *: (Nonreachable_Co_Rewrite_Pair grt rp)
  hence "isOK (check_non_reach_co_rewrite_pair (rel_impl_of grt rp) R s t)" 
    by auto
  from check_non_reach_co_rewrite_pair[OF rel_impl_of this]
  show ?case .
next
  case (Nonreachable_Equational_Disproof v)
  (* s, t must be ground! *)
  hence ok: "isOK (check_equational_disproof False i I J R (s, t) v)" and g: "ground s \<and> ground t"
    by auto
  with assms check_equational_disproof_sound
  have "(s, t) \<notin> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" by metis
  then have "(s, t) \<notin> (rstep (set R))\<^sup>*" by blast
  thus ?case using ground_subst_apply g by metis
qed

lemma nonjoin_via_nonreach:
  assumes "is_NF_trs R t" and "ground t" and "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*)"
  shows  "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>\<down>)"
proof
  assume "\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>\<down>"
  then obtain \<sigma> where sigma: "(s \<cdot> \<sigma>, t) \<in> (rstep (set R))\<^sup>\<down>" using assms ground_subst_apply by metis
  have t: "(u, t) \<in> (rstep (set R))\<^sup>\<down> \<Longrightarrow> (u, t) \<in> (rstep (set R))\<^sup>*" for u 
    using assms NF_join_imp_reach unfolding is_NF_trs by metis
  with sigma have "(s \<cdot> \<sigma>, t) \<in> (rstep (set R))\<^sup>*" by presburger
  with assms ground_subst_apply show False by metis
qed

lemma check_nonjoinable:
  assumes I: "tp_spec I" and J: "dpp_spec J" and ok: "isOK (check_nonjoinable a i I J R s t p)"
  shows "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>\<down>)"
proof (cases p)
  case Nonjoinable_Tcap
  with assms show ?thesis using join_imp_unifiable_tcaps [of s _ t] by auto
next
  case (Nonjoinable_Ground_NF p)
  with ok have c: "(is_NF_trs R s \<and> ground s \<and> isOK (check_nonreachable a i I J R t s p)) \<or> 
    (is_NF_trs R t \<and> ground t \<and> isOK (check_nonreachable a i I J R s t p))"
    by (auto split: if_splits)
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    with assms check_nonreachable[OF I J]
    have " \<not> (\<exists>\<sigma>. (t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*)" by metis
    then show ?case using nonjoin_via_nonreach 1 by blast
  next
    case 2
    with assms check_nonreachable[OF I J]
    have f1: " \<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*)" by metis
    then show ?case using nonjoin_via_nonreach 2 by blast
  qed
qed

end
