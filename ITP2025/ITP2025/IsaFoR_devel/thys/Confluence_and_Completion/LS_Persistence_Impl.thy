section \<open>Persistent decomposition and check functions\<close>

theory LS_Persistence_Impl
  imports 
    LS_Persistence
    LS_Modularity
    First_Order_Terms.Position
    TRS.Trs_Impl_More
    "Transitive-Closure.Transitive_Closure_List_Impl"
    Norm_Equiv.Litsim_Trs_Impl
begin

subsection \<open>Misc\<close>

lemma in_pair_collect_simp: "(a,b) \<in> {(a,b). P a b} \<longleftrightarrow> P a b" by auto

(* UGH *)
instance prod :: (infinite, type) infinite
  by standard (simp add: infinite_UNIV finite_prod)

lemma isOK_try_catch:
  "isOK (try a catch b) \<longleftrightarrow> isOK a \<or> (\<exists>e. a = Inl e \<and> isOK (b e))"
  by (cases a) (auto)

lemma litsim_empty_empty [simp]:
  "R \<doteq> {} \<longleftrightarrow> R = {}" "{} \<doteq> R \<longleftrightarrow> R = {}"
  by (auto simp: subsumable_trs.litsim_def)

(* facts about permutations *)
lemma is_Var_permute [simp]: "is_Var (p \<bullet> t) \<longleftrightarrow> is_Var t"
  by (cases t) auto

lemma vars_term_permute [simp]:
  fixes p :: "'v::infinite perm"
  shows "vars_term (p \<bullet> t) = p \<bullet> vars_term t"
  by (induct t) (auto simp: atom_set_pt.insert_eqvt atom_set_pt.inv_mem_simps(1)[symmetric] simp del: atom_set_pt.inv_mem_simps)

lemma wf_trs_permute_imp:
  "wf_trs R \<Longrightarrow> wf_trs (p \<bullet> R)"
  by (auto 0 3 simp: wf_trs_def' trs_pt.permute_set_def rule_pt.permute_prod_eqvt split: prod.splits)
   (insert atom_set_pt.inv_mem_simps(1), blast)

lemma wf_trs_permute [simp]:
  "wf_trs (p \<bullet> R) \<longleftrightarrow> wf_trs R"
  using wf_trs_permute_imp[of R p] wf_trs_permute_imp[of "p \<bullet> R" "-p"] by auto

lemma permute_term_by_var_subst [simp]:
  fixes \<pi> :: "'v::infinite perm"
  shows "t \<cdot> (\<lambda>x. Var (\<pi> \<bullet> x)) = \<pi> \<bullet> t"
  by (induct t) auto

lemma rstep'_permute_sub:
  "rstep' (\<pi> \<bullet> R) \<subseteq> rstep' R"
proof (intro subrelI, unfold rstep'_iff_rstep_r_p_s', elim exE, goal_cases)
  case (1 s t l r p \<sigma>) then show ?case
    using rstep_r_p_s'I[of "-\<pi> \<bullet> (l, r)" R p _ s "(\<lambda>x. \<pi> \<bullet> Var x) \<circ>\<^sub>s _" t]
    by (auto elim!: rstep_r_p_s'E simp: rule_pt.permute_prod_eqvt) blast
qed

lemma rstep'_permute [simp]:
  "rstep' (p \<bullet> R) = rstep' R"
  using rstep'_permute_sub[of p R] rstep'_permute_sub[of "-p" "p \<bullet> R"] by auto

lemma CR_on_iff_CR:
  assumes "wf_trs (\<R> :: ('f, 'v :: infinite) trs)" "funas_trs \<R> \<subseteq> \<F>"
  shows "CR_on (rstep \<R>) { t :: ('f, 'v) term. funas_term t \<subseteq> \<F> } \<longleftrightarrow> CR (rstep \<R>)"
  using assms by (auto simp: CR_on_imp_CR) (auto simp: CR_on_def)

lemma rstep'_mono_subsumeseq_trs:
  fixes R S :: "('f, 'v :: infinite) trs"
  assumes "R \<le>\<cdot> S" shows "rstep' R \<subseteq> rstep' S"
  using assms by (auto simp: subsumeseq_trs_def elim!: rstep'.cases)
    (metis rstep'.rstep' rstep'_permute trs_pt.inv_mem_simps(2))

lemma rstep'_eq_litsim_trs:
  fixes R S :: "('f, 'v :: infinite) trs"
  shows "R \<doteq> S \<Longrightarrow> rstep' R = rstep' S"
  using rstep'_mono_subsumeseq_trs by (auto simp: subsumable_trs.litsim_def)

lemma wf_trs_mono_subsumeseq_trs:
  fixes R S :: "('f, 'v :: infinite) trs"
  assumes "R \<le>\<cdot> S" shows "wf_trs S \<Longrightarrow> wf_trs R"
  using assms by (meson subsumeseq_trsE trs_pt.inv_mem_simps(2) wf_trs_def' wf_trs_permute)

lemma wf_trs_lit_sim_trs:
  fixes R S :: "('f, 'v :: infinite) trs"
  shows "R \<doteq> S \<Longrightarrow> wf_trs R \<longleftrightarrow> wf_trs S"
  by (auto simp: wf_trs_mono_subsumeseq_trs subsumable_trs.litsim_def)

lemma CR_change_variables:
  shows "wf_trs R \<Longrightarrow> CR (rstep' R :: ('f, 'v :: infinite) trs) \<Longrightarrow> CR (rstep' R :: ('f, 'w :: infinite) trs)"
proof (standard, goal_cases)
  case (1 s t u)
  obtain f :: "'w \<Rightarrow> 'v"  where f: "inj_on f (vars_term s)"
    by (metis finite_into_infinite infinite_UNIV finite_vars_term)
  let ?g = "inv_into (vars_term s) f"
  obtain v where v: "(t \<cdot> (Var \<circ> f), v) \<in> (rstep' R)\<^sup>*" "(u \<cdot> (Var \<circ> f), v) \<in> (rstep' R)\<^sup>*"
    using CR_onD[OF 1(2) _ rsteps'_stable[OF 1(4)] rsteps'_stable[OF 1(5)], of "Var \<circ> f"] by auto
  have "vars_term t \<subseteq> vars_term s" "vars_term u \<subseteq> vars_term s" using 1(1,4,5) rstep'_sub_vars by metis+
  moreover then have "t \<cdot> (Var \<circ> f) \<cdot> (Var \<circ> ?g) = t" "u \<cdot> (Var \<circ> f) \<cdot> (Var \<circ> ?g) = u"
    using f by (auto simp del: subst_subst_compose simp: subst_subst_compose[symmetric]
      subst_compose_def term_subst_eq_conv[of _ _ Var, unfolded subst_apply_term_empty])
  ultimately show ?case using v by (auto dest!: rsteps'_stable[of _ _ _ "Var \<circ> ?g"])
qed

lemma CR_change_variables_iff:
  "wf_trs R \<Longrightarrow> CR (rstep' R :: ('f, 'v :: infinite) trs) \<longleftrightarrow> CR (rstep' R :: ('f, 'w :: infinite) trs)"
  by (auto simp: CR_change_variables)

lemma CR_change_variables_iff':
  "wf_trs (R :: ('f, 'v :: infinite) trs) \<Longrightarrow> CR (rstep' R :: ('f, 'w :: infinite) trs) \<longleftrightarrow> CR (rstep R)"
  by (simp add: CR_change_variables_iff rstep_eq_rstep')

subsection \<open>Executable version of @{const many_sorted_terms.\<T>\<^sub>\<alpha>}\<close>

fun \<T>\<^sub>\<alpha>_code :: "(('f \<times> nat) \<Rightarrow> ('t list \<times> 't) option) \<Rightarrow> ('v \<Rightarrow> 't option) \<Rightarrow> 't \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "\<T>\<^sub>\<alpha>_code sigF sigV \<alpha> (Var x) \<longleftrightarrow> sigV x = Some \<alpha>"
| "\<T>\<^sub>\<alpha>_code sigF sigV \<alpha> (Fun f ts) \<longleftrightarrow>
  case_option False (\<lambda>(tys, \<alpha>'). \<alpha> = \<alpha>' \<and> list_all (case_prod (\<T>\<^sub>\<alpha>_code sigF sigV)) (zip tys ts)) (sigF (f, length ts))"

lemma (in many_sorted_terms) \<T>\<^sub>\<alpha>_code:
   "\<T>\<^sub>\<alpha> \<alpha> t \<longleftrightarrow> \<T>\<^sub>\<alpha>_code sigF sigV \<alpha> t"
proof (induct t arbitrary: \<alpha>)
  case (Fun f ts) then show ?case
    using Fun[OF nth_mem] arity by (auto simp: list_all_length split: option.split elim: \<T>\<^sub>\<alpha>.cases)
qed (auto elim: \<T>\<^sub>\<alpha>.cases)

subsection \<open>Make signature from list\<close>

fun mk_sigF :: "('f \<times> ('t list \<times> 't)) list \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('t list \<times> 't) option" where
  "mk_sigF sig (f, a) = map_option snd (find (\<lambda>(f', tys, t). f = f' \<and> a = length tys) sig)"

lemma many_sorted_terms_mk_sigF [simp]:
  "many_sorted_terms (mk_sigF sig)"
  by (unfold_locales) (auto simp: find_Some_iff)

lemma \<T>\<^sub>\<alpha>_code:
  "\<T>\<^sub>\<alpha>_code (mk_sigF sig) sigV = many_sorted_terms.\<T>\<^sub>\<alpha> (mk_sigF sig) sigV"
proof -
  interpret many_sorted_terms "mk_sigF sig" sigV by simp
  show ?thesis by (force simp: \<T>\<^sub>\<alpha>_code)
qed

subsection \<open>Executable version of needed_types\<close>

context many_sorted_terms
begin

definition sigF_arcs where
  "sigF_arcs = {(\<alpha>, \<beta>) |f n tys \<alpha> \<beta>. sigF (f, n) = Some (tys, \<alpha>) \<and> \<beta> \<in> set tys}"

lemma needed_types_by_sigF_arcs:
  "needed_types \<alpha> \<beta> \<longleftrightarrow> (\<alpha>, \<beta>) \<in> sigF_arcs\<^sup>*" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R by (induct) (force simp: sigF_arcs_def)+
next
  assume ?R then show ?L by (induct) (auto simp: sigF_arcs_def)
qed

end

context
  fixes sig :: "('f :: showl \<times> 't list \<times> 't :: showl) list"
begin

interpretation many_sorted_terms "mk_sigF sig" "Some \<circ> snd" by simp

definition sig_is_clean where
  "sig_is_clean = distinct (map (\<lambda>(f, tys, _). (f, length tys)) sig)"

definition sigF_arcs_code where
  "sigF_arcs_code = concat (map (\<lambda>(_, tys, ty). map (\<lambda>ty'. (ty, ty')) tys) sig)"

lemma sigF_arcs_code:
  assumes "sig_is_clean"
  shows "set (sigF_arcs_code) = many_sorted_terms.sigF_arcs (mk_sigF sig)"
  using find_distinct(1)[OF assms[unfolded sig_is_clean_def]]
  by (simp add: sigF_arcs_code_def many_sorted_terms.sigF_arcs_def split_beta split_beta' image_def)
    fastforce

definition needed_types_code where
  "needed_types_code = memo_list_rtrancl sigF_arcs_code"

lemma needed_types_code:
  "sig_is_clean \<Longrightarrow> set (needed_types_code \<alpha>) = {\<beta>. many_sorted_terms.needed_types (mk_sigF sig) \<alpha> \<beta>}"
  by (auto simp: needed_types_code_def memo_list_rtrancl many_sorted_terms.needed_types_by_sigF_arcs sigF_arcs_code)

fun annotate_term where
  "annotate_term sigF \<alpha> (Var x) = return (Var (x, \<alpha>))"
| "annotate_term sigF \<alpha> (Fun f ts) = (case sigF (f, length ts) of
    None \<Rightarrow> error (showsl_lit (STR ''persistent decomposition: no signature for symbol '') \<circ> showsl f)
  | Some (tys, ty) \<Rightarrow> if \<alpha> \<noteq> ty then error (showsl_lit (STR ''persistent decomposition: '') \<circ> showsl f
      \<circ> showsl_lit (STR '' has wrong type in '') \<circ> showsl (Fun f ts))
    else do { ts' <- mapM (\<lambda>(\<beta>, t). annotate_term sigF \<beta> t) (zip tys ts); return (Fun f ts') })"

lemma isOK_annotate_term:
  "isOK (annotate_term (mk_sigF sig) \<alpha> t) \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> (run (annotate_term (mk_sigF sig) \<alpha> t))"
  (* somehow the proof below doesn't work *inside* the context *)
  oops

end (* context *)

lemma isOK_annotate_term:
  "isOK (annotate_term (mk_sigF sig) \<alpha> t) \<Longrightarrow> many_sorted_terms.\<T>\<^sub>\<alpha> (mk_sigF sig) (Some \<circ> snd) \<alpha> (run (annotate_term (mk_sigF sig) \<alpha> t))"
proof (induct t arbitrary: \<alpha>)
  case (Fun f ts)
  show ?case using Fun(1)[OF nth_mem] Fun(2)
    by (auto simp del: mk_sigF.simps split: prod.splits sum.splits option.splits if_splits dest!: mapM_return
      simp: isOK_def zip_nth_conv list_all_length \<T>\<^sub>\<alpha>_code[symmetric] many_sorted_terms.arity[OF many_sorted_terms_mk_sigF])
qed (auto simp: \<T>\<^sub>\<alpha>_code[symmetric])

context
  fixes sig :: "('f :: showl \<times> 't list \<times> 't :: showl) list"
begin

interpretation many_sorted_terms "mk_sigF sig" "Some \<circ> snd" by simp

definition annotate_term' where
  "annotate_term' sigF t =
    (case root t of None \<Rightarrow> error id
    | Some fn \<Rightarrow> (case sigF fn of None \<Rightarrow> error (showsl_lit (STR ''persistent decomposition: no signature for symbol '') \<circ> showsl fn)
    | Some (_, \<alpha>) \<Rightarrow> do { t' <- annotate_term sigF \<alpha> t; return (\<alpha>, t') }))"

lemma isOK_annotate_term':
  "isOK (annotate_term' (mk_sigF sig) t) \<Longrightarrow> case_prod (many_sorted_terms.\<T>\<^sub>\<alpha> (mk_sigF sig) (Some \<circ> snd)) (run (annotate_term' (mk_sigF sig) t))"
  unfolding annotate_term'_def isOK_case_option 
  by (cases "root t", auto simp del: annotate_term.simps split: option.splits dest: isOK_annotate_term)

definition
  "check_rule sigF rl = do {
     let (l, r) = rl;
     (\<alpha>, l') <- annotate_term' sigF l;
     r' <- annotate_term sigF \<alpha> r;
     \<comment> \<open>check_variants_rule (l, r) (l', r'); (* TODO: message? *)\<close>
     check_variants_rule (map_vars_term (\<lambda>x. (x, \<alpha>)) l, map_vars_term (\<lambda>x. (x, \<alpha>)) r) (l', r')
      <? (showsl_lit (STR ''persistent decomposition: inconsistent types of variables in rule '')
         \<circ> showsl_rule (l, r));
     return (l', r')
   }"

lemma isOK_check_rule:
  assumes "wf_trs {rl}" "isOK (check_rule (mk_sigF sig) rl)"
  defines "res \<equiv> run (check_rule (mk_sigF sig) rl)"
  shows "wf_trs {res} \<and> rstep' {rl} = rstep' {res :: (_, 'v :: {showl, infinite} \<times> _) rule} \<and> (\<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst res) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd res))"
proof (intro conjI, goal_cases)
  obtain l r l' r' where [simp]: "rl = (l, r)" "res = (l', r')" by (metis prod.collapse)
  obtain \<alpha> where [simp]:
    "projr (annotate_term' (mk_sigF sig) l) = (\<alpha>, l')"
    "projr (annotate_term (mk_sigF sig) \<alpha> r) = r'"
    using assms by (auto simp: check_rule_def del: check_variants_rule) blast
  have *: "\<T>\<^sub>\<alpha> \<alpha> (fst res)" "\<T>\<^sub>\<alpha> \<alpha> (snd res)"
    using assms by (auto simp: check_rule_def dest!: isOK_annotate_term' isOK_annotate_term)
  obtain p where
    **: "(l', r') = p \<bullet> (map_vars_term (\<lambda>x. (x, \<alpha>)) l, map_vars_term (\<lambda>x. (x, \<alpha>)) r)"
    using assms by (auto simp: check_rule_def) metis
  {
    case 1
    have "wf_trs {(map_vars_term (\<lambda>x. (x, \<alpha>)) l, map_vars_term (\<lambda>x. (x, \<alpha>)) r)}"
      using assms(1) by (auto simp: wf_trs_def term.set_map)
    then show ?case using wf_trs_permute[of _ "{_}"]
      by (auto simp: ** trs_pt.permute_set_def[unfolded Setcompr_eq_image])
  next
    case 2
    have [simp]: "rstep' {(l, r)} = rstep' {(map_vars_term (\<lambda>x. (x, \<alpha>)) l, map_vars_term (\<lambda>x. (x, \<alpha>)) r)}"
      unfolding map_vars_term_eq
      apply (intro equalityI subrelI)
      subgoal using rstep'.intros[of "l \<cdot> (Var \<circ> (\<lambda>x. (x, \<alpha>)))" "r \<cdot> (Var \<circ> (\<lambda>x. (x, \<alpha>)))" _ _ "(Var \<circ> fst) \<circ>\<^sub>s _"]
        unfolding subst_subst_compose[symmetric] subst_compose_assoc[symmetric] subst_compose_def[of _ "Var \<circ> _"]
        by (auto elim!: rstep'.cases simp: comp_def)
      subgoal by (auto elim!: rstep'.cases simp: subst_subst_compose[symmetric] simp del: subst_subst_compose)
      done
    show ?case using rstep'_permute[of _ "{_}"]
      by (auto simp: ** trs_pt.permute_set_def[unfolded Setcompr_eq_image])
  next
    case 3 then show ?case using * by auto
  }
qed

definition
  "check_persistence1 R Rs = do {
     check (sig_is_clean sig) (showsl_lit (STR ''persistent decomposition: duplicate function symbol in signature'')); 
       \<comment> \<open>TODO: message\<close>
     check_wf_trs R;
     mapM check_wf_trs Rs;
     let sigF = mk_sigF sig;
     R' <- mapM (check_rule sigF) R;
     Rs' <- mapM (mapM (check_rule sigF)) Rs;
     return (R', Rs')
  }"

lemma wf_trs_by_singletons:
  "wf_trs R \<longleftrightarrow> (\<forall>r \<in> R. wf_trs {r})"
  by (auto simp: wf_trs_def)

lemma rstep'_by_singletons:
  "rstep' R = \<Union>{rstep' {r} |r. r \<in> R}"
  by (auto elim!: rstep'.cases)

lemma isOK_check_rules:
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) rule list"
  assumes "wf_trs (set R)" "isOK (mapM (check_rule (mk_sigF sig)) R)"
  defines "res \<equiv> run (mapM (check_rule (mk_sigF sig)) R)"
  shows "wf_trs (set res)" "rstep' (set R) = rstep' (set res)" "\<And>r. r \<in> set res \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)"
proof -
  note x[simp] = wf_trs_by_singletons[of "set _"] rstep'_by_singletons[of "set _"]
  have [simp]: "length res = length R"
    using isOK_mapM[OF assms(2)] by (auto simp: res_def)
  { fix i assume *: "i < length R"
    then have **: "isOK (check_rule (mk_sigF sig) (R ! i))" "res ! i = run (check_rule (mk_sigF sig) (R ! i))"
      by (metis isOK_mapM[OF assms(2)] nth_mem nth_map res_def)+
    have "wf_trs {res ! i}" "rstep' {R ! i} = rstep' {res ! i}" "\<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst (res ! i)) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd (res ! i))"
      using assms(1) nth_mem[OF *(1)] isOK_check_rule[OF _ **(1)]
      by (auto simp: **(2)[symmetric]) }
  note [simp] = this
  show "wf_trs (set res)" "\<And>r. r \<in> set res \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)"
    by (auto dest!: in_set_idx)
  show "rstep' (set R) = rstep' (set res)" unfolding x Setcompr_eq_image set_map[symmetric]
    by (intro arg_cong[of _ _ "\<lambda>xs. Union (set xs)"]) (auto intro!: nth_equalityI)
qed

lemma isOK_check_persistence1:
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) rule list"
    and Rs :: "('f :: showl, 'v :: {infinite, showl}) rule list list"
  assumes "isOK (check_persistence1 R Rs)"
  defines "res \<equiv> run (check_persistence1 R Rs)"
  defines "R' \<equiv> fst res" and "Rs' \<equiv> snd res"
  shows "sig_is_clean sig"
    "wf_trs (set R')"
    "CR (rstep' (set R) :: ('f, 'w) trs) \<longleftrightarrow> CR (rstep' (set R') :: ('f, 'w) trs)"
    "\<And>r. r \<in> set R' \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)"
    "\<And>S. S \<in> set Rs' \<Longrightarrow> wf_trs (set S)"
    "(\<forall>S \<in> set Rs. CR (rstep' (set S) :: ('f, 'w) trs)) \<longleftrightarrow> (\<forall>S \<in> set Rs'. CR (rstep' (set S) :: ('f, 'w) trs))"
    "\<And>S r. S \<in> set Rs' \<Longrightarrow> r \<in> set S \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)"
    "length Rs' = length Rs"
proof (goal_cases 0 1 2 3 4 5 6 7)
  have *: "sig_is_clean sig" "wf_trs (set R)"
    "isOK (mapM (check_rule (mk_sigF sig)) R)"
    "R' = run (mapM (check_rule (mk_sigF sig)) R)" and
    **: "\<And>R. R \<in> set Rs \<Longrightarrow> wf_trs (set R)"
    "\<And>R. R \<in> set Rs \<Longrightarrow> isOK (mapM (check_rule (mk_sigF sig)) R)"
    "Rs' = map (\<lambda>R. run (mapM (check_rule (mk_sigF sig)) R)) Rs"
    using assms(1) by (auto simp: check_persistence1_def R'_def Rs'_def res_def dest: isOK_mapM)
     (insert isOK_mapM, fastforce)
  { case 0 then show ?case using * by (auto simp: isOK_check_rules)
  next  case 1 then show ?case using * by (auto simp: isOK_check_rules)
  next case 2 then show ?case using * by (auto simp: isOK_check_rules)
  next case (3 r) then show ?case using * by (auto simp: isOK_check_rules)
  next case (4 S) then show ?case by (auto simp: isOK_check_rules[OF **(1,2)] **(3))
  next case 5 then show ?case by (auto simp: isOK_check_rules[OF **(1,2)] **(3))
  next case (6 S r) then show ?case by (auto simp: isOK_check_rules[OF **(1,2)] **(3))
  next case 7 then show ?case by (auto simp: isOK_check_rules[OF **(1,2)] **(3)) }
qed

lemma interpret_persistent_cr_infinite_vars:
  fixes R :: "('f, 'v :: infinite \<times> 't) trs"
  assumes "wf_trs R" and "\<And>l r. (l, r) \<in> R \<Longrightarrow> \<exists>\<alpha> . \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r"
  shows "persistent_cr_infinite_vars (mk_sigF sig) (Some \<circ> snd) R"
proof (unfold_locales, goal_cases)
  case (3 \<alpha>)
  have [simp]: "{v \<in> many_sorted_terms.\<V> (Some \<circ> snd). snd v = \<alpha>} = UNIV \<times> {\<alpha>}"
    by (auto simp: many_sorted_terms.\<V>_def[OF many_sorted_terms_mk_sigF])
  show ?case by (auto simp: infinite_UNIV dest: finite_cartesian_productD1)
qed (auto simp: assms)

definition
  "type_of_rule sigF r = snd (the (sigF (the (root (fst r)))))"

definition
  "R_n\<alpha> ty R = filter (\<lambda>r. type_of_rule (mk_sigF sig) r \<in> set (needed_types_code sig ty)) R"

lemma type_of_rule_simp [simp]:
  "is_Fun l \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> l \<Longrightarrow> type_of_rule (mk_sigF sig) (l, r) = \<alpha>"
  by (auto simp: type_of_rule_def elim!: \<T>\<^sub>\<alpha>.cases)

lemma R_n\<alpha>_to_\<R>_n\<alpha>:
  assumes "sig_is_clean sig" "wf_trs (set R)" "\<And>l r. (l, r) \<in> set R \<Longrightarrow> \<exists>\<alpha> . \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r"
  shows "set (R_n\<alpha> \<alpha> R) = persistent_cr.\<R>\<^sub>n\<^sub>\<alpha> (mk_sigF sig) (Some \<circ> snd) (set R) \<alpha>"
  using needed_types_code[OF assms(1)] assms(2)
  apply (auto simp: R_n\<alpha>_def wf_trs_def')
  by (smt assms(3) case_prodD in_pair_collect_simp type_of_rule_simp)

definition
  "check_persistence_not_cr R S = do {
     (R', Ss') <- check_persistence1 R [S];
     let sigF = mk_sigF sig;
     let types = map (snd \<circ> snd) sig;
     let needed_types = needed_types_code sig;
     existsM (\<lambda>S. check_litsim_trs S (hd Ss'))
       (map (\<lambda>ty. let tys = needed_types ty in filter (\<lambda>r. type_of_rule sigF r \<in> set tys) R') types)
       <? (showsl_lit (STR ''persistent decomposition: new system is not induced by any type:'') \<circ> showsl_nl
          \<circ> showsl_trs S)
   }"

lemma isOK_check_persistence_not_cr:
  fixes R :: "('f, 'v :: {infinite, showl}) rule list"
  assumes "isOK (check_persistence_not_cr R S)" "CR (rstep' (set R) :: (_, 'w :: infinite) trs)"
  shows "CR (rstep' (set S) :: (_, 'w) trs)"
proof -
  let ?res1 = "run (check_persistence1 R [S])"
  define R' S' where "R' = fst ?res1" and "S' = hd (snd ?res1)"
  have *: "wf_trs (set R')" "\<And>l r. (l, r) \<in> (set R') \<Longrightarrow> \<exists>\<alpha> . \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r"
    and [simp]: "sig_is_clean sig"
      "CR (rstep' (set R) :: (_, 'w) trs) \<longleftrightarrow> CR (rstep' (set R') :: (_, 'w) trs)"
    using assms(1) isOK_check_persistence1[of R "[S]"] by (auto simp: R'_def check_persistence_not_cr_def)
  then interpret persistent_cr_infinite_vars "mk_sigF sig" "Some \<circ> snd" "set R'"
    by (intro interpret_persistent_cr_infinite_vars)
  have [simp]: "CR (rstep' (set S) :: (_, 'w) trs) \<longleftrightarrow> CR (rstep' (set S') :: (_, 'w) trs)"
    and **: "wf_trs (set S')" "\<And>l r. (l, r) \<in> set S' \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r"
    using assms(1) isOK_check_persistence1(5-)[of R "[S]"]
    by (cases "snd ?res1", (auto 0 0 simp: S'_def check_persistence_not_cr_def)[2])+
  obtain \<alpha> where "set (R_n\<alpha> \<alpha> R') \<doteq> set S'"
    using assms(1) by (auto simp: check_persistence_not_cr_def R_n\<alpha>_def R'_def S'_def)
  note *** = rstep'_eq_litsim_trs[OF subsumable_trs.litsim_sym[OF this]]
     wf_trs_lit_sim_trs[OF subsumable_trs.litsim_sym[OF this]]
  have "funas_trs (set R') \<subseteq> \<F>" "funas_trs (set S') \<subseteq> \<F>"
    using * subsetD[OF \<T>\<^sub>\<alpha>_\<T>] ** unfolding \<T>_def by (auto simp: funas_trs_def funas_rule_def) blast+
  then show ?thesis
    using persistent_decomposition[of UNIV] assms(2) *(1) **(1) R_n\<alpha>_to_\<R>_n\<alpha>[OF _ *]
    by (auto simp: CR_change_variables_iff' CR_on_iff_CR[symmetric] \<T>_def)
      (auto simp: *** rstep_eq_rstep')
qed

fun maximal_types_loop where
  "maximal_types_loop nt [] = []"
| "maximal_types_loop nt (\<beta> # tys) =
    (let mt = maximal_types_loop nt tys; nt\<beta> = nt \<beta> in
     if (\<exists>\<alpha> \<in> set mt. \<beta> \<in> set (nt \<alpha>)) then mt else \<beta> # filter (\<lambda>\<alpha>. \<alpha> \<notin> set nt\<beta>) mt)"

lemma maximal_types_loop_prop:
  assumes "sig_is_clean sig" "\<beta> \<in> set tys"
  shows "\<exists>\<alpha> \<in> set (maximal_types_loop (needed_types_code sig) tys). needed_types \<alpha> \<beta>"
  using assms(2)
proof (induct tys arbitrary: \<beta>)
  case (Cons a tys)
  show ?case using assms(1) Cons(2-) needed_types_code[of sig]
    by (auto dest!: Cons(1) simp: Let_def)
qed auto

definition
  "maximal_types nt = maximal_types_loop nt (map (snd \<circ> snd) sig)"

lemma maximal_types_prop:
  assumes "wf_trs R" "sig_is_clean sig"
  shows "\<Union>{{(l, r). (l, r) \<in> R \<and> \<T>\<^sub>\<alpha> \<beta>' l \<and> \<T>\<^sub>\<alpha> \<beta>' r} |\<beta>'. needed_types \<beta> \<beta>'} = {} \<or>
    (\<exists>\<alpha>\<in>set (maximal_types (needed_types_code sig)). needed_types \<alpha> \<beta>)"
proof -
  have *: "needed_types \<beta> \<gamma> \<Longrightarrow> (\<And>x. x \<in> set sig \<Longrightarrow> snd (snd x) \<noteq> \<beta>) \<Longrightarrow> \<beta> = \<gamma>" for \<beta> \<gamma>
    by (induct rule: needed_types.induct) (auto simp: find_Some_iff split: prod.splits, metis nth_mem prod_cases3)
  have **: "is_Fun t \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> t \<Longrightarrow> \<exists>x \<in> set sig. snd (snd x) = \<alpha>" for \<alpha> t
    by (cases t) (auto elim!: \<T>\<^sub>\<alpha>.cases simp: find_Some_iff set_conv_nth, metis)
  show ?thesis using maximal_types_loop_prop assms
    apply (auto simp: maximal_types_def wf_trs_def' Ball_def)
    apply (smt * ** comp_apply in_set_idx length_map nth_map nth_mem snd_conv)
    done
qed

definition
  "check_persistence_cr R Rs = do {
     (R', Rs') <- check_persistence1 R Rs;
     let sigF = mk_sigF sig;
     let needed_types = needed_types_code sig;
     let types = maximal_types needed_types;
     check_allm (\<lambda>ty.
       let S = filter (\<lambda>r. type_of_rule sigF r \<in> set (needed_types ty)) R' in
       existsM (check_litsim_trs S) ([] # Rs')
         <? (showsl_lit (STR ''persistent decomposition: missing system induced by sort '') \<circ> showsl ty \<circ> showsl_lit (STR '':'')
            \<circ> showsl_nl \<circ> showsl_trs (map (\<lambda>(l,r). (map_vars_term snd l, map_vars_term snd r)) S))
       ) types
   }"

lemma isOK_check_persistence_cr:
  fixes R :: "('f, 'v :: {infinite, showl}) rule list"
  assumes "isOK (check_persistence_cr R Rs)" "\<And>R. R \<in> set Rs \<Longrightarrow> CR (rstep' (set R) :: (_, 'w :: infinite) trs)"
  shows "CR (rstep' (set R) :: (_, 'w) trs)"
proof -
  let ?res1 = "run (check_persistence1 R Rs)"
  let ?maximal_types = "maximal_types (needed_types_code sig)"
  define R' Rs' where "R' = fst ?res1" and "Rs' = snd ?res1"
  have *: "isOK (local.check_persistence1 R Rs)"
    "\<And>ty. ty \<in> set ?maximal_types \<Longrightarrow>
       let S = filter (\<lambda>r. type_of_rule (mk_sigF sig) r \<in> set (needed_types_code sig ty)) R' in
       S = [] \<or> (\<exists>R \<in> set Rs'. set S \<doteq> set R)"
    using assms(1)
      by (auto simp: check_persistence_cr_def R'_def Rs'_def isOK_try_catch check_litsim_trs intro!: filter_False)
  have sig: "sig_is_clean sig" and wfx: "wf_trs (set R')" "\<And>S. S \<in> set Rs' \<Longrightarrow> wf_trs (set S)" and
    ty: "\<And>r. r \<in> set R' \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)"
      "\<And>S r. S \<in> set Rs' \<Longrightarrow> r \<in> set S \<Longrightarrow> \<exists>\<alpha>. \<T>\<^sub>\<alpha> \<alpha> (fst r) \<and> \<T>\<^sub>\<alpha> \<alpha> (snd r)" and
    cr: "CR (rstep' (set R) :: (_, 'w) trs) \<longleftrightarrow> CR (rstep' (set R') :: (_, 'w) trs)"
      "(\<forall>S \<in> set Rs. CR (rstep' (set S) :: (_, 'w) trs)) \<longleftrightarrow> (\<forall>S \<in> set Rs'. CR (rstep' (set S) :: (_, 'w) trs))"
    using isOK_check_persistence1[OF *(1)] by (auto simp: R'_def Rs'_def)
  interpret persistent_cr_infinite_vars "mk_sigF sig" "Some \<circ> snd" "set R'"
    using wfx(1) ty(1) by (auto intro: interpret_persistent_cr_infinite_vars)
  have "\<And>S. S \<in> set Rs' \<Longrightarrow> funas_trs (set S) \<subseteq> \<F>"
    using ty(2) \<T>\<^sub>\<alpha>_\<T> by (auto simp: funas_trs_def funas_rule_def \<T>_def) blast+
  then have **: "\<And>R. R \<in> set Rs' \<Longrightarrow> CR_on (rstep (set R)) \<T>"
    using assms(2) wfx(2) cr(2) by (auto simp: CR_change_variables_iff' \<T>_def CR_on_iff_CR)
  have "CR_on (rstep (set R')) \<T>"
  proof (intro persistent_decomposition[of "set ?maximal_types", THEN iffD2] ballI, goal_cases)
    case (1 \<beta>) show ?case by (rule maximal_types_prop[OF wfx(1) sig])
  next
    case (2 \<alpha>)
    have x: "set [r\<leftarrow>R' . type_of_rule (mk_sigF sig) r \<in> set (needed_types_code sig \<alpha>)] = \<Union>{\<R>\<^sub>\<alpha> \<beta> |\<beta>. needed_types \<alpha> \<beta>}"
      using sig ty(1) wfx(1)
      apply (auto simp: needed_types_code wf_trs_def' split: prod.splits)
      apply (smt type_of_rule_simp in_pair_collect_simp)
      done
    have [simp]: "rstep' {} = {}" by (auto elim: rstep'.cases)
    have [simp]: "R = {} \<Longrightarrow> CR_on (rstep' R) X" for R X by (auto simp: CR_on_def)
    show ?case
      using *(2)[OF 2, unfolded x Let_def set_empty2[symmetric]] **
      by (auto simp: rstep_eq_rstep' rstep'_eq_litsim_trs)
  qed
  then show ?thesis using wfx(1) \<R>_sig
    by (auto simp: cr(1) CR_change_variables_iff' CR_on_iff_CR \<T>_def)
qed

(* export_code \<T>\<^sub>\<alpha>_code sig_is_clean needed_types_code sigF_arcs_code check_persistence_not_cr in Haskell *)

(* export_code check_persistence_cr in Haskell *)

end (* context *)

end (* LS_Persistence *)
