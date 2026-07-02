theory Tree_Automata_Wit_Impl
imports
  "HOL-Library.RBT"
  Collections.RBTSetImpl
  Collections.RBTMapImpl
  Tree_Automata_Wit
  Tree_Automata_Autoref_Setup
  First_Order_Rewriting.Trs_Impl
begin

lemma dflt_TA_rel_finite[intro]:
  assumes "(TA', TA) \<in> dflt_ta_rel"
    shows "ta_finite TA"
using assms unfolding dflt_ta_rel_def ta_finite_def
by (auto split: prod.splits simp: list_set_rel_def br_def)

definition has_res_wit where
  "has_res_wit m r \<equiv> case r of TA_rule f qs q \<Rightarrow>
    do { ts \<leftarrow> mapM (\<lambda>x. op_map_lookup x m) qs; Some (q, Fun f ts) }"

definition next_res_wit_refine where
  "next_res_wit_refine rs m \<equiv> FOREACH\<^sub>C rs (\<lambda>w. w = None) (\<lambda>r _. RETURN (has_res_wit m r)) None"

lemma next_res_wit_refine:
  assumes "finite rs"
    shows "next_res_wit_refine rs m \<le> SPEC(next_res_wit_inv rs m)"
unfolding next_res_wit_refine_def next_res_wit_inv_def
proof (refine_vcg FOREACHc_rule[where I="\<lambda>it. next_res_wit_inv (rs - it) m"], goal_cases)
  case prems: (3 r it w)
    obtain f qs q where r: "r = TA_rule f qs q" by (cases r)
    from prems show ?case unfolding r next_res_wit_inv_def
      by (cases "mapM m qs", simp_all add: has_res_wit_def, auto simp: mapM_None dest: mapM_Some)
qed (auto simp: next_res_wit_inv_def assms)

schematic_goal next_res_wit_refine_aux:
  assumes [autoref_rules]: "(R',R) \<in> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(M',M) \<in> \<langle>Id,\<langle>Id,V\<rangle>term_rel\<rangle>comp_rm_rel"
  shows "(?f, next_res_wit_refine R M) \<in> \<langle>\<langle>Id \<times>\<^sub>r \<langle>Id,V\<rangle>term_rel\<rangle>option_rel\<rangle>nres_rel"
unfolding next_res_wit_refine_def[abs_def] has_res_wit_def
by (autoref_monadic (plain))

concrete_definition next_res_wit_code uses next_res_wit_refine_aux

definition [simp]: "op_next_res_wit rs m \<equiv> SPEC(next_res_wit_inv rs m)"
context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "SPEC(next_res_wit_inv rs m) \<equiv> op_next_res_wit$rs$m"
by simp_all
end

lemma next_res_wit_autoref[autoref_rules]:
  "(\<lambda>rs m. RETURN (next_res_wit_code rs m), op_next_res_wit) \<in>
    \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel \<rightarrow> \<langle>Id,\<langle>Id,V\<rangle>term_rel\<rangle>comp_rm_rel \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r \<langle>Id,V\<rangle>term_rel\<rangle>option_rel\<rangle>nres_rel"
proof (intro fun_relI, goal_cases)
  case prems: (1 rs rs' m m')
    then have fin: "finite rs'" by (auto simp add: map2set_rel_def rbt_map_rel_def rbt_map_rel'_def br_def)
    note next_res_wit_code.refine[OF prems, THEN nres_relD]
    also note next_res_wit_refine[OF fin]
    finally show ?case by (auto intro: nres_relI)
qed

lemma [autoref_itype]:
  "op_next_res_wit ::\<^sub>i \<langle>\<langle>F,Q\<rangle>\<^sub>ii_ta_rule\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>Q,\<langle>F,V\<rangle>\<^sub>ii_term\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>Q,\<langle>F,V\<rangle>\<^sub>ii_term\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option\<rangle>\<^sub>ii_nres"
by simp_all

definition "update_all_refine m ks v \<equiv> FOREACH ks (\<lambda>k m. RETURN (m(k \<mapsto> v))) m"

lemma update_all_ref:
  assumes "finite ks"
  shows "update_all_refine m ks v \<le> RETURN(update_all m ks v)"
unfolding update_all_refine_def
by (refine_vcg FOREACH_rule[OF assms, where I="\<lambda>it r. r = update_all m (ks - it) v"])
   (auto simp: update_all_def fun_eq_iff)

schematic_goal update_all_refine_aux:
  assumes [autoref_rules]: "(M',M) \<in> \<langle>Id,Rv\<rangle>comp_rm_rel"
  assumes [autoref_rules]: "(S',S) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(V',V) \<in> Rv"
  shows "(?f::?'a, update_all_refine M S V) \<in> ?R"
unfolding update_all_refine_def[abs_def]
by (autoref_monadic (plain))

concrete_definition update_all_code uses update_all_refine_aux

lemma update_all_autoref[autoref_rules]:
  assumes "PREFER_id Rk"
  shows "(update_all_code, update_all) \<in> \<langle>Rk,Rv\<rangle>comp_rm_rel \<rightarrow> \<langle>Rk\<rangle>comp_rs_rel \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>comp_rm_rel"
proof (intro fun_relI, goal_cases)
  from assms have id[simp]: "Rk = Id" by simp
  case rel: (1 m m' ks ks')
    then have fin: "finite ks'" by (auto simp add: map2set_rel_def rbt_map_rel_def rbt_map_rel'_def br_def)
    note update_all_code.refine[OF rel[unfolded id], THEN nres_relD] 
    also note update_all_ref[OF fin]
    finally show ?case by simp
qed

definition update_all2_refine where
  "update_all2_refine m ks1 ks2 v \<equiv>
    FOREACH ks1
      (\<lambda>k1 m. let m' = update_all (case_option Map.empty id (m k1)) ks2 v in
        RETURN (m(k1 \<mapsto> m'))) m"

lemma update_all2_ref:
  assumes "finite ks1"
  shows "update_all2_refine m ks1 ks2 v \<le> RETURN(update_all2 m ks1 ks2 v)"
unfolding update_all2_refine_def update_all_def
by (refine_vcg FOREACH_rule[OF assms, where I="\<lambda>it r. r = update_all2 m (ks1 - it) ks2 v"])
   (auto simp: update_all2_def fun_eq_iff split: option.split)

schematic_goal update_all2_refine_aux:
  assumes [autoref_rules]: "(M',M) \<in> \<langle>Id,\<langle>Id,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
  assumes [autoref_rules]: "(S1',S1) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(S2',S2) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(V',V) \<in> Rv"
  shows "(?f::?'a, update_all2_refine M S1 S2 V) \<in> ?R"
unfolding update_all2_refine_def[abs_def]
by (autoref_monadic (plain))

concrete_definition update_all2_code uses update_all2_refine_aux

lemma update_all2_autoref[autoref_rules]:
  assumes "PREFER_id Rk1" and "PREFER_id Rk2"
  shows "(update_all2_code, update_all2) \<in> \<langle>Rk1,\<langle>Rk2,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel \<rightarrow> \<langle>Rk1\<rangle>comp_rs_rel \<rightarrow> \<langle>Rk2\<rangle>comp_rs_rel \<rightarrow> Rv \<rightarrow> \<langle>Rk1,\<langle>Rk2,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
proof (intro fun_relI, goal_cases)
  from assms have id[simp]: "Rk1 = Id" "Rk2 = Id" by simp_all
  case rel: (1 m m' ks1 ks1' ks2 ks2' v v')
    then have fin: "finite ks1'" by (auto simp add: map2set_rel_def rbt_map_rel_def rbt_map_rel'_def br_def)
    note update_all2_code.refine[OF rel[unfolded id], THEN nres_relD]
    also note update_all2_ref[OF fin]
    finally show ?case by simp
qed

definition map_add2_refine where
  "map_add2_refine m1 m2 \<equiv>
    FOREACH (map_to_set m2)
      (\<lambda>(k,v) m. RETURN (case m k of Some v' \<Rightarrow> m(k \<mapsto> v' ++ v) | None \<Rightarrow> m(k \<mapsto> v))) m1"

lemma map_add2_ref:
  assumes "finite (dom m2)"
  shows "map_add2_refine m1 m2 \<le> RETURN(map_add2 m1 m2)"
proof -
  note rule = FOREACH_rule[where I="\<lambda>it r. r = map_add2 m1 (set_to_map ((map_to_set m2) - it))"]
  show ?thesis unfolding map_add2_refine_def
  proof (refine_vcg rule, simp_all only: it_step_insert_iff, goal_cases)
    case prems: (3 _ it r k v)
      note inj_diff = inj_on_image_set_diff[OF inj_on_fst_map_to_set Diff_subset]
      from prems have fst: "fst (k,v) \<notin> fst ` (map_to_set m2 - it)" by (auto simp: inj_diff)
      note inj = inj_on_fst_map_to_set[THEN inj_on_diff]
      note [simp] = fun_eq_iff map_add2_def Map.map_add_def set_to_map_simp[OF inj] set_to_map_insert[OF fst]
      from fst show ?case by (auto split: option.splits)
  qed (simp_all add: map_to_set_inverse map_add2_def finite_map_to_set assms fun_eq_iff)
qed

schematic_goal map_add2_refine_aux:
  assumes [autoref_rules]: "(M1',M1) \<in> \<langle>Id,\<langle>Id,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
  assumes [autoref_rules]: "(M2',M2) \<in> \<langle>Id,\<langle>Id,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
  shows "(?f::?'a, map_add2_refine M1 M2) \<in> ?R"
unfolding map_add2_refine_def[abs_def]
by (autoref_monadic (plain))

concrete_definition map_add2_code uses map_add2_refine_aux

lemma map_add2_autoref[autoref_rules]:
  assumes "PREFER_id Rk1" and "PREFER_id Rk2"
  shows "(map_add2_code, map_add2) \<in> \<langle>Rk1,\<langle>Rk2,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel \<rightarrow> \<langle>Rk1,\<langle>Rk2,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel \<rightarrow> \<langle>Rk1,\<langle>Rk2,Rv\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
proof (intro fun_relI, goal_cases)
  from assms have id[simp]: "Rk1 = Id" "Rk2 = Id" by simp_all
  case prems: 1
    note map_add2_code.refine[OF prems[unfolded id], THEN nres_relD]
    also note map_add2_ref
    finally show ?case using prems by simp
qed

subsection \<open>Refinement of @{term res_wits}\<close>

abbreviation "res_wit_map_rel \<equiv> \<langle>Id,\<langle>Id,Id\<rangle>term_rel\<rangle>comp_rm_rel"

schematic_goal res_wits_refine_aux:
  shows "(?f, res_wits) \<in> dflt_ta_rel \<rightarrow> \<langle>res_wit_map_rel\<rangle>nres_rel"
unfolding res_wits_def[abs_def]
by (autoref (keep_goal))

concrete_definition res_wits_impl uses res_wits_refine_aux
lemmas [autoref_rules] = res_wits_impl.refine

schematic_goal res_wits_transfer_aux: 
  "RETURN ?c \<le> res_wits_impl TAi"
unfolding res_wits_impl_def 
by (refine_transfer (post))

concrete_definition res_wits_code for TAi uses res_wits_transfer_aux
lemmas [refine_transfer] = res_wits_code.refine

schematic_goal ta_only_res_wits_refine_aux:
  shows "(?f, ta_only_res_wits) \<in> dflt_ta_rel \<rightarrow> res_wit_map_rel \<rightarrow> dflt_ta_rel"
unfolding ta_only_res_wits_def[abs_def]
by autoref

concrete_definition ta_only_res_wits_code uses ta_only_res_wits_refine_aux
lemmas [autoref_rules] = ta_only_res_wits_code.refine

schematic_goal ta_only_res_wits_code_post_simp_opt:
  "RETURN ?f \<le> RETURN (ta_only_res_wits_code a b)"
unfolding ta_only_res_wits_code_def
by (refine_transfer (post))

lemmas [code] = ta_only_res_wits_code_post_simp_opt[unfolded nres_order_simps, symmetric]

schematic_goal ta_only_res_autoref_aux:
  assumes [autoref_rules]: "(TA', TA) \<in> dflt_ta_rel"
  shows "(RETURN ?f, ta_only_res TA) \<in> \<langle>dflt_ta_rel\<rangle>nres_rel"
unfolding ta_only_res_def comp_def
by (autoref_monadic (plain))

concrete_definition ta_only_res_code for TA' uses ta_only_res_autoref_aux

lemma ta_only_res_autoref[autoref_rules]:
    shows "(ta_only_res_code, ta_only_reach) \<in> dflt_ta_rel \<rightarrow> dflt_ta_rel"
proof (intro fun_relI, goal_cases)
  case rel: (1 TA' TA)
    then have fin: "ta_finite TA" by auto
    note ta_only_res_code.refine[OF rel, THEN nres_relD]
    also note ta_only_res[OF fin]
    finally show ?case by simp
qed

subsection \<open>Refinement of @{term prs_wits}\<close>
  
lemma eps_invcls_impl:
  "eps_icls TA qs = op_union_image qs (eps_icl TA)"
by auto

lemma the_Var_autoref:
  "PREFER_id V \<Longrightarrow> PREFER_id F \<Longrightarrow> (the_Var, the_Var) \<in> \<langle>F,V\<rangle>term_rel \<rightarrow> V"
by simp

abbreviation "prs_wit_map \<equiv> \<langle>Id,\<langle>Id,\<langle>Id,Id\<rangle>term_rel\<rangle>actxt_rel\<rangle>comp_rm_rel"

schematic_goal prs_wits_refine_aux:
  notes [autoref_rules] = the_Var_autoref
  shows "(?f, prs_wits) \<in> dflt_ta_rel \<rightarrow> \<langle>prs_wit_map\<rangle>nres_rel"
unfolding prs_wits_def[abs_def] add_prs_wit_def add_prs_wit_aux_def eps_invcls_impl
by autoref

concrete_definition prs_wits_impl uses prs_wits_refine_aux
lemmas [autoref_rules] = prs_wits_impl.refine

schematic_goal prs_wits_transfer_aux: 
  "RETURN ?c \<le> prs_wits_impl TAi"
unfolding prs_wits_impl_def 
by (refine_transfer (post))

concrete_definition prs_wits_code for TAi uses prs_wits_transfer_aux
lemmas [refine_transfer] = prs_wits_code.refine

schematic_goal ta_only_prs_wits_refine_aux:
  "(?f, ta_only_prs_wits) \<in> dflt_ta_rel \<rightarrow> prs_wit_map \<rightarrow> dflt_ta_rel"
unfolding ta_only_prs_wits_def[abs_def]
by autoref

concrete_definition ta_only_prs_wits_code uses ta_only_prs_wits_refine_aux
lemmas [autoref_rules] = ta_only_prs_wits_code.refine

schematic_goal ta_only_prs_wits_code_post_simp_opt:
  "RETURN ?f \<le> RETURN (ta_only_prs_wits_code a b)"
unfolding ta_only_prs_wits_code_def
by (refine_transfer (post))

lemmas [code] = ta_only_prs_wits_code_post_simp_opt[unfolded nres_order_simps, symmetric]

schematic_goal ta_only_prs_autoref_aux:
  assumes [autoref_rules]: "(TA', TA) \<in> dflt_ta_rel"
  shows "(RETURN ?f, ta_only_prs TA) \<in> \<langle>dflt_ta_rel\<rangle>nres_rel"
unfolding ta_only_prs_def comp_def
by (autoref_monadic (plain))

concrete_definition ta_only_prs_code for TA' uses ta_only_prs_autoref_aux

lemma ta_only_prs_autoref[autoref_rules]:
    shows "(ta_only_prs_code, ta_only_prod) \<in> dflt_ta_rel \<rightarrow> dflt_ta_rel"
proof (intro fun_relI, goal_cases)
  case rel: (1 TA' TA)
    then have fin: "ta_finite TA" by auto
    note ta_only_prs_code.refine[OF rel, THEN nres_relD]
    also note ta_only_prs[OF fin]
    finally show ?case by simp
qed

subsection \<open>Refinement of @{term trim_ta_wits}\<close>

schematic_goal trim_ta_wits_aux:
  shows "(?f, trim_ta_wits) \<in> dflt_ta_rel \<rightarrow> \<langle>dflt_ta_rel \<times>\<^sub>r res_wit_map_rel \<times>\<^sub>r prs_wit_map\<rangle>nres_rel"
unfolding trim_ta_wits_def[abs_def]
by autoref

concrete_definition trim_ta_wits_impl uses trim_ta_wits_aux
lemmas [autoref_rules] = trim_ta_wits_impl.refine

schematic_goal trim_ta_wits_transfer_aux: 
  "RETURN ?c \<le> trim_ta_wits_impl TAi"
unfolding trim_ta_wits_impl_def 
by (refine_transfer (post))

concrete_definition trim_ta_wits_code for TAi uses trim_ta_wits_transfer_aux
lemmas [refine_transfer] = trim_ta_wits_code.refine

subsection \<open>Refinement of @{term ta_res}\<close>

definition ta_res_args_aux :: "(_,_)ta \<Rightarrow> _" where
  "ta_res_args_aux TA f qss \<equiv>
    \<Union>((\<lambda>r. case r of TA_rule f' qs q \<Rightarrow>
          if f' = f \<and> list_all2 (\<lambda>qi qsi. qi \<in> qsi) qs qss then eps_cl TA q else {}
      ) ` (ta_rules TA))"

definition ta_res_args_aux_opt :: "(_,_)ta \<Rightarrow> _" where
  "ta_res_args_aux_opt TA f qss \<equiv>
    case ta_idx TA (f, length qss) of
      None \<Rightarrow> {}
    | Some rs \<Rightarrow> \<Union>((\<lambda>(qs,q). if list_all2 (\<lambda>qi qsi. qi \<in> qsi) qs qss then eps_cl TA q else {}) ` rs)"

lemma ta_res_args_aux_opt:
  "ta_res_args_aux TA f qss = ta_res_args_aux_opt TA f qss"
by (auto simp: ta_idx_def ta_res_args_aux_def ta_res_args_aux_opt_def list_all2_conv_all_nth
        split: ta_rule.splits option.splits if_splits) (metis)

schematic_goal ta_res_args_aux_ref_aux:
  "(?f, ta_res_args_aux) \<in> dflt_ta_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>Id\<rangle>comp_rs_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
unfolding ta_res_args_aux_opt[abs_def] ta_res_args_aux_opt_def
by (autoref (debug))

concrete_definition ta_res_args_aux_code uses ta_res_args_aux_ref_aux
lemmas [autoref_rules] = ta_res_args_aux_code.refine

primrec ta_res_impl where
  "ta_res_impl TA (Var q) = eps_cl TA q"
| "ta_res_impl TA (Fun f ts) = (let qss = map (ta_res_impl TA) ts in ta_res_args_aux TA f qss)"

lemma ta_res_impl: "ta_res TA t = ta_res_impl TA t"
by (induction t, auto simp add: ta_res_args_aux_def list_all2_conv_all_nth split: ta_rule.splits if_splits)
    metis

schematic_goal ta_res_impl_aux:
  shows "(?f, ta_res_impl) \<in> dflt_ta_rel \<rightarrow> \<langle>Id,Id\<rangle>term_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
unfolding ta_res_impl_def[abs_def] 
by autoref

concrete_definition ta_res_code uses ta_res_impl_aux

lemma ta_res_autoref[autoref_rules]:
  "(ta_res_code, ta_res) \<in> dflt_ta_rel \<rightarrow> \<langle>Id,Id\<rangle>term_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
using ta_res_code.refine unfolding ta_res_impl[abs_def] by simp

subsection \<open>Refinement of @{term ta_match}\<close>

definition set_App where
"set_App X XS = {z | z x xs. z = x @ xs \<and> x \<in> X \<and> xs \<in> XS}"

definition "set_App_ref X XS \<equiv> FOREACH X (\<lambda>x r. FOREACH XS (\<lambda>xs r. RETURN (insert (x@xs) r)) r) {}"

primrec concat_listset where
"concat_listset [] = {[]}" |
"concat_listset (A # As) = set_App A (concat_listset As)"

lemma concat_listset: "concat ` listset m = concat_listset m"
proof (induction m, auto simp add: set_Cons_def set_App_def, goal_cases)
  case prems: (2 A m x xs)
    let ?P = "\<lambda>x xs. x \<in> A \<and> xs \<in> listset m"
    have "concat ` {x # xs |x xs. ?P x xs} = {concat (x#xs) |x xs. ?P x xs}" by blast
    also have "... = {x@concat xs |x xs. ?P x xs}" by simp
    also have "... = {x@xs | x xs. x \<in> A \<and> xs \<in> concat ` listset m}" by auto
    finally show ?case using prems by auto
qed blast

lemma set_App_ref:
  assumes X: "finite X"
      and XS: "finite XS"
    shows "set_App_ref X XS \<le> RETURN(set_App X XS)"
proof -
  note ruleX = FOREACH_rule[OF X, where I = "\<lambda>itX r. r = set_App (X - itX) XS"]
  show ?thesis unfolding set_App_ref_def
  proof (refine_vcg ruleX, goal_cases)
    case prems: (2 x itX r)
    let ?I = "\<lambda>itXS r. r = set_App (X - itX) XS \<union> set_App (insert x (X - itX)) (XS - itXS)"
    note ruleXS = FOREACH_rule[OF XS, where I = ?I]
    from prems show ?case by (refine_vcg ruleXS, simp_all add: set_App_def, blast+)
  qed (simp_all add: set_App_def)
qed

schematic_goal set_App_ref_aux: 
  assumes [autoref_rules]: "(X',X) \<in> \<langle>\<langle>Id\<rangle>list_rel\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(XS',XS) \<in> \<langle>\<langle>Id\<rangle>list_rel\<rangle>comp_rs_rel"
  shows "(?f, set_App_ref X XS) \<in> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>comp_rs_rel\<rangle>nres_rel"
unfolding set_App_ref_def[abs_def] 
by (autoref_monadic (plain))

concrete_definition set_App_code uses set_App_ref_aux

lemma set_App_autoref[autoref_rules]:
  assumes "PREFER_id A"
  shows "(set_App_code, set_App) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>comp_rs_rel"
proof (intro fun_relI, goal_cases)
  from assms have id[simp]: "A = Id" by simp_all
  case prems: (1 X X' XS XS')
    then have fin: "finite X'" "finite XS'" by auto
    note set_App_code.refine[OF prems[unfolded id], THEN nres_relD]
    also note set_App_ref[OF fin]
    finally show ?case by simp
qed

schematic_goal concat_listset_aux:
  assumes [relator_props]:  "A = Id"
  shows "(?f, concat_listset) \<in> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>comp_rs_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>comp_rs_rel"
unfolding concat_listset_def[abs_def] 
by autoref

concrete_definition concat_listset_code uses concat_listset_aux

definition [simp]: "op_concat_listset X \<equiv> concat ` listset X"
context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "concat ` listset X \<equiv> op_concat_listset$X"
by simp_all
end

lemma concat_listset_autoref[autoref_rules]:
  assumes "PREFER_id A"
  shows "(concat_listset_code, op_concat_listset) \<in> \<langle>\<langle>\<langle>A\<rangle>list_rel\<rangle>comp_rs_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>comp_rs_rel"
using concat_listset_code.refine[OF PREFER_id_D[OF assms(1)]]
unfolding op_concat_listset_def[abs_def] concat_listset PREFER_id_D[OF assms(1)] .

definition ta_match_var :: "(_,_)ta \<Rightarrow> _" where
  "ta_match_var TA Qsig x Q \<equiv> { [(x,q')] | q'. q' \<in> Qsig \<and> (\<exists> q \<in> Q. (q',q) \<in> (ta_eps TA)\<^sup>*)}"

definition ta_match_var_ref :: "(_,_)ta \<Rightarrow> _" where
  "ta_match_var_ref TA Qsig x Q \<equiv>
    FOREACH Qsig (\<lambda>q res. RETURN (if eps_cl TA q \<inter> Q \<noteq> {} then insert [(x,q)] res else res)) {}"

lemma ta_match_var_ref:
  assumes "finite Qsig"
  shows "ta_match_var_ref TA Qsig x Q \<le> RETURN(ta_match_var TA Qsig x Q)"
unfolding ta_match_var_ref_def
by (refine_vcg FOREACH_rule[OF assms, where I = "\<lambda>it r. r = ta_match_var TA (Qsig - it) x Q"])
   (auto simp: ta_match_var_def)

schematic_goal ta_match_var_ref_aux:
  assumes [autoref_rules]: "(TA',TA) \<in> dflt_ta_rel"
  assumes [autoref_rules]: "(Qsig',Qsig) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(x',x) \<in> Id"
  assumes [autoref_rules]: "(Q',Q) \<in> \<langle>Id\<rangle>comp_rs_rel"
  shows "(?f, ta_match_var_ref TA Qsig x Q) \<in> \<langle>\<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel\<rangle>nres_rel"
unfolding ta_match_var_ref_def[abs_def]
by (autoref_monadic (plain))

concrete_definition ta_match_var_ref_code uses ta_match_var_ref_aux

lemma ta_match_var_refine:
  "(ta_match_var_ref_code, ta_match_var) \<in> dflt_ta_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel"
proof (intro fun_relI, goal_cases)
  case rel: (1 _ _ Qsig Qsig')
    then have finite: "finite Qsig'" by (simp add: br_def)
    note ta_match_var_ref_code.refine[OF rel, THEN nres_relD]
    also note ta_match_var_ref[OF finite]
    finally show ?case by simp
qed

definition ta_match_fun :: "(_,_)ta \<Rightarrow> _" where
  "ta_match_fun TA f n Q rec \<equiv>
    \<Union>((\<lambda>r. case r of TA_rule f' qs q \<Rightarrow>
          if f = f' \<and> length qs = n \<and> eps_cl TA q \<inter> Q \<noteq> {} then
            concat ` (listset (rec qs))
          else
            {}) ` (ta_rules TA))"

definition ta_match_fun_opt :: "(_,_)ta \<Rightarrow> _" where
  "ta_match_fun_opt TA f n Q rec \<equiv>
    case ta_idx TA (f, n) of
      None \<Rightarrow> {}
    | Some rs \<Rightarrow>
        \<Union>((\<lambda>(qs,q).
            if eps_cl TA q \<inter> Q \<noteq> {} then
              concat ` (listset (rec qs))
            else
              {}) ` rs)"

lemma ta_match_fun_opt:
  "ta_match_fun TA f n Q rec = ta_match_fun_opt TA f n Q rec"
by (auto simp: ta_match_fun_def ta_match_fun_opt_def ta_idx_def
        split: ta_rule.splits option.splits if_splits) blast

schematic_goal ta_match_fun_aux:
  shows "(?f, ta_match_fun) \<in>
    dflt_ta_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> (\<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel\<rangle>list_rel) \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel"
unfolding ta_match_fun_opt[abs_def] ta_match_fun_opt_def
by autoref

concrete_definition ta_match_fun_code uses ta_match_fun_aux
thm ta_match_fun_code_def

fun map2 where
  "map2 f [] ys = []"
| "map2 f xs [] = []"
| "map2 f (x#xs) (y#ys) = f x y # map2 f xs ys"

lemma map2_cong[fundef_cong]:
  assumes "xs = xs'" and "\<And>x y. x \<in> set xs' \<Longrightarrow> f x y = g x y"
  shows "map2 f xs = map2 g xs'"
unfolding fun_eq_iff proof (intro allI)
  fix x
  show "map2 f xs x = map2 g xs' x" 
    using assms by (induction f xs x arbitrary: xs' rule: map2.induct) auto
qed

fun ta_match_impl where
  "ta_match_impl TA Qsig (Var x) Q =
    ta_match_var TA Qsig x Q"
| "ta_match_impl TA Qsig (Fun f ts) Q =
    ta_match_fun TA f (length ts) Q (map2 (\<lambda>t Q. ta_match_impl TA Qsig t {Q}) ts)"

fun ta_match_code where
  "ta_match_code TA Qsig (Var x) Q =
    ta_match_var_ref_code TA Qsig x Q"
| "ta_match_code TA Qsig (Fun f ts) Q =
    ta_match_fun_code TA f (length ts) Q (map2 (\<lambda>t Q. ta_match_code TA Qsig t (rbt_comp_insert compare Q () rbt.Empty)) ts)"

lemma map2_param2_cong:
  assumes "\<And>x y y' . x \<in> set xs \<Longrightarrow> (y,y') \<in> Rb \<Longrightarrow> (f x y, f' x y') \<in> Rc"
      and "(ys,ys') \<in> \<langle>Rb\<rangle>list_rel"
    shows "(map2 f xs ys, map2 f' xs ys') \<in> \<langle>Rc\<rangle>list_rel"           
using assms by (induction f xs ys arbitrary: ys' rule: map2.induct, auto elim!: list_relE)                          

schematic_goal sng_autoref:
  assumes[autoref_rules]: "(y',y) \<in> Id"
  shows "(?f, {y}) \<in> \<langle>Id\<rangle>comp_rs_rel"
by autoref

lemma ta_match_code_ref:
  "(ta_match_code, ta_match_impl) \<in> dflt_ta_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>Id,Id\<rangle>term_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel"
proof (intro fun_relI, goal_cases)
  case (1 _ _ _ _ t t' Q Q')
    then show ?case proof (induction t arbitrary: t' Q Q')
      case (Fun f ts)
        then show ?case
        apply (auto elim!: term_relE simp only: ta_match_code.simps ta_match_impl.simps)
        apply (intro ta_match_fun_code.refine[THEN fun_relD5'])
        apply (simp_all)
        apply (intro fun_relI map2_param2_cong[where Rb = "Id"])
        apply (parametricity)
        apply (auto simp: br_def intro: sng_autoref)
        done
    qed (insert ta_match_var_refine, auto elim!: term_relE dest: fun_relD)
qed

lemma map2_length_eq:
  assumes "length ys = length xs"
    shows "length (map2 g xs ys) = length xs"
using assms by (induction rule: list_induct2, auto)

lemma Suc_lengthE:
  assumes "length xs = Suc (length ys)"
  obtains z zs where "xs = z#zs" "length zs = length ys"
using assms by (cases xs) auto

lemma ta_match_impl:
  fixes TA :: "('q,'f)ta" and t :: "('f,'v)term"
  shows "ta_match_impl TA Qsig t Q = ta_match TA Qsig t Q"
proof (induction t arbitrary: Q)
  case (Fun f ts)
    {
      fix qs :: "'q list" and  xs :: "('v\<times>'q) list list" and i
      assume i: "i < length ts" and lenxs: "length xs = length ts" and lenqs: "length qs = length ts"
      from i Fun.IH have IH: "ta_match TA Qsig (ts!i) {qs!i} = ta_match_impl TA Qsig (ts!i) {qs!i}" by auto
      have "xs!i \<in> map2 (\<lambda>t Q. ta_match_impl TA Qsig t {Q}) ts qs ! i \<longleftrightarrow> xs!i \<in>  ta_match TA Qsig (ts!i) {qs!i}"
      using lenqs lenxs i unfolding IH
      by (induction arbitrary: xs i rule: list_induct2) (auto simp: nth_Cons split: nat.splits elim!: Suc_lengthE)
    } note IH = this
    show ?case by (force simp add: IH ta_match_fun_def listset map2_length_eq split: ta_rule.splits if_splits)
qed (simp add: ta_match_var_def)

lemma ta_match_autoref[autoref_rules]:
  "(ta_match_code, ta_match) \<in> dflt_ta_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>Id,Id\<rangle>term_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>comp_rs_rel"
using ta_match_code_ref unfolding ta_match_impl[abs_def] by simp

schematic_goal ta_match_code_post_simp_opt: 
  "RETURN ?c \<le> RETURN (ta_match_code a b (Fun c d) e)"
unfolding ta_match_code.simps[abs_def] ta_match_fun_code_def
by (refine_transfer (post))

lemmas [code] = ta_match_code_post_simp_opt[unfolded nres_order_simps, symmetric] ta_match_code.simps(1)

subsection \<open>Refinement of @{term is_compatible}\<close>

lemma [autoref_rules, param]:
  "(isOK, isOK) \<in> \<langle>A,B\<rangle>sum_rel \<rightarrow> Id"
unfolding isOK_def[abs_def] by parametricity

lemma fun_of_idref:
  "PREFER_id A \<Longrightarrow> PREFER_id B \<Longrightarrow> (fun_of, fun_of) \<in> \<langle>A \<times>\<^sub>r B\<rangle>list_rel \<rightarrow> A \<rightarrow> B"
by simp

lemma isOK_is_Inr:
  "isOK e = is_Inr e"
by (cases e, simp_all)

abbreviation "term_pair \<equiv> \<langle>Id,Id\<rangle>term_rel \<times>\<^sub>r \<langle>Id,Id\<rangle>term_rel"
abbreviation "wit_tuple \<equiv> Id \<times>\<^sub>r term_pair"
abbreviation "wit_rel \<equiv> \<langle>Id,\<langle>Id,term_pair\<rangle>comp_rm_rel\<rangle>comp_rm_rel"
abbreviation "wit_result \<equiv> \<langle>wit_tuple, wit_rel\<rangle>sum_rel"
abbreviation "trs \<equiv> \<langle>\<langle>Id,Id::('x::compare \<times> 'x) set\<rangle>term_rel \<times>\<^sub>r \<langle>Id,Id\<rangle>term_rel\<rangle>comp_rs_rel"

schematic_goal is_compatible_aux:
  notes fun_of_idref[autoref_rules]
  shows "(?f, is_compatible) \<in> dflt_ta_rel \<rightarrow> trs \<rightarrow> \<langle>wit_result\<rangle>nres_rel"
unfolding is_compatible_def[abs_def] ta_match'_def isOK_is_Inr
by autoref

concrete_definition is_compatible_impl uses is_compatible_aux
lemmas [autoref_rules] = is_compatible_impl.refine

schematic_goal is_compatible_transfer_aux: 
  "RETURN ?f \<le> is_compatible_impl TA R"
unfolding is_compatible_impl_def
by (refine_transfer (post))

concrete_definition is_compatible_code for TA R uses is_compatible_transfer_aux
lemmas [refine_transfer] = is_compatible_code.refine

subsection \<open>Refinement of @{term is_coh_final}\<close>

schematic_goal is_coh_final_aux:
  shows "(?f, is_coh_final) \<in> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> wit_rel \<rightarrow> \<langle>\<langle>term_pair\<rangle>option_rel\<rangle>nres_rel"
unfolding is_coh_final_def[abs_def]
by autoref

concrete_definition is_coh_final_impl uses is_coh_final_aux
lemmas [autoref_rules] = is_coh_final_impl.refine

schematic_goal is_coh_final_transfer_aux: 
  "RETURN ?f \<le> is_coh_final_impl fin rel"
unfolding is_coh_final_impl_def
by (refine_transfer (post))

concrete_definition is_coh_final_code for fin rel uses is_coh_final_transfer_aux
lemmas [refine_transfer] = is_coh_final_code.refine

subsection \<open>Refinement of @{term ta_check_comcoh}\<close>

definition rule_filter_opt where
  "rule_filter_opt TA f qs \<equiv>
    case ta_idx TA (f, length qs) of None \<Rightarrow> {} | Some rs \<Rightarrow> snd ` {r \<in> rs. case r of (qs',q) \<Rightarrow> qs' = qs}"

schematic_goal rule_filter_opt_ref:
  "(?f, rule_filter_opt) \<in> dflt_ta_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
unfolding rule_filter_opt_def[abs_def]
by autoref

concrete_definition rule_filter_opt_code uses rule_filter_opt_ref
lemmas [autoref_rules] = rule_filter_opt_code.refine

schematic_goal rule_filter_post_simp_opt:
  "RETURN ?f \<le> RETURN (rule_filter_opt_code a b c)"
unfolding rule_filter_opt_code_def
by (refine_transfer (post))

lemmas [code] = rule_filter_post_simp_opt[unfolded nres_order_simps, symmetric]

lemma rule_filter_opt:
  "r_rhs ` {r \<in> ta_rules TA. case r of TA_rule f' qs' q' \<Rightarrow> f' = f \<and> qs' = qs} = rule_filter_opt TA f qs"
by (auto simp: rule_filter_opt_def ta_idx_def image_iff r_rhs_unfold split: ta_rule.splits option.splits)+

lemma autoref_the_id:
  "PREFER_id R \<Longrightarrow> (the, the) \<in> \<langle>R\<rangle>option_rel \<rightarrow> R"
  by simp

schematic_goal ta_check_comcoh_aux:
  notes param_list_update[autoref_rules]
  notes param_upt[autoref_rules]
  notes autoref_the_id[autoref_rules]
  notes isOK_is_Inr[simp]
  shows "(?f, ta_check_comcoh) \<in> dflt_ta_rel \<rightarrow> trs \<rightarrow> \<langle>\<langle>term_pair\<rangle>option_rel\<rangle>nres_rel"
unfolding
  ta_check_comcoh_def[abs_def] ta_check_comcoh_trim_def[folded Subst_apply_term_def] ta_lang_wit_def[abs_def, folded Subst_apply_term_def] comp_def[abs_def]
  is_coh_iterate_ref_def[abs_def] new_rel_def isOK_is_Inr rule_filter_opt
 by autoref

concrete_definition ta_check_comcoh_impl uses ta_check_comcoh_aux

schematic_goal ta_check_comcoh_transfer_aux: 
  "RETURN ?f \<le> ta_check_comcoh_impl TA R"
unfolding ta_check_comcoh_impl_def
by (refine_transfer (post))

concrete_definition ta_check_comcoh_code for TA R uses ta_check_comcoh_transfer_aux

subsection \<open>An easier to use interface\<close>

text \<open>
  A dedicated type for tuples that represent tree automata is defined, and useful functions and
  theorems are lifted accordingly. This enables the usage of refined functions without
  relying on Autoref.
\<close>

schematic_goal ta_empty_autoref:
  "(?c, ta.make {} {} {}) \<in> dflt_ta_rel"
by autoref
           
concrete_definition ta_empty_code uses ta_empty_autoref

definition "ta_make_ls F R E = ta.make (set F) (set R) (set E)"

schematic_goal ta_make_ls_autoref:
  "(?c, ta_make_ls) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>list_rel \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>list_rel \<rightarrow> dflt_ta_rel"
unfolding ta_make_ls_def[abs_def]
by autoref

concrete_definition ta_make_ls_code uses ta_make_ls_autoref

no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

definition "is_ta_code TC \<equiv> \<exists> TA. (TC,TA) \<in> dflt_ta_rel"

lemma is_ta_codeE:
  assumes "is_ta_code TC"
  obtains TA F Q where "(TC, TA) \<in> dflt_ta_rel"
using assms by (auto simp: is_ta_code_def)

lemma is_ta_codeI:
  assumes "(TA, TA') \<in> dflt_ta_rel"
    shows "is_ta_code TA"
using assms by (auto simp: is_ta_code_def)

typedef (overloaded) ('q::compare_order,'f::compare_order) ta_code = "{TC::(_ \<times> (('q, 'f) ta_rule, _) RBT_Impl.rbt \<times> _). is_ta_code TC}"
proof -
  show ?thesis
  by (intro exI[of _ ta_empty_code])
     (auto intro!: ta_empty_autoref simp: ta_empty_code_def is_ta_code_def)
qed

setup_lifting type_definition_ta_code

locale ta_code =
 fixes comp_sym :: "'f :: compare_order"
 fixes comp_state :: "'q :: compare_order"
 fixes comp_var :: "'vc :: compare_order"
begin

context includes rbt.lifting begin

private type_synonym 'a rb_set = "('a, unit) RBT_Impl.rbt"
private type_synonym ('a,'b) rb_ta_rules = "(('a, 'b) ta_rule) rb_set"
private type_synonym ('a,'b) rb_idx = "('b \<times> nat, ('a list \<times> 'a) rb_set) RBT_Impl.rbt"
private type_synonym 'a rb_eps = "'a \<Rightarrow> 'a rb_set"

private type_synonym ('a,'b) ta_code_tuple =
  "'a rb_set \<times> ('a, 'b) rb_ta_rules \<times> ('a \<times> 'a) list \<times>
   'a rb_set \<times> ('a,'b) rb_idx \<times> bool \<times> 'a rb_eps \<times> 'a rb_eps"

private definition rs_abs :: "('a::compare, unit) RBT_Impl.rbt \<Rightarrow> 'a set" where
  "rs_abs S \<equiv> dom (ord.rbt_lookup (comp2lt compare_res) S)"

private definition rm_abs :: "('a::compare, 'b) RBT_Impl.rbt \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "rm_abs S \<equiv> ord.rbt_lookup (comp2lt compare_res) S"

lemma rm_abs_compare_order:
  "rm_abs (S::('a::compare_order, _) RBT_Impl.rbt) = rbt_lookup S"
by (simp add: rm_abs_def ord.rbt_lookup_def rbt_lookup_def lt_of_comp_post_simp ord_defs)

private definition ta_abs :: "('q,'f) ta_code_tuple \<Rightarrow> ('q,'f) ta" where
  "ta_abs TC \<equiv> case TC of (F,R,E,_) \<Rightarrow> ta.make (rs_abs F) (rs_abs R) (set E)"

lift_definition \<alpha> :: "('q,'f)ta_code \<Rightarrow> ('q,'f) ta" is ta_abs .

lift_definition make_ls :: "'q list  \<Rightarrow> ('q, 'f) ta_rule list  \<Rightarrow> ('q \<times> 'q) list \<Rightarrow> ('q,'f)ta_code" is ta_make_ls_code
  by (auto intro: ta_make_ls_code.refine[THEN fun_relD3', THEN is_ta_codeI])

lift_definition res_wits :: "('q,'f)ta_code \<Rightarrow> ('q, ('f, 'v) term) RBT.rbt" is res_wits_code
by (auto elim!: is_ta_codeE
        intro!: is_rbt_compare_refine_spec'[OF
                  res_wits_code.refine
                  res_wits_impl.refine[THEN fun_relD, THEN nres_relD, simplified]
                  res_wits_correct])

lift_definition only_res_wits :: "('q,'f)ta_code \<Rightarrow> ('q, ('f, unit) term) RBT.rbt \<Rightarrow> ('q,'f)ta_code" is ta_only_res_wits_code
by (auto elim!: is_ta_codeE is_rbt_mapE
         intro: ta_only_res_wits_code.refine[THEN fun_relD2', THEN is_ta_codeI])

lift_definition only_res :: "('q,'f)ta_code \<Rightarrow> ('q,'f)ta_code" is "ta_only_res_code"
by (auto elim!: is_ta_codeE
         intro: ta_only_res_autoref[THEN fun_relD, THEN is_ta_codeI])

lift_definition prs_wits :: "('q,'f)ta_code \<Rightarrow> ('q, ('f, 'q) ctxt) RBT.rbt" is prs_wits_code 
by (auto elim!: is_ta_codeE
        intro!: is_rbt_compare_refine_spec'[OF
                  prs_wits_code.refine
                  prs_wits_impl.refine[THEN fun_relD, THEN nres_relD, simplified]
                  prs_wits_correct])

lift_definition only_prs :: "('q,'f)ta_code \<Rightarrow> ('q,'f) ta_code" is ta_only_prs_code
by (auto elim!: is_ta_codeE intro: ta_only_prs_autoref[THEN fun_relD, THEN is_ta_codeI])

lift_definition only_prs_wits :: "('q,'f)ta_code \<Rightarrow> ('q, ('f, 'q) ctxt) RBT.rbt \<Rightarrow> ('q,'f)ta_code" is ta_only_prs_wits_code
by (auto elim!: is_ta_codeE is_rbt_mapE intro: ta_only_prs_wits_code.refine[THEN fun_relD2', THEN is_ta_codeI])

lift_definition det :: "('q,'f)ta_code \<Rightarrow> bool" is ta_det_impl .

lift_definition check_comcoh_wit :: "('q,'f)ta_code  \<Rightarrow> (('f,'vc)term \<times> ('f,'vc)term, unit) RBT.rbt \<Rightarrow> (('f,'vc)term \<times> ('f,'vc) term) option" is ta_check_comcoh_code .

lift_definition final :: "('q,'f)ta_code \<Rightarrow> ('q, unit) RBT.rbt" is ta_final_impl
proof -
  fix TC assume "is_ta_code (TC :: ('q,'f)ta_code_tuple)"
  from is_ta_codeE[OF this] obtain TA where "(TC, TA) \<in> dflt_ta_rel" by auto
  from ta_impl_autoref(1)[THEN fun_relD, OF this] have "is_rbt (ta_final_impl TC)" by (auto simp: rbt_map_rel_simps)
  then show "?thesis TC" by blast
qed

definition "check_comcoh TA R = (check_comcoh_wit TA R = None)"
definition "check_comcoh_wit_ls TA R \<equiv> check_comcoh_wit TA (rs.from_list R)"
definition "check_comcoh_ls TA R = (check_comcoh_wit_ls TA R = None)"

definition "trim_wits TA \<equiv> let res = res_wits TA; TA = only_res_wits TA res; 
                                prs = prs_wits TA; TA = only_prs_wits TA prs in (TA, res, prs)"
definition "trim TA \<equiv> fst (trim_wits TA :: _ \<times> (_,(_,unit)term)rbt \<times> _)"

definition "only_reach TA = only_res_wits TA (res_wits TA :: (_,(_,unit)term)rbt)"
definition "only_prod TA = only_prs_wits TA (prs_wits TA)"

definition empty_wit where "empty_wit TA \<equiv> rm.sel (res_wits TA) (\<lambda>(q,t::('f,unit)term). rs.memb q (final TA))"
definition empty where "empty TA \<equiv> empty_wit TA = (None::(_ \<times> (_,unit)term)option)"

private lemma ta_abs_TA_rel:
  assumes "(TC, TA) \<in> dflt_ta_rel"
    shows "ta_abs TC = TA"
proof -
  note simps =
    dflt_ta_rel_def ta_abs_def ta.make_def
    list_set_rel_def rbt_map_rel_simps rs_abs_def
  from assms show ?thesis by (simp add: simps split: prod.splits)
qed

private lemma rep_abs_TA_rel:
  "(Rep_ta_code TC, \<alpha> TC) \<in> dflt_ta_rel"
proof -
  from Rep_ta_code obtain TA where "(Rep_ta_code TC, TA) \<in> dflt_ta_rel" by (auto simp: is_ta_code_def)
  moreover from this have "TA = \<alpha> TC" by (simp add: \<alpha>_def ta_abs_TA_rel)
  ultimately show ?thesis by simp
qed

private lemma make_ls:
  "\<alpha> (make_ls F R E) = ta.make (set F) (set R) (set E)"
unfolding \<alpha>.rep_eq make_ls.rep_eq ta_make_ls_def[symmetric]
by (auto intro!: ta_abs_TA_rel ta_make_ls_code.refine[THEN fun_relD3'])

private lemma det:
  "det TA = ta_det (\<alpha> TA)"
proof -
  have "(ta_det_impl (Rep_ta_code TA), ta_det (\<alpha> TA)) \<in> bool_rel"
    by (intro ta_impl_autoref(6)[THEN fun_relD]) (auto intro: rep_abs_TA_rel)
  then show ?thesis unfolding det.rep_eq by simp
qed

private lemma res_wits_code:
  assumes "(I,A) \<in> dflt_ta_rel" shows
    "dom (rm_abs (res_wits_code I)) = ta_reachable A" (is "?A")
    "rm_abs (res_wits_code I) q = Some t \<Longrightarrow> is_ad_res_wit A q t" (is "?B \<Longrightarrow> ?C")
proof -
  from assms have finite: "ta_finite A" by blast
  note res_wits_code.refine[of I]
  also note res_wits_impl.refine[THEN fun_relD, THEN nres_relD, OF assms]
  also note res_wits_correct[OF finite]
  finally have "res_wits_inv A ({}, rm_abs (res_wits_code I))" by (auto simp: RETURN_RES_refine_iff rbt_map_rel_simps rm_abs_def)
  then show ?A "?B \<Longrightarrow> ?C" by (auto simp: res_wits_inv_def map_to_set_def)
qed

private lemma  res_wits:
  "dom (rm.\<alpha> (res_wits TA :: ('q, ('f, 'v) term) rbt)) = ta_reachable (\<alpha> TA)"
  "rm.\<alpha> (res_wits TA) q = Some t \<Longrightarrow> is_ad_res_wit (\<alpha> TA) q (t :: ('f, 'v) term)"
by (auto simp: icf_rec_unf lookup.rep_eq res_wits.rep_eq rm_abs_compare_order[symmetric]
       intro!: res_wits_code rep_abs_TA_rel)

private lemma only_res_wits:
  assumes "dom (rm.\<alpha> wits) = ta_reachable (\<alpha> TA)"
    shows "\<alpha> (only_res_wits TA wits) = ta_only_reach (\<alpha> TA)"
proof -
  note intro = ta_only_res_wits_code.refine[THEN fun_relD2', THEN ta_abs_TA_rel]
  note simps = \<alpha>.rep_eq only_res_wits.rep_eq icf_rec_unf rbt_map_rel_simps
               rm_abs_def[symmetric] rm_abs_compare_order lookup.rep_eq
  show ?thesis using ta_only_res_wits[OF assms, symmetric] rep_abs_TA_rel
  by (auto simp: simps intro!: intro)
qed
  
private lemma prs_wits_code:
  assumes "(I,A) \<in> dflt_ta_rel" shows
    "dom (rm_abs (prs_wits_code I)) = ta_productive A" (is "?A")
    "rm_abs (prs_wits_code I) q = Some C \<Longrightarrow> is_prs_wit A q C" (is "?B \<Longrightarrow> ?C")
proof -
  from assms have finite: "ta_finite A" by auto
  note prs_wits_code.refine[of I]
  also note prs_wits_impl.refine[THEN fun_relD, THEN nres_relD, OF assms]
  also note prs_wits_correct[OF finite]
  finally have "prs_wits_spec A (rm_abs (prs_wits_code I))" by (auto simp: RETURN_RES_refine_iff rbt_map_rel_simps rm_abs_def)
  then show ?A "?B \<Longrightarrow> ?C" by (auto simp: map_to_set_def)
qed

private lemma prs_wits:
  "dom (rm.\<alpha> (prs_wits TA)) = ta_productive (\<alpha> TA)" (is "?A")
  "rm.\<alpha> (prs_wits TA) q = Some C \<Longrightarrow> is_prs_wit (\<alpha> TA) q C" (is "?B \<Longrightarrow> ?C")
by (simp_all add: icf_rec_unf lookup.rep_eq prs_wits.rep_eq rm_abs_compare_order[symmetric])
   (intro prs_wits_code[of "Rep_ta_code TA"] rep_abs_TA_rel)+

private lemma only_prs_wits:
  assumes "dom (rm.\<alpha> wits) = ta_productive (\<alpha> TA)"
    shows "\<alpha> (only_prs_wits TA wits) = ta_only_prod (\<alpha> TA)"
proof -
  note intro = ta_only_prs_wits_code.refine[THEN fun_relD2', THEN ta_abs_TA_rel]
  note simps = \<alpha>.rep_eq only_prs_wits.rep_eq icf_rec_unf rbt_map_rel_simps
               rm_abs_def[symmetric] rm_abs_compare_order lookup.rep_eq
  show ?thesis using ta_only_prs_wits[OF assms, symmetric] rep_abs_TA_rel
  by (auto simp: simps intro!: intro)
qed

private lemma ta_check_comcoh_code:
  assumes TA: "(I,A) \<in> dflt_ta_rel"
     and R: "(R',R) \<in> \<langle>term_pair\<rangle>comp_rs_rel"
     and det: "ta_det A"
     and wf: "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l" shows
  "case (ta_check_comcoh_code I R') of
     None \<Rightarrow> rstep R `` ta_lang A \<subseteq> ta_lang A
   | Some (wl, wr) \<Rightarrow> (wl, wr) \<in> rstep R \<and> wl \<in> ta_lang A \<and> wr \<notin> ta_lang A"
proof -
  from assms have finiteA: "ta_finite A" by blast
  from R have finiteR: "finite R" by simp
  note ta_check_comcoh_code.refine[of I R']
  also note ta_check_comcoh_impl.refine[THEN fun_relD2', THEN nres_relD, OF TA R]
  also note ta_check_comcoh_correct[OF finiteA finiteR det]
  finally show ?thesis using wf by auto
qed

private lemma check_comcoh_wit:
  assumes det: "ta_det (\<alpha> TA)"
      and wf: "\<forall>(l, r) \<in> rs.\<alpha> R. vars_term r \<subseteq> vars_term l" shows
  "case (check_comcoh_wit TA R) of
     None \<Rightarrow> rstep (rs.\<alpha> R) `` ta_lang (\<alpha> TA) \<subseteq> ta_lang (\<alpha> TA)
   | Some (wl, wr) \<Rightarrow> (wl, wr) \<in> rstep (rs.\<alpha> R) \<and> wl \<in> ta_lang (\<alpha> TA) \<and> wr \<notin> ta_lang (\<alpha> TA)"
using assms unfolding icf_rec_unf rs_sbm.\<alpha>_def
by (simp_all add: lookup.rep_eq check_comcoh_wit.rep_eq rm_abs_compare_order[symmetric])
   (auto intro!: ta_check_comcoh_code rep_abs_TA_rel 
           simp: rbt_map_rel_simps rm_abs_def[symmetric] rm_abs_compare_order lookup_impl_of)

private lemma check_comcoh:
  assumes det: "ta_det (\<alpha> TA)"
     and wf: "\<forall>(l, r) \<in> rs.\<alpha> R. vars_term r \<subseteq> vars_term l" shows
  "check_comcoh TA R = (rstep (rs.\<alpha> R) `` ta_lang (\<alpha> TA) \<subseteq> ta_lang (\<alpha> TA))"
unfolding check_comcoh_def using check_comcoh_wit[of TA R, OF assms]
by (cases "check_comcoh_wit TA R") auto

private lemma check_comcoh_wit_ls:
  assumes det: "ta_det (\<alpha> TA)"
      and wf: "\<forall>(l, r) \<in> set R. vars_term r \<subseteq> vars_term l" shows
  "case (check_comcoh_wit_ls TA R) of
     None \<Rightarrow> rstep (set R) `` ta_lang (\<alpha> TA) \<subseteq> ta_lang (\<alpha> TA)
   | Some (wl, wr) \<Rightarrow> (wl, wr) \<in> rstep (set R) \<and> wl \<in> ta_lang (\<alpha> TA) \<and> wr \<notin> ta_lang (\<alpha> TA)"
unfolding check_comcoh_wit_ls_def using check_comcoh_wit[of TA "rs.from_list R"] assms 
by (auto simp: rs.correct, unfold rs.correct(35)) blast

private lemma check_comcoh_ls:
  assumes det: "ta_det (\<alpha> TA)"
     and wf: "\<forall>(l, r) \<in> set R. vars_term r \<subseteq> vars_term l" shows
  "check_comcoh_ls TA R = (rstep (set R) `` ta_lang (\<alpha> TA) \<subseteq> ta_lang (\<alpha> TA))"
unfolding check_comcoh_ls_def using check_comcoh_wit_ls[of TA R, OF assms]
by (cases "check_comcoh_wit_ls TA R") auto

private lemma trim_wits:
  "case trim_wits TA of (TA', rs :: ('q, ('f, unit) term) rbt, ps)
    \<Rightarrow> \<alpha> TA' = trim_ta (\<alpha> TA) \<and>
      (\<forall>q \<in> ta_states (\<alpha> TA'). is_ad_res_wit (\<alpha> TA') q (the (rm.\<alpha> rs q))) \<and>
      (\<forall>q \<in> ta_states (\<alpha> TA'). is_prs_wit (\<alpha> TA') q (the (rm.\<alpha> ps q)))"
proof -
  note rw = res_wits[where ?'v = unit]
  let ?rw = "res_wits TA :: ('q, ('f, unit) term) rbt"
  let ?pw = "prs_wits (only_res_wits TA ?rw)"
  let ?tar = "ta_only_reach (\<alpha> TA)"
  let ?tapr = "ta_only_prod ?tar"
  let ?states = "ta_states (?tapr)"
  have prod: "\<And>TA. ta_states (ta_only_prod TA) \<subseteq> ta_productive TA" by (auto simp: ta_states_def r_states_def ta_restrict_def)

  from rw[of TA] trim_ta_reachable[of "\<alpha> TA"] have "?states \<subseteq> dom (rm.\<alpha> ?rw)" by auto
  then have "\<forall>q \<in> ?states. is_ad_res_wit ?tar q (the (rm.\<alpha> ?rw q))" by (auto simp: ta_only_reach_res_wit rw(2))
  with prod[of ?tar] ta_res_only_prod[of _ ?tar] have
    rs: "\<forall>q \<in> ?states. is_ad_res_wit ?tapr q (the (rm.\<alpha> ?rw q))" by auto

  from prs_wits(2) have "\<forall>q \<in> dom (rm.\<alpha> ?pw). is_prs_wit (\<alpha> (only_res_wits TA ?rw)) q (the (rm.\<alpha> ?pw q))" by auto
  then have "\<forall>q \<in> dom (rm.\<alpha> ?pw). is_prs_wit ?tar q (the (rm.\<alpha> ?pw q))" by (simp add: only_res_wits[OF rw(1)])
  then have "\<forall>q \<in> ta_productive ?tar. is_prs_wit ?tar q (the (rm.\<alpha> ?pw q))"
    unfolding prs_wits(1)[of "only_res_wits TA ?rw", unfolded only_res_wits[OF rw(1)]] .
  with prod[of ?tar] have ps: "\<forall>q \<in> ?states. is_prs_wit ?tapr q (the (rm.\<alpha> ?pw q))" by (auto simp: ta_only_prod_prs_wit)
  
  note simps = trim_wits_def Let_def res_wits only_res_wits prs_wits only_prs_wits trim_ta_def rs ps
  show ?thesis by (simp add: simps)
qed

private lemma trim:
  "\<alpha> (trim TA) = trim_ta (\<alpha> TA)"
unfolding trim_def using trim_wits[of TA]
by (cases "trim_wits TA :: _ \<times> (_,(_,unit)term)rbt \<times> _") (simp)

private lemma only_reach:
  "\<alpha> (only_reach TA) = ta_only_reach (\<alpha> TA)"
unfolding only_reach_def using only_res_wits[OF res_wits(1)[where ?'v = unit]] by simp

private lemma only_prod:
  "\<alpha> (only_prod TA) = ta_only_prod (\<alpha> TA)"
unfolding only_prod_def using only_prs_wits[OF prs_wits(1)] by simp

(* TODO: port emptiness check 
private lemma empty_wit:
  "case empty_wit TA of
    None \<Rightarrow> ta_empty (\<alpha> TA)
  | Some (q,t) \<Rightarrow> q \<in> ta_final (\<alpha> TA) \<and> is_ad_res_wit (\<alpha> TA) q (t::('f,'v)term)"
proof -
  let ?empty = "empty_wit TA :: ('q \<times> ('f, 'v) term) option"
  show ?thesis proof (cases "?empty")
    case None
      {
        fix q and t :: "('f,'v)term"
        from None have "rm.\<alpha> (res_wits TA) q = Some t \<Longrightarrow> \<not> (q \<in> ta_final (\<alpha> TA))"
          by (auto simp: empty_wit_def rs.correct final dest!: rm.sel'_noneD[simplified, where u = q and v = t])
      }
      with res_wits(1) have "ta_final (\<alpha> TA) \<inter> ta_reachable (\<alpha> TA) = {}" by (auto simp: dom_def)
      with None show ?thesis by (auto simp: ta_empty_def) next
    case (Some qt)
      obtain q and t :: "('f,'v)term" where [simp]: "qt = (q,t)" by (cases qt)
      from Some have "rm.\<alpha> (res_wits TA) q = Some t" "q \<in> ta_final (\<alpha> TA)"
        by (auto simp: empty_wit_def rs.correct final dest!: rm.sel'_SomeD[simplified])
      with Some res_wits show ?thesis by simp
  qed
qed

private lemma empty:
  "empty TA = ta_empty (\<alpha> TA)"
unfolding empty_def using empty_wit[of TA, where ?'v = unit]
by (cases "empty_wit TA ::(_ \<times> (_,unit)term)option")
   (auto simp: ta_empty[where ?'c = unit] ta_lang_def2)
*)

lemmas correct = make_ls det final (*empty*) only_reach only_prod trim check_comcoh check_comcoh_ls
(*lemmas correct_empty_wit = empty_wit*)
lemmas correct_res_wits = res_wits only_res_wits
lemmas correct_prs_wits = prs_wits only_prs_wits
lemmas correct_trim_wits = trim_wits
lemmas correct_comcoh_wit = check_comcoh_wit check_comcoh_wit_ls

end
end

lemmas [code] =
    ta_code.res_wits.rep_eq
    ta_code.prs_wits.rep_eq
    ta_code.det.rep_eq
    ta_code.final.rep_eq
    ta_code.check_comcoh_wit.rep_eq  
    
    ta_code.check_comcoh_def
    ta_code.check_comcoh_ls_def
    ta_code.check_comcoh_wit_ls_def
    ta_code.trim_def
    ta_code.trim_wits_def
    ta_code.empty_def
    ta_code.empty_wit_def
    ta_code.only_reach_def
    ta_code.only_prod_def

lemmas [code abstract] =
  ta_code.only_res_wits.rep_eq
  ta_code.only_prs_wits.rep_eq
  ta_code.make_ls.rep_eq

end
